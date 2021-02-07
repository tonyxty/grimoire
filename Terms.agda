{-# OPTIONS --safe --without-K #-}
module Terms where

open import Data.Maybe
open import Data.Nat
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Types

infixr 2 _↠_
data Type : Set where
  `ℕ : Type
  _↠_ : Type → Type → Type

Type≟ : ∀ (A B : Type) → Dec (A ≡ B)
Type≟ `ℕ `ℕ = yes refl
Type≟ `ℕ (B ↠ B₁) = no (λ ())
Type≟ (A₁ ↠ A₂) `ℕ = no (λ ())
Type≟ (A₁ ↠ A₂) (B₁ ↠ B₂) with Type≟ A₁ B₁ | Type≟ A₂ B₂
...                          | yes refl    | yes refl = yes refl
...                          | _           | no ≢₂ = no λ{refl → ≢₂ refl}
...                          | no ≢₁       | _ = no λ{refl → ≢₁ refl}

unify : ∀ (A B : Type) → Maybe (A ≡ B)
unify A B = decToMaybe (Type≟ A B)

-- Contexts

infixl 1 _,_
data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

infix 0 _∋_
data _∋_ : Context → Type → Set where
  head : ∀ {Γ A} → Γ , A ∋ A
  tail : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ)

at : (Γ : Context) → (i : ℕ) → (i<len : i < length Γ) → Type
at (_ , A) zero i<len = A
at (Γ , x) (suc i) (s≤s i<len) = at Γ i i<len

lookup : (Γ : Context) → (i : ℕ) → (i<len : i < length Γ) → Γ ∋ (at Γ i i<len)
lookup (_ , _) zero _ = head
lookup (Γ , _) (suc i) (s≤s i<len) = tail (lookup Γ i i<len)

-- Terms (intrinsically typed)

infix 0 _⊢_
infix 5 `_
infix 2 ƛ_⇒_
infixl 3 _∙_
infix 4 S_
infix 2 μ_
data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  ƛ_⇒_ : ∀ {Γ B} (A : Type) → Γ , A ⊢ B → Γ ⊢ A ↠ B
  _∙_ : ∀ {Γ A B} → Γ ⊢ A ↠ B → Γ ⊢ A → Γ ⊢ B
  Z : ∀ {Γ} → Γ ⊢ `ℕ
  S_ : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case_[Z⇒_|S⇒_] : ∀ {Γ A} → Γ ⊢ `ℕ → Γ ⊢ A → Γ , `ℕ ⊢ A → Γ ⊢ A
  μ_ : ∀ {Γ A} → Γ , A ⊢ A → Γ ⊢ A
  -- Note that μ without termination check breaks soundness

-- Helpers

# : ∀ {Γ} (i : ℕ) {i<len : True (i <? length Γ)} → Γ ⊢ at Γ i (toWitness i<len)
# {Γ} i {i<len} = ` lookup Γ i (toWitness i<len)

⌜_⌝ : ∀ {Γ} → ℕ → Γ ⊢ `ℕ
⌜ zero ⌝ = Z
⌜ suc n ⌝ = S ⌜ n ⌝

-- Substitution

Rename : Context → Context → Set
Rename Γ Δ = ∀ {A : Type} → Δ ∋ A → Γ ∋ A

ext : ∀ {Γ Δ A} → Rename Γ Δ → Rename (Γ , A) (Δ , A)
ext ρ head = head
ext ρ (tail x) = tail (ρ x)

-- note how this is contravariant
rename : ∀ {Γ Δ A} → Rename Γ Δ → Δ ⊢ A → Γ ⊢ A
rename ρ (` x) = ` ρ x
rename ρ (ƛ A ⇒ M) = ƛ A ⇒ rename (ext ρ) M
rename ρ (M₁ ∙ M₂) = rename ρ M₁ ∙ rename ρ M₂
rename ρ Z = Z
rename ρ (S M) = S rename ρ M
rename ρ case M [Z⇒ N₁ |S⇒ N₂ ] = case rename ρ M [Z⇒ rename ρ N₁ |S⇒ rename (ext ρ) N₂ ]
rename ρ (μ M) = μ rename (ext ρ) M

Subst : Context → Context → Set
Subst Γ Δ = ∀ (A : Type) → Δ ∋ A → Γ ⊢ A

infixl 10 _⋆_
_⋆_ : ∀ {Γ Δ} (σ : Subst Γ Δ) (A : Type) → Subst (Γ , A) (Δ , A)
(σ ⋆ _) _ head = ` head
(σ ⋆ _) _ (tail x) = rename tail (σ _ x)

-- implicit argument version
infix 9 _♯
_♯ : ∀ {Γ Δ A} → Subst Γ Δ → Subst (Γ , A) (Δ , A)
_♯ {A = A} σ = σ ⋆ A

extTerm : ∀ {Γ A} → Γ ⊢ A → Subst Γ (Γ , A)
extTerm M _ head = M
extTerm M _ (tail ∋A) = ` ∋A

subst : ∀ {Γ Δ A} → Subst Γ Δ → Δ ⊢ A → Γ ⊢ A
subst σ (` x) = σ _ x
subst σ (ƛ A ⇒ M) = ƛ A ⇒ (subst (σ ♯) M)
subst σ (M₁ ∙ M₂) = subst σ M₁ ∙ subst σ M₂
subst σ Z = Z
subst σ (S M) = S subst σ M
subst σ case M [Z⇒ N₁ |S⇒ N₂ ] = case subst σ M [Z⇒ subst σ N₁ |S⇒ subst (σ ♯) N₂ ]
subst σ (μ M) = μ subst (σ ♯) M

_[_] : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
_[_] M N = subst (extTerm N) M

-- Examples

`one : ∀ {Γ} → Γ ⊢ `ℕ
`one = ⌜ 1 ⌝

`two : ∀ {Γ} → Γ ⊢ `ℕ
`two = ⌜ 2 ⌝

`suc : ∀ {Γ} → Γ ⊢ `ℕ ↠ `ℕ
`suc = ƛ `ℕ ⇒ S # 0

`plus : ∀ {Γ} → Γ ⊢ `ℕ ↠ `ℕ ↠ `ℕ
`plus = μ (ƛ `ℕ ⇒ ƛ `ℕ ⇒
           case # 1
           [Z⇒ # 0
           |S⇒ S (# 3 ∙ # 0 ∙ # 1) ])

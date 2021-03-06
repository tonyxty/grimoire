{-# OPTIONS --safe --without-K #-}
module Terms where

open import Data.Maybe
open import Data.Nat
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Types

infixr 2 _↠_
infixl 3 _⊗_
data Type : Set where
  `ℕ : Type
  _↠_ : Type → Type → Type
  _⊗_ : Type → Type → Type

Type≟ : ∀ (A B : Type) → Dec (A ≡ B)
Type≟ `ℕ `ℕ = yes refl
Type≟ `ℕ (_ ↠ _) = no (λ ())
Type≟ `ℕ (_ ⊗ _) = no (λ ())
Type≟ (_ ↠ _) `ℕ = no (λ ())
Type≟ (A₁ ↠ A₂) (B₁ ↠ B₂) with Type≟ A₁ B₁ | Type≟ A₂ B₂
...                          | yes e       | yes refl rewrite e = yes refl
...                          | yes _       | no ≢₂ = no λ{refl → ≢₂ refl}
...                          | no ≢₁       | _ = no λ{refl → ≢₁ refl}
Type≟ (_ ↠ _) (_ ⊗ _) = no (λ ())
Type≟ (_ ⊗ _) `ℕ = no (λ ())
Type≟ (_ ⊗ _) (_ ↠ _) = no (λ ())
Type≟ (A₁ ⊗ A₂) (B₁ ⊗ B₂) with Type≟ A₁ B₁ | Type≟ A₂ B₂
...                          | yes e       | yes refl rewrite e = yes refl
...                          | yes _       | no ≢₂ = no λ{refl → ≢₂ refl}
...                          | no ≢₁       | _ = no λ{refl → ≢₁ refl}

unify : ∀ (A B : Type) → Maybe (A ≡ B)
unify A B = decToMaybe (Type≟ A B)

-- Contexts

infixl 1 _,_
data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

-- intrinsically scoped & typed de Brujin index.  this type is called "_[_]=_" in Data.Vec
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
  -- variable reference
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  -- ↠
  ƛ_⇒_ : ∀ {Γ B} (A : Type) → Γ , A ⊢ B → Γ ⊢ A ↠ B
  _∙_ : ∀ {Γ A B} → Γ ⊢ A ↠ B → Γ ⊢ A → Γ ⊢ B
  -- `ℕ
  Z : ∀ {Γ} → Γ ⊢ `ℕ
  S_ : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case_[Z⇒_|S⇒_] : ∀ {Γ A} → Γ ⊢ `ℕ → Γ ⊢ A → Γ , `ℕ ⊢ A → Γ ⊢ A
  -- ⊗
  ⟪_,_⟫ : ∀ {Γ A₁ A₂} → Γ ⊢ A₁ → Γ ⊢ A₂ → Γ ⊢ A₁ ⊗ A₂
  case_[⟪,⟫⇒_] : ∀ {Γ A₁ A₂ B} → Γ ⊢ A₁ ⊗ A₂ → Γ , A₁ , A₂ ⊢ B → Γ ⊢ B
  -- fixpoint
  μ_ : ∀ {Γ A} → Γ , A ⊢ A → Γ ⊢ A
  -- Note that μ without termination check breaks consitency (and confuses Agda C-c C-a)

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
rename ρ ⟪ M₁ , M₂ ⟫ = ⟪ rename ρ M₁ , rename ρ M₂ ⟫
rename ρ case M [⟪,⟫⇒ N ] = case rename ρ M [⟪,⟫⇒ rename (ext (ext ρ)) N ]
rename ρ (μ M) = μ rename (ext ρ) M

_♯ : ∀ {Γ A B} → Γ ⊢ A → Γ , B ⊢ A
M ♯ = rename tail M

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Δ ∋ A → Γ ⊢ A

infixl 10 _⋆_
_⋆_ : ∀ {Γ Δ} (σ : Subst Γ Δ) (A : Type) → Subst (Γ , A) (Δ , A)
(σ ⋆ _) head = ` head
(σ ⋆ _) (tail x) = σ x ♯

-- implicit argument version
infix 9 _⋆
_⋆ : ∀ {Γ Δ A} → Subst Γ Δ → Subst (Γ , A) (Δ , A)
σ ⋆ = σ ⋆ _

extByTerm : ∀ {Γ A} → Γ ⊢ A → Subst Γ (Γ , A)
extByTerm M head = M
extByTerm M (tail x) = ` x

subst : ∀ {Γ Δ A} → Subst Γ Δ → Δ ⊢ A → Γ ⊢ A
subst σ (` x) = σ x
subst σ (ƛ A ⇒ M) = ƛ A ⇒ (subst (σ ⋆) M)
subst σ (M₁ ∙ M₂) = subst σ M₁ ∙ subst σ M₂
subst σ Z = Z
subst σ (S M) = S subst σ M
subst σ case M [Z⇒ N₁ |S⇒ N₂ ] = case subst σ M [Z⇒ subst σ N₁ |S⇒ subst (σ ⋆) N₂ ]
subst σ ⟪ M₁ , M₂ ⟫ = ⟪ subst σ M₁ , subst σ M₂ ⟫
subst σ case M [⟪,⟫⇒ N ] = case subst σ M [⟪,⟫⇒ subst (σ ⋆ ⋆) N ]
subst σ (μ M) = μ subst (σ ⋆) M

_[_] : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
M [ N ] = subst (extByTerm N) M

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

`proj₁ : ∀ {Γ A B} → Γ ⊢ A ⊗ B ↠ A
`proj₁ = ƛ _ ⇒ case # 0 [⟪,⟫⇒ # 1 ]

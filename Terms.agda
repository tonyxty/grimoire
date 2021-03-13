{-# OPTIONS --safe --without-K #-}
module Terms where

open import Data.Maybe
open import Data.Nat
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Types

infixr 5 _↠_
infixl 6 _⊗_
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

infixl 4 _,_
data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

private
  variable
    Γ Δ : Context
    A A' B A₁ A₂ : Type

-- Terms (intrinsically typed)

-- intrinsically scoped & typed de Brujin index.  this type is called "_[_]=_" in Data.Vec
infix 1 _∋_
data _∋_ : Context → Type → Set where
  zero : Γ , A ∋ A
  suc : Γ ∋ A → Γ , A' ∋ A

length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ)

at : ∀ (Γ : Context) (i : ℕ) (< : i < length Γ) → Type
at (_ , A) zero _ = A
at (Γ , _) (suc i) (s≤s <) = at Γ i <

lookup : (Γ : Context) → (i : ℕ) → (i<len : i < length Γ) → Γ ∋ (at Γ i i<len)
lookup (_ , _) zero _ = zero
lookup (Γ , _) (suc i) (s≤s i<len) = suc (lookup Γ i i<len)

infix 1 _⊢_
infix 9 `_
infix 6 ƛ_⇒_
infixl 7 _∙_
infix 8 S_
infix 6 μ_
data _⊢_ : Context → Type → Set where
  -- variable reference
  `_ : Γ ∋ A → Γ ⊢ A
  -- A ↠ B
  ƛ_⇒_ : ∀ (A : Type) → Γ , A ⊢ B → Γ ⊢ A ↠ B
  _∙_ : Γ ⊢ A ↠ B → Γ ⊢ A → Γ ⊢ B
  -- `ℕ
  Z : Γ ⊢ `ℕ
  S_ : Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case_[Z⇒_|S⇒_] : Γ ⊢ `ℕ → Γ ⊢ A → Γ , `ℕ ⊢ A → Γ ⊢ A
  -- A₁ ⊗ A₂
  ⟪_,_⟫ : Γ ⊢ A₁ → Γ ⊢ A₂ → Γ ⊢ A₁ ⊗ A₂
  case_[⟪,⟫⇒_] : Γ ⊢ A₁ ⊗ A₂ → Γ , A₁ , A₂ ⊢ B → Γ ⊢ B
  -- μ
  μ_ : Γ , A ⊢ A → Γ ⊢ A
  -- note that μ without termination check breaks consitency (and confuses Agda C-c C-a)

-- Helpers

infix 9 #_
#_ : ∀ (i : ℕ) {i<len : True (i <? length Γ)} → Γ ⊢ at Γ i (toWitness i<len)
#_ {Γ} i {i<len} = ` lookup Γ i (toWitness i<len)

⌜_⌝ : ℕ → Γ ⊢ `ℕ
⌜ zero ⌝ = Z
⌜ suc n ⌝ = S ⌜ n ⌝

-- Substitution

module Rename where
  -- Rename.  since subtitution for a ƛ term requires extending the scope, and they can nest arbitararily deep, we need
  -- a way to manage these data.  they should mostly be regarded as implementation details, hence the separate module.
  data Rename (Γ : Context) : Context → Set where
    ∅ : Rename Γ ∅
    _,_ : Rename Γ Δ → Γ ∋ A → Rename Γ (Δ , A)

  weaken : Rename Γ Δ → Rename (Γ , A) Δ
  weaken ∅ = ∅
  weaken (ρ , x) = weaken ρ , suc x

  ext : Rename Γ Δ → Rename (Γ , A) (Δ , A)
  ext ρ = weaken ρ , zero

  idRename : Rename Γ Γ
  idRename {Γ = ∅} = ∅
  idRename {Γ = _ , _} = ext idRename

  drop : Rename (Γ , A) Γ
  drop = weaken idRename

  -- note how this is contravariant
  renameVar : Rename Γ Δ → Δ ∋ A → Γ ∋ A
  renameVar (_ , x) zero = x
  renameVar (ρ , _) (suc x) = renameVar ρ x

  rename : Rename Γ Δ → Δ ⊢ A → Γ ⊢ A
  rename ρ (` x) = ` renameVar ρ x
  rename ρ (ƛ A ⇒ M) = ƛ A ⇒ rename (ext ρ) M
  rename ρ (M₁ ∙ M₂) = rename ρ M₁ ∙ rename ρ M₂
  rename ρ Z = Z
  rename ρ (S M) = S rename ρ M
  rename ρ case M [Z⇒ N₁ |S⇒ N₂ ] = case rename ρ M [Z⇒ rename ρ N₁ |S⇒ rename (ext ρ) N₂ ]
  rename ρ ⟪ M₁ , M₂ ⟫ = ⟪ rename ρ M₁ , rename ρ M₂ ⟫
  rename ρ case M [⟪,⟫⇒ N ] = case rename ρ M [⟪,⟫⇒ rename (ext (ext ρ)) N ]
  rename ρ (μ M) = μ rename (ext ρ) M

data Subst (Γ : Context) : Context → Set where
  ∅ : Subst Γ ∅
  _,_ : Subst Γ Δ → Γ ⊢ A → Subst Γ (Δ , A)

_♯_ : Γ ⊢ A → ∀ (A' : Type) → Γ , A' ⊢ A
M ♯ _ = rename drop M where open Rename

_♯ : Γ ⊢ A → Γ , A' ⊢ A
M ♯ = M ♯ _

weaken : Subst Γ Δ → Subst (Γ , A) Δ
weaken ∅ = ∅
weaken (σ , M) = weaken σ , M ♯

infixl 11 _⋆_
_⋆_ : ∀ (σ : Subst Γ Δ) (A : Type) → Subst (Γ , A) (Δ , A)
σ ⋆ A = weaken σ , ` zero

-- implicit argument version
infix 10 _⋆
_⋆ : Subst Γ Δ → Subst (Γ , A) (Δ , A)
σ ⋆ = σ ⋆ _

idSubst : Subst Γ Γ
idSubst {Γ = ∅} = ∅
idSubst {Γ = Γ , A} = idSubst ⋆

intro : Γ ⊢ A → Subst Γ (Γ , A)
intro M = idSubst , M

substVar : Subst Γ Δ → Δ ∋ A → Γ ⊢ A
substVar (_ , M) zero = M
substVar (σ , _) (suc x) = substVar σ x

subst : Subst Γ Δ → Δ ⊢ A → Γ ⊢ A
subst σ (` x) = substVar σ x
subst σ (ƛ A ⇒ M) = ƛ A ⇒ (subst (σ ⋆) M)
subst σ (M₁ ∙ M₂) = subst σ M₁ ∙ subst σ M₂
subst σ Z = Z
subst σ (S M) = S subst σ M
subst σ case M [Z⇒ N₁ |S⇒ N₂ ] = case subst σ M [Z⇒ subst σ N₁ |S⇒ subst (σ ⋆) N₂ ]
subst σ ⟪ M₁ , M₂ ⟫ = ⟪ subst σ M₁ , subst σ M₂ ⟫
subst σ case M [⟪,⟫⇒ N ] = case subst σ M [⟪,⟫⇒ subst (σ ⋆ ⋆) N ]
subst σ (μ M) = μ subst (σ ⋆) M

_[_] : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
M [ N ] = subst (intro N) M

-- Examples

`one : ∀ {Γ} → Γ ⊢ `ℕ
`one = ⌜ 1 ⌝

`two : ∀ {Γ} → Γ ⊢ `ℕ
`two = ⌜ 2 ⌝

`suc : ∀ {Γ} → Γ ⊢ `ℕ ↠ `ℕ
`suc = ƛ `ℕ ⇒ S # 0

`plus : ∀ {Γ} → Γ ⊢ `ℕ ↠ `ℕ ↠ `ℕ
`plus = μ ƛ `ℕ ⇒ ƛ `ℕ ⇒
            case # 1
            [Z⇒ # 0
            |S⇒ S (# 3 ∙ # 0 ∙ # 1) ]

`proj₁ : ∀ {Γ A B} → Γ ⊢ A ⊗ B ↠ A
`proj₁ = ƛ _ ⇒ case # 0 [⟪,⟫⇒ # 1 ]

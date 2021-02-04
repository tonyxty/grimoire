{-# OPTIONS --safe --without-K #-}
module Typecheck where

open import Terms
open import Data.Nat
open import Data.Nat.Properties
open import Data.Maybe
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

-- Untyped variable references and terms

Var = ℕ

data Term : Set where
  `_ : Var → Term
  ƛ_⇒_ : Type → Term → Term
  _∙_ : Term → Term → Term
  Z : Term
  S_ : Term → Term
  case_[Z⇒_|S⇒_] : Term → Term → Term → Term
  ⟪_,_⟫ : Term → Term → Term
  case_[⟪,⟫⇒_] : Term → Term → Term
  μ_⇒_ : Type → Term → Term

eraseVar : ∀ {Γ A} → Γ ∋ A → Var
eraseVar head = zero
eraseVar (tail ∋A) = suc (eraseVar ∋A)

data CheckVarResult (Γ : Context) (x : Var) : Set where
  good : ∀ {A} (x' : Γ ∋ A) → eraseVar x' ≡ x → CheckVarResult Γ x
  ungood : (∀ {A} (x' : Γ ∋ A) → eraseVar x' ≢ x) → CheckVarResult Γ x

checkVar : ∀ (Γ : Context) (x : Var) → CheckVarResult Γ x
checkVar ∅ x = ungood λ ()
checkVar (Γ , A) zero = good head refl
checkVar (Γ , A) (suc x) with checkVar Γ x
...                    | good x' refl = good (tail x') refl
...                    | ungood ≢ = ungood (λ{(tail x') e → ≢ x' (suc-injective e)})

-- Correct-by-type typechecking

erase : ∀ {Γ A} → Γ ⊢ A → Term
erase (` x) = ` (eraseVar x)
erase (ƛ A ⇒ M) = ƛ A ⇒ erase M
erase (M₁ ∙ M₂) = erase M₁ ∙ erase M₂
erase Z = Z
erase (S M) = S erase M
erase case M [Z⇒ M₁ |S⇒ M₂ ] = case erase M [Z⇒ erase M₁ |S⇒ erase M₂ ]
erase ⟪ M₁ , M₂ ⟫ = ⟪ erase M₁ , erase M₂ ⟫
erase case M [⟪,⟫⇒ N ] = case erase M [⟪,⟫⇒ erase N ]
erase (μ_ {A = A} M) = μ A ⇒ erase M

data CheckGoodResult (Γ : Context) (M : Term) : Set where
  ⟨_,_,_⟩ : ∀ (A : Type) (M' : Γ ⊢ A) → erase M' ≡ M → CheckGoodResult Γ M

check' : ∀ (Γ : Context) (M : Term) → Maybe (CheckGoodResult Γ M)
check' Γ (` x) with checkVar Γ x
...               | good {A} x' refl = just ⟨ A , ` x' , refl ⟩
...               | ungood _ = nothing
check' Γ (ƛ A ⇒ M) = do
  ⟨ B , M , refl ⟩ ← check' (Γ , A) M
  just ⟨ A ↠ B , ƛ A ⇒ M , refl ⟩
check' Γ (M₁ ∙ M₂) = do
  ⟨ A ↠ B , M₁ , refl ⟩ ← check' Γ M₁
                        where _ → nothing
  ⟨ A' , M₂ , refl ⟩ ← check' Γ M₂
  refl ← unify A A'
  just ⟨ B , M₁ ∙ M₂ , refl ⟩
check' Γ Z = just ⟨ `ℕ , Z , refl ⟩
check' Γ (S M) = do
  ⟨ A , M , refl ⟩ ← check' Γ M
  refl ← unify A `ℕ
  just ⟨ `ℕ , S M , refl ⟩
check' Γ case M [Z⇒ N₁ |S⇒ N₂ ] = do
  ⟨ A , M , refl ⟩ ← check' Γ M
  refl ← unify A `ℕ
  ⟨ B , N₁ , refl ⟩ ← check' Γ N₁
  ⟨ B' , N₂ , refl ⟩ ← check' (Γ , `ℕ) N₂
  refl ← unify B B'
  just ⟨ B , case M [Z⇒ N₁ |S⇒ N₂ ] , refl ⟩
check' Γ ⟪ M₁ , M₂ ⟫ = do
  ⟨ A₁ , M₁ , refl ⟩ ← check' Γ M₁
  ⟨ A₂ , M₂ , refl ⟩ ← check' Γ M₂
  just ⟨ A₁ ⊗ A₂ , ⟪ M₁ , M₂ ⟫ , refl ⟩
check' Γ case M [⟪,⟫⇒ N ] = do
  ⟨ A₁ ⊗ A₂ , M , refl ⟩ ← check' Γ M
                                   where _ → nothing
  ⟨ B , N , refl ⟩ ← check' (Γ , A₁ , A₂) N
  just ⟨ B , case M [⟪,⟫⇒ N ] , refl ⟩

check' Γ (μ A ⇒ M) = do
  ⟨ A' , M , refl ⟩ ← check' (Γ , A) M
  refl ← unify A A'
  just ⟨ A , μ M , refl ⟩

-- Examples

private
  `ungood : Term
  `ungood = (S S Z) ∙ Z

  _ : ∀ {Γ} → check' Γ `ungood ≡ nothing
  _ = refl

  `plusungood : Term
  `plusungood = ƛ `ℕ ⇒ ƛ `ℕ ⇒ ` 0 ∙ ` 1

  _ : ∀ {Γ} → check' Γ `plusungood ≡ nothing
  _ = refl

  `doubleplusungood : Term
  `doubleplusungood = μ `ℕ ⇒ (` 0 ∙ ` 0)

  _ : ∀ {Γ} → check' Γ `doubleplusungood ≡ nothing
  _ = refl

-- Completeness

completenessVar : ∀ {Γ A} (x : Γ ∋ A) → checkVar Γ (eraseVar x) ≡ good x refl
completenessVar head = refl
completenessVar (tail x) rewrite completenessVar x = refl

-- Note that the following essentially asserts that Type is an h-Set.
unifySelf : ∀ (A : Type) → Type≟ A A ≡ yes refl
unifySelf `ℕ = refl
unifySelf (A ↠ B) rewrite unifySelf A | unifySelf B = refl
unifySelf (A ⊗ B) rewrite unifySelf A | unifySelf B = refl

completeness : ∀ {Γ A} (M : Γ ⊢ A) → check' Γ (erase M) ≡ just ⟨ A , M , refl ⟩
completeness (` x) rewrite completenessVar x = refl
completeness (ƛ A ⇒ M) rewrite completeness M = refl
completeness (_∙_ {A = A} M₁ M₂)
  rewrite completeness M₁ | completeness M₂ | unifySelf A = refl
completeness Z = refl
completeness (S M) rewrite completeness M = refl
completeness {A = A} case M [Z⇒ M₁ |S⇒ M₂ ]
  rewrite completeness M | completeness M₁ | completeness M₂ | unifySelf A = refl
completeness ⟪ M₁ , M₂ ⟫ rewrite completeness M₁ | completeness M₂ = refl
completeness case M [⟪,⟫⇒ N ] rewrite completeness M | completeness N = refl
completeness {A = A} (μ M) rewrite completeness M | unifySelf A = refl

data CheckResult (Γ : Context) (M : Term) : Set where
  good : ∀ {A} (M' : Γ ⊢ A) → erase M' ≡ M → CheckResult Γ M
  ungood : (∀ {A} (M' : Γ ⊢ A) → erase M' ≢ M) → CheckResult Γ M

check : ∀ (Γ : Context) (M : Term) → CheckResult Γ M
check Γ M with check' Γ M | inspect (check' Γ) M
...        | just ⟨ A , M' , refl ⟩ | _ = good M' refl
...        | nothing | [ ≡ ] = ungood λ{M' refl → helper ≡}
  where
  helper : ∀ {Γ A} {M : Γ ⊢ A} → check' Γ (erase M) ≢ nothing
  helper {M = M} rewrite completeness M = λ ()

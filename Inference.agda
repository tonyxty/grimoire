{-# OPTIONS --safe --without-K #-}
open import Stlc
open import Data.Nat
open import Data.Nat.Properties
open import Data.Maybe
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

-- Untyped variable references and terms

data Term : Set where
  `_ : ℕ → Term
  ƛ_⇒_ : Type → Term → Term
  _∙_ : Term → Term → Term
  `Z : Term
  `S : Term → Term
  case_[Z⇒_|S⇒_] : Term → Term → Term → Term
  μ[_]⇒_ : Type → Term → Term

eraseVar : ∀ {Γ A} → Γ ∋ A → ℕ
eraseVar head = zero
eraseVar (tail ∋A) = suc (eraseVar ∋A)

data InferenceVarResult (Γ : Context) (x : ℕ) : Set where
  good : ∀ {A} (x' : Γ ∋ A) → eraseVar x' ≡ x → InferenceVarResult Γ x
  ungood : (∀ {A} (x' : Γ ∋ A) → eraseVar x' ≢ x) → InferenceVarResult Γ x

inferVar : ∀ (Γ : Context) (x : ℕ) → InferenceVarResult Γ x
inferVar ∅ x = ungood λ ()
inferVar (Γ , A) zero = good head refl
inferVar (Γ , A) (suc x) with inferVar Γ x
...                    | good x' refl = good (tail x') refl
...                    | ungood ≢ = ungood (λ{(tail x') e → ≢ x' (suc-injective e)})

-- Correct-by-type inference

erase : ∀ {Γ A} → Γ ⊢ A → Term
erase (` x) = ` (eraseVar x)
erase (ƛ A ⇒ M) = ƛ A ⇒ erase M
erase (M₁ ∙ M₂) = erase M₁ ∙ erase M₂
erase `Z = `Z
erase (`S M) = `S (erase M)
erase case M [Z⇒ M₁ |S⇒ M₂ ] = case erase M [Z⇒ erase M₁ |S⇒ erase M₂ ]
erase (μ_ {A = A} M) = μ[ A ]⇒ erase M

unify : ∀ (A B : Type) → Maybe (A ≡ B)
unify A B = decToMaybe (Type≟ A B)

data InferenceGoodResult (Γ : Context) (M : Term) : Set where
  ⟨_,_,_⟩ : ∀ (A : Type) (M' : Γ ⊢ A) → erase M' ≡ M → InferenceGoodResult Γ M

infer' : ∀ (Γ : Context) (M : Term) → Maybe (InferenceGoodResult Γ M)
infer' Γ (` x) with inferVar Γ x
...               | good {A} x' refl = just ⟨ A , ` x' , refl ⟩
...               | ungood ≢ = nothing
infer' Γ (ƛ A ⇒ M) = do
  ⟨ B , M , refl ⟩ ← infer' (Γ , A) M
  just ⟨ A ⇒ B , ƛ A ⇒ M , refl ⟩
infer' Γ (M₁ ∙ M₂) = do
  ⟨ A ⇒ B , M₁ , refl ⟩ ← infer' Γ M₁
                        where _ → nothing
  ⟨ A' , M₂ , refl ⟩ ← infer' Γ M₂
  refl ← unify A A'
  just ⟨ B , M₁ ∙ M₂ , refl ⟩
infer' Γ `Z = just ⟨ `ℕ , `Z , refl ⟩
infer' Γ (`S M) = do
  ⟨ A , M , refl ⟩ ← infer' Γ M
  refl ← unify A `ℕ
  just ⟨ `ℕ , `S M , refl ⟩
infer' Γ case M [Z⇒ M₁ |S⇒ M₂ ] = do
  ⟨ A , M , refl ⟩ ← infer' Γ M
  refl ← unify A `ℕ
  ⟨ B , M₁ , refl ⟩ ← infer' Γ M₁
  ⟨ B' , M₂ , refl ⟩ ← infer' (Γ , `ℕ) M₂
  refl ← unify B B'
  just ⟨ B , case M [Z⇒ M₁ |S⇒ M₂ ] , refl ⟩
infer' Γ (μ[ A ]⇒ M) = do
  ⟨ A' , M , refl ⟩ ← infer' (Γ , A) M
  refl ← unify A A'
  just ⟨ A , μ M , refl ⟩

-- Examples

`ungood : Term
`ungood = (`S (`S `Z)) ∙ `Z

_ : infer' ∅ `ungood ≡ nothing
_ = refl

`plusungood : Term
`plusungood = ƛ `ℕ ⇒ ƛ `ℕ ⇒ ` 0 ∙ ` 1

_ : infer' ∅ `plusungood ≡ nothing
_ = refl

`doubleplusungood : Term
`doubleplusungood = μ[ `ℕ ]⇒ (` 0 ∙ ` 0)

_ : infer' ∅ `doubleplusungood ≡ nothing
_ = refl

-- Completeness

completenessVar : ∀ {Γ A} (x : Γ ∋ A) → inferVar Γ (eraseVar x) ≡ good x refl
completenessVar head = refl
completenessVar (tail x) rewrite completenessVar x = refl

-- Note that the following essentially asserts that Type is an h-Set.
unifySelf : ∀ (A : Type) → Type≟ A A ≡ yes refl
unifySelf `ℕ = refl
unifySelf (A ⇒ B) rewrite unifySelf A | unifySelf B = refl

completeness : ∀ {Γ A} (M : Γ ⊢ A) → infer' Γ (erase M) ≡ just ⟨ A , M , refl ⟩
completeness (` x) rewrite completenessVar x = refl
completeness (ƛ A ⇒ M) rewrite completeness M = refl
completeness (_∙_ {A = A} M₁ M₂)
  rewrite completeness M₁ | completeness M₂ | unifySelf A = refl
completeness `Z = refl
completeness (`S M) rewrite completeness M = refl
completeness {A = A} case M [Z⇒ M₁ |S⇒ M₂ ]
  rewrite completeness M | completeness M₁ | completeness M₂ | unifySelf A = refl
completeness {A = A} (μ M) rewrite completeness M | unifySelf A = refl

data InferenceResult (Γ : Context) (M : Term) : Set where
  good : ∀ {A} (M' : Γ ⊢ A) → erase M' ≡ M → InferenceResult Γ M
  ungood : (∀ {A} (M' : Γ ⊢ A) → erase M' ≢ M) → InferenceResult Γ M

infer : ∀ (Γ : Context) (M : Term) → InferenceResult Γ M
infer Γ M with infer' Γ M | inspect (infer' Γ) M
...        | just ⟨ A , M' , refl ⟩ | _ = good M' refl
...        | nothing | [ ≡ ] = ungood λ{M' refl → helper ≡}
  where
  helper : ∀ {Γ A} {M : Γ ⊢ A} → infer' Γ (erase M) ≢ nothing
  helper {M = M} rewrite completeness M = λ ()

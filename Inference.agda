{-# OPTIONS --safe --without-K #-}
open import Stlc
open import Data.Nat
open import Data.Maybe
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

-- Untyped variable references and terms

data Var : Context → Set where
  head : ∀ {Γ A} → Var (Γ , A)
  tail : ∀ {Γ A} → Var Γ → Var (Γ , A)

data Term : Context → Set where
  `_ : ∀ {Γ} → Var Γ → Term Γ
  ƛ_⇒_ : ∀ {Γ} (A : Type) → Term (Γ , A) → Term Γ
  _∙_ : ∀ {Γ} → Term Γ → Term Γ → Term Γ
  `Z : ∀ {Γ} → Term Γ
  `S : ∀ {Γ} → Term Γ → Term Γ
  case_[Z⇒_|S⇒_] : ∀ {Γ} → Term Γ → Term Γ → Term (Γ , `ℕ) → Term Γ
  μ_ : ∀ {Γ A} → Term (Γ , A) → Term Γ

lookupVar : (Γ : Context) → (i : ℕ) → (i<len : i < length Γ) → Var Γ
lookupVar (_ , _) zero _ = head
lookupVar (Γ , _) (suc i) (s≤s i<len) = tail (lookupVar Γ i i<len)

#var : ∀ (i : ℕ) → {Γ : Context} → {i<len : True (i <? length Γ)} → Term Γ
#var i {Γ} {i<len} = ` lookupVar Γ i (toWitness i<len)

unify : ∀ (A B : Type) → Maybe (A ≡ B)
unify A B with Type≟ A B
...          | yes ≡ = just ≡
...          | no _ = nothing

eraseVar : ∀ {Γ A} → Γ ∋ A → Var Γ
eraseVar head = head
eraseVar (tail ∋A) = tail (eraseVar ∋A)

data InferenceVarResult {Γ} (x : Var Γ) : Set where
  ⟨_,_,_⟩ : ∀ (A : Type) (x' : Γ ∋ A) → eraseVar x' ≡ x → InferenceVarResult x

inferVar : ∀ {Γ} (x : Var Γ) → InferenceVarResult x
inferVar (head {A = A}) = ⟨ A , head , refl ⟩
-- I wish Agda has let binding for irrefutable patterns
inferVar (tail x) with inferVar x
...                  | ⟨ A , x' , refl ⟩ = ⟨ A , (tail x') , refl ⟩

erase : ∀ {Γ A} → Γ ⊢ A → Term Γ
erase (` x) = ` (eraseVar x)
erase (ƛ A ⇒ M) = ƛ A ⇒ erase M
erase (M₁ ∙ M₂) = erase M₁ ∙ erase M₂
erase `Z = `Z
erase (`S M) = `S (erase M)
erase case M [Z⇒ M₁ |S⇒ M₂ ] = case erase M [Z⇒ erase M₁ |S⇒ erase M₂ ]
erase (μ M) = μ erase M

-- Correct-by-type inference

data InferenceResult {Γ} (M : Term Γ) : Set where
  ⟨_,_,_⟩ : ∀ (A : Type) (M' : Γ ⊢ A) → erase M' ≡ M → InferenceResult M

infer : ∀ {Γ} (M : Term Γ) → Maybe (InferenceResult M)
infer (` x) with inferVar x
...            | ⟨ A , x' , refl ⟩ = just ⟨ A , ` x' , refl ⟩
infer (ƛ A ⇒ M) = do
  ⟨ B , M , refl ⟩ ← infer M
  just ⟨ A ⇒ B , ƛ A ⇒ M , refl ⟩
-- Ok, Agda actually has incomplete pattern matching in do-blocks, and works better than MonadFail!  Hooray!
infer (M₁ ∙ M₂) = do
  ⟨ A ⇒ B , M₁ , refl ⟩ ← infer M₁
                        where _ → nothing
  ⟨ A' , M₂ , refl ⟩ ← infer M₂
  refl ← unify A A'
  just ⟨ B , M₁ ∙ M₂ , refl ⟩
infer `Z = just ⟨ `ℕ , `Z , refl ⟩
infer (`S M) = do
  ⟨ A , M , refl ⟩ ← infer M
  refl ← unify A `ℕ
  just ⟨ `ℕ , `S M , refl ⟩
infer case M [Z⇒ M₁ |S⇒ M₂ ] = do
  ⟨ A , M , refl ⟩ ← infer M
  refl ← unify A `ℕ
  ⟨ B , M₁ , refl ⟩ ← infer M₁
  ⟨ B' , M₂ , refl ⟩ ← infer M₂
  refl ← unify B B'
  just ⟨ B , case M [Z⇒ M₁ |S⇒ M₂ ] , refl ⟩
infer (μ_ {Γ} {A} M) = do
  ⟨ A' , M , refl ⟩ ← infer M
  refl ← unify A A'
  just ⟨ A , μ M , refl ⟩

-- Examples

`ungood : Term ∅
`ungood = (`S (`S `Z)) ∙ `Z

_ : infer `ungood ≡ nothing
_ = refl

`plusungood : Term ∅
`plusungood = ƛ `ℕ ⇒ ƛ `ℕ ⇒ #var 0 ∙ #var 1

_ : infer `plusungood ≡ nothing
_ = refl

`doubleplusungood : Term ∅
`doubleplusungood = μ_ {A = `ℕ} (#var 0 ∙ `Z)

_ : infer `doubleplusungood ≡ nothing
_ = refl

-- Completeness

completenessVar : ∀ {Γ A} (x : Γ ∋ A) → inferVar (eraseVar x) ≡ ⟨ A , x , refl ⟩
completenessVar head = refl
completenessVar (tail x) rewrite completenessVar x = refl

-- Note that the following essentially asserts that Type is an h-Set.
unifySelf : ∀ (A : Type) → Type≟ A A ≡ yes refl
unifySelf `ℕ = refl
unifySelf (A ⇒ B) rewrite unifySelf A | unifySelf B = refl

completeness : ∀ {Γ A} (M : Γ ⊢ A) → infer (erase M) ≡ just ⟨ A , M , refl ⟩
completeness (` x) rewrite completenessVar x = refl
completeness (ƛ A ⇒ M) rewrite completeness M = refl
completeness (_∙_ {A = A} M₁ M₂)
  rewrite completeness M₁ | completeness M₂ | unifySelf A = refl
completeness `Z = refl
completeness (`S M) rewrite completeness M = refl
completeness {A = A} case M [Z⇒ M₁ |S⇒ M₂ ]
  rewrite completeness M | completeness M₁ | completeness M₂ | unifySelf A = refl
completeness {A = A} (μ M) rewrite completeness M | unifySelf A = refl

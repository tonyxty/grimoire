{-# OPTIONS --safe --without-K #-}
open import Stlc
open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

data Var : Context → Set where
  head : ∀ {Γ A} → Var (Γ , A)
  tail : ∀ {Γ A} → Var Γ → Var (Γ , A)

inferVar : ∀ {Γ} → Var Γ → Σ[ A ∈ Type ] (Γ ∋ A)
inferVar (head {A = A}) = ⟨ A , head ⟩
inferVar (tail x) = map₂ tail (inferVar x)

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

infer : ∀ {Γ} → Term Γ → Maybe (Σ[ A ∈ Type ] (Γ ⊢ A))
infer (` x) = just (map₂ `_ (inferVar x))
infer (ƛ A ⇒ M) = do
  ⟨ B , M ⟩ ← infer M
  just ⟨ A ⇒ B , ƛ A ⇒ M ⟩
-- I wish Agda has MonadFail and incomplete pattern matching in do-blocks
infer (M₁ ∙ M₂) with infer M₁
...                | just ⟨ A ⇒ B , M₁' ⟩ = do
                                         ⟨ A' , M₂ ⟩ ← infer M₂
                                         refl ← unify A A'
                                         just ⟨ B , M₁' ∙ M₂ ⟩
...                | _ = nothing
infer `Z = just ⟨ `ℕ , `Z ⟩
infer (`S M) = do
  ⟨ A , M ⟩ ← infer M
  refl ← unify A `ℕ
  just ⟨ `ℕ , `S M ⟩
infer case M [Z⇒ M₁ |S⇒ M₂ ] = do
  ⟨ A , M ⟩ ← infer M
  refl ← unify A `ℕ
  ⟨ B , M₁ ⟩ ← infer M₁
  ⟨ B' , M₂ ⟩ ← infer M₂
  refl ← unify B B'
  just ⟨ B , case M [Z⇒ M₁ |S⇒ M₂ ] ⟩
infer (μ_ {Γ} {A} M) = do
  ⟨ A' , M ⟩ ← infer M
  refl ← unify A A'
  just ⟨ A , μ M ⟩

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

{-# OPTIONS --safe --without-K #-}
open import Stlc
open import Data.Nat
open import Data.Maybe
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

-- Note on the idea of bidirectional type inference: a term can be typed in two ways: synthesis and inheritance.
-- In synthesis, the term is typed via some form of annotations.  The term and the context are the input, and the type is the output.
-- In inheritance, on the contrary, the type of the term is inferred, and the term itself must be check against it.  Thus the term, the context, and the type are all inputs.
-- For example, in an function application f ∙ x, f should be synthesized and then x can be inherited by looking at the type of f.

data Term↓ : Set
data Term↑ : Set

infix 5 `_
infixr 2 ƛ_
infixl 3 _∙_
infix 4 `S
infixr 2 μ_
infix 1 _↓_
infix 1 _↑

-- It's not strictly necessary to define Term↓ and Term↑ as two different types, but it makes the code easier to understand.
-- synthesized terms
data Term↓ where
  `_ : ℕ → Term↓
  _∙_ : Term↓ → Term↑ → Term↓
  _↓_ : Term↑ → Type → Term↓

-- inherited terms
data Term↑ where
  ƛ_ : Term↑ → Term↑
  `Z : Term↑
  `S : Term↑ → Term↑
  case_[Z⇒_|S⇒_] : Term↑ → Term↑ → Term↑ → Term↑
  μ_ : Term↑ → Term↑
  _↑ : Term↓ → Term↑

private
  `two : Term↑
  `two = `S (`S `Z)

  `plus : Term↓
  `plus = μ ƛ ƛ case ` 1 ↑ [Z⇒ ` 0 ↑ |S⇒ `S (` 3 ∙ (` 0 ↑) ∙ (` 1 ↑) ↑)] ↓ (`ℕ ↠ `ℕ ↠ `ℕ)

checkVar : ∀ (Γ : Context) (x : ℕ) → Maybe (∃[ A ] (Γ ∋ A))
checkVar ∅ x = nothing
checkVar (Γ , A) zero = just ⟨ A , head ⟩
checkVar (Γ , A) (suc x) = do
  ⟨ A , ∋ ⟩ ← checkVar Γ x
  just ⟨ A , tail ∋ ⟩

synthesize : ∀ (Γ : Context) → Term↓ → Maybe (∃[ A ] (Γ ⊢ A))
inherit : ∀ (Γ : Context) → (A : Type) → Term↑ → Maybe (Γ ⊢ A)

synthesize Γ (` x) = do
  ⟨ A , ∋ ⟩ ← checkVar Γ x
  just ⟨ A , ` ∋ ⟩
synthesize Γ (M₁ ∙ M₂) = do
  ⟨ A ↠ B , M₁ ⟩ ← synthesize Γ M₁
                 where _ → nothing
  M₂ ← inherit Γ A M₂
  just ⟨ B , M₁ ∙ M₂ ⟩
synthesize Γ (M ↓ A) = do
  M ← inherit Γ A M
  just ⟨ A , M ⟩

inherit Γ `ℕ (ƛ M) = nothing
inherit Γ (A ↠ B) (ƛ M) = do
  M ← inherit (Γ , A) B M
  just (ƛ A ⇒ M)
inherit Γ `ℕ `Z = just `Z
inherit Γ (A ↠ B) `Z = nothing
inherit Γ `ℕ (`S M) = do
  M ← inherit Γ `ℕ M
  just (`S M)
inherit Γ (A ↠ B) (`S M) = nothing
inherit Γ A case M [Z⇒ M₁ |S⇒ M₂ ] = do
  M ← inherit Γ `ℕ M
  M₁ ← inherit Γ A M₁
  M₂ ← inherit (Γ , `ℕ) A M₂
  just (case M [Z⇒ M₁ |S⇒ M₂ ])
inherit Γ A (μ M) = do
  M ← inherit (Γ , A) A M
  just (μ M)
inherit Γ A (M ↑) = do
  ⟨ A' , M ⟩ ← synthesize Γ M
  refl ← decToMaybe (Type≟ A A')
  just M

private
  _ : inherit ∅ `ℕ `two ≡ just (`S (`S `Z))
  _ = refl

  `plus⁺ : ∅ ⊢ `ℕ ↠ `ℕ ↠ `ℕ
  `plus⁺ = proj₂ (from-just (synthesize ∅ `plus))

  _ : result (eval 20 (`plus⁺ ∙ (`S (`S `Z)) ∙ (`S (`S `Z)))) ≡ just (`S (`S (`S (`S `Z))))
  _ = refl

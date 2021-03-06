{-# OPTIONS --safe --without-K #-}
module Inference where

open import Terms
open import Reduction
open import Data.Nat
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- Note on the idea of bidirectional type inference: a term can be typed in two ways: synthesis and inheritance.
-- In synthesis, the term is typed via some form of annotations.  The term and the context are the input, and the type is the output.
-- In inheritance, on the contrary, the type of the term is inferred, and the term itself must be check against it.  Thus the term, the context, and the type are all inputs.
-- For example, in an function application f ∙ x, f should be synthesized and then x can be inherited by looking at the type of f.

Var = ℕ

-- It's not strictly necessary to define Term↓ and Term↑ as two different types, but it makes the code easier to understand.
data Term↓ : Set
data Term↑ : Set

infix 1 _↓_
infix 1 _↑

-- synthesized terms
data Term↓ where
  `_ : Var → Term↓
  _∙_ : Term↓ → Term↑ → Term↓
  _↓_ : Term↑ → Type → Term↓

-- inherited terms
data Term↑ where
  ƛ_ : Term↑ → Term↑
  Z : Term↑
  S_ : Term↑ → Term↑
  case_[Z⇒_|S⇒_] : Term↑ → Term↑ → Term↑ → Term↑
  ⟪_,_⟫ : Term↑ → Term↑ → Term↑
  case_[⟪,⟫⇒_] : Term↓ → Term↑ → Term↑
  μ_ : Term↑ → Term↑
  _↑ : Term↓ → Term↑

private
  `two' : Term↑
  `two' = S S Z

  `plus' : Term↓
  `plus' = μ ƛ ƛ case ` 1 ↑ [Z⇒ ` 0 ↑ |S⇒ S (` 3 ∙ (` 0 ↑) ∙ (` 1 ↑) ↑)] ↓ `ℕ ↠ `ℕ ↠ `ℕ

  `proj₁' : ∀ (A₁ A₂ : Type) → Term↓
  `proj₁' A₁ A₂ = ƛ case ` 0 [⟪,⟫⇒ ` 1 ↑ ] ↓ A₁ ⊗ A₂ ↠ A₁

checkVar : ∀ (Γ : Context) (x : ℕ) → Maybe (∃[ A ] (Γ ∋ A))
checkVar ∅ x = nothing
checkVar (Γ , A) zero = just (A , zero)
checkVar (Γ , A) (suc x) = do
  A , x ← checkVar Γ x
  just (A , suc x)

synthesize : ∀ (Γ : Context) → Term↓ → Maybe (∃[ A ] (Γ ⊢ A))
inherit : ∀ (Γ : Context) → (A : Type) → Term↑ → Maybe (Γ ⊢ A)

synthesize Γ (` x) = do
  A , x ← checkVar Γ x
  just (A , ` x)
synthesize Γ (M₁ ∙ M₂) = do
  A ↠ B , M₁ ← synthesize Γ M₁
               where _ → nothing
  M₂ ← inherit Γ A M₂
  just (B , M₁ ∙ M₂)
synthesize Γ (M ↓ A) = do
  M ← inherit Γ A M
  just (A , M)

inherit Γ (A ↠ B) (ƛ M) = do
  M ← inherit (Γ , A) B M
  just (ƛ A ⇒ M)
inherit Γ _ (ƛ M) = nothing
inherit Γ `ℕ Z = just Z
inherit Γ _ Z = nothing
inherit Γ `ℕ (S M) = do
  M ← inherit Γ `ℕ M
  just (S M)
inherit Γ _ (S M) = nothing
inherit Γ A case M [Z⇒ M₁ |S⇒ M₂ ] = do
  M ← inherit Γ `ℕ M
  M₁ ← inherit Γ A M₁
  M₂ ← inherit (Γ , `ℕ) A M₂
  just (case M [Z⇒ M₁ |S⇒ M₂ ])
inherit Γ (A₁ ⊗ A₂) ⟪ M₁ , M₂ ⟫ = do
  M₁ ← inherit Γ A₁ M₁
  M₂ ← inherit Γ A₂ M₂
  just ⟪ M₁ , M₂ ⟫
inherit Γ _ ⟪ M₁ , M₂ ⟫ = nothing
inherit Γ A case M [⟪,⟫⇒ N ] = do
  A₁ ⊗ A₂ , M ← synthesize Γ M
                where _ → nothing
  N ← inherit ((Γ , A₁) , A₂) A N
  just case M [⟪,⟫⇒ N ]
inherit Γ A (μ M) = do
  M ← inherit (Γ , A) A M
  just (μ M)
inherit Γ A (M ↑) = do
  A' , M ← synthesize Γ M
  refl ← unify A A'
  just M

private
  _ : inherit ∅ `ℕ `two' ≡ just `two
  _ = refl

  `plus⁺ : ∅ ⊢ `ℕ ↠ `ℕ ↠ `ℕ
  `plus⁺ = proj₂ (from-just (synthesize ∅ `plus'))

  _ : result (eval 20 (`plus⁺ ∙ `two ∙ `two)) ≡ just ⌜ 4 ⌝
  _ = refl

  `proj₁⁺ : ∅ ⊢ (`ℕ ↠ `ℕ) ⊗ `ℕ ↠ (`ℕ ↠ `ℕ)
  `proj₁⁺ = proj₂ (from-just (synthesize ∅ (`proj₁' (`ℕ ↠ `ℕ) `ℕ)))

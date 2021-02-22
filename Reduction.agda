{-# OPTIONS --safe --without-K #-}
module Reduction where

open import Terms
open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Reduction

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {Γ A B} {M : Γ , A ⊢ B} → Value (ƛ A ⇒ M)
  V-Z : ∀ {Γ} → Value (Z {Γ})
  V-S : ∀ {Γ} {V : Γ ⊢ `ℕ} → Value V → Value (S V)
  V-⟪,⟫ : ∀ {Γ A₁ A₂} {V₁ : Γ ⊢ A₁} {V₂ : Γ ⊢ A₂} → Value V₁ → Value V₂ → Value ⟪ V₁ , V₂ ⟫

infix 0 _—→_
data _—→_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where
  ξ-∙₁ : ∀ {Γ A B} {M M' : Γ ⊢ A ↠ B} {N : Γ ⊢ A} → M —→ M' → M ∙ N —→ M' ∙ N
  ξ-∙₂ : ∀ {Γ A B} {V : Γ ⊢ A ↠ B} {N N' : Γ ⊢ A} → Value V → N —→ N' → V ∙ N —→ V ∙ N'
  β-ƛ : ∀ {Γ A B} {M : Γ , A ⊢ B} {V : Γ ⊢ A} → Value V → (ƛ A ⇒ M) ∙ V —→ M [ V ]
  ξ-S : ∀ {Γ} {M M' : Γ ⊢ `ℕ} → M —→ M' → S M —→ S M'
  ξ-case-`ℕ : ∀ {Γ A} {M M' : Γ ⊢ `ℕ} {N₁ : Γ ⊢ A} {N₂ : Γ , `ℕ ⊢ A} → M —→ M' → case M [Z⇒ N₁ |S⇒ N₂ ] —→ case M' [Z⇒ N₁ |S⇒ N₂ ]
  β-Z : ∀ {Γ A} {N₁ : Γ ⊢ A} {N₂ : Γ , `ℕ ⊢ A} → case Z [Z⇒ N₁ |S⇒ N₂ ] —→ N₁
  β-S : ∀ {Γ A} {V : Γ ⊢ `ℕ} {N₁ : Γ ⊢ A} {N₂ : Γ , `ℕ ⊢ A} → Value V → case S V [Z⇒ N₁ |S⇒ N₂ ] —→ N₂ [ V ]
  ξ-⟪,⟫₁ : ∀ {Γ A₁ A₂} {M₁ M₁' : Γ ⊢ A₁} {M₂ : Γ ⊢ A₂} → M₁ —→ M₁' → ⟪ M₁ , M₂ ⟫ —→ ⟪ M₁' , M₂ ⟫
  ξ-⟪,⟫₂ : ∀ {Γ A₁ A₂} {V₁ : Γ ⊢ A₁} {M₂ M₂' : Γ ⊢ A₂} → Value V₁ → M₂ —→ M₂' → ⟪ V₁ , M₂ ⟫ —→ ⟪ V₁ , M₂' ⟫
  ξ-case-⊗ : ∀ {Γ A₁ A₂ B} {M M' : Γ ⊢ A₁ ⊗ A₂} {N : Γ , A₁ , A₂ ⊢ B} → M —→ M' → case M [⟪,⟫⇒ N ] —→ case M' [⟪,⟫⇒ N ]
  β-⟪,⟫ : ∀ {Γ A₁ A₂ B} {V₁ : Γ ⊢ A₁} {V₂ : Γ ⊢ A₂} {N : Γ , A₁ , A₂ ⊢ B} → Value V₁ → Value V₂ →
    case ⟪ V₁ , V₂ ⟫ [⟪,⟫⇒ N ] —→ N [ rename tail V₂ ] [ V₁ ]
  β-μ : ∀ {Γ A} {M : Γ , A ⊢ A} → μ M —→ M [ μ M ]

infixr 0 _—↠_
infix 1 _∎
infixr 0 _—→⟨_⟩_

data _—↠_ {Γ A} : Γ ⊢ A → Γ ⊢ A → Set where
  _∎ : ∀ (M : Γ ⊢ A) → M —↠ M
  _—→⟨_⟩_ : ∀ (L : Γ ⊢ A) {M N} → L —→ M → M —↠ N → L —↠ N

-- Example of reduction

_ : `plus {∅} ∙ `one ∙ `one —↠ `two
_ =
    `plus ∙ `one ∙ `one
  —→⟨ ξ-∙₁ (ξ-∙₁ β-μ) ⟩
    (ƛ `ℕ ⇒ ƛ `ℕ ⇒ case # 1 [Z⇒ # 0 |S⇒ S (`plus ∙ # 0 ∙ # 1) ]) ∙ `one ∙ `one
  —→⟨ ξ-∙₁ (β-ƛ (V-S V-Z)) ⟩
    (ƛ `ℕ ⇒ case `one [Z⇒ # 0 |S⇒ S (`plus ∙ # 0 ∙ # 1) ]) ∙ `one
  —→⟨ β-ƛ (V-S V-Z) ⟩
    case `one [Z⇒ `one |S⇒ S (`plus ∙ # 0 ∙ `one) ]
  —→⟨ β-S V-Z ⟩
    S (`plus ∙ Z ∙ `one)
  —→⟨ ξ-S (ξ-∙₁ (ξ-∙₁ β-μ)) ⟩
    S ((ƛ `ℕ ⇒ ƛ `ℕ ⇒ case # 1 [Z⇒ # 0 |S⇒ S (`plus ∙ # 0 ∙ # 1) ]) ∙ Z ∙ `one)
  —→⟨ ξ-S (ξ-∙₁ (β-ƛ V-Z)) ⟩
    S ((ƛ `ℕ ⇒ case Z [Z⇒ # 0 |S⇒ S (`plus ∙ # 0 ∙ # 1) ]) ∙ `one)
  —→⟨ ξ-S (β-ƛ (V-S V-Z)) ⟩
    S (case Z [Z⇒ `one |S⇒ S (`plus ∙ # 0 ∙ `one) ])
  —→⟨ ξ-S β-Z ⟩
    `two
  ∎

-- Properties of reduction

V¬—→ : ∀ {Γ A} → {M N : Γ ⊢ A} → Value M → ¬ (M —→ N)
V¬—→ (V-S VM) (ξ-S M—→N) = V¬—→ VM M—→N
V¬—→ (V-⟪,⟫ VM₁ VM₂) (ξ-⟪,⟫₁ M₁—→N₁) = V¬—→ VM₁ M₁—→N₁
V¬—→ (V-⟪,⟫ VM₁ VM₂) (ξ-⟪,⟫₂ _ M₂—→N₂) = V¬—→ VM₂ M₂—→N₂

data Progress {A} (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A} → M —→ N → Progress M
  value : Value M → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (ƛ A ⇒ M) = value V-ƛ
progress (M₁ ∙ M₂) with progress M₁
...                   | step M₁—→N₁ = step (ξ-∙₁ M₁—→N₁)
...                   | value V-ƛ with progress M₂
...                               | step M₂—→N₂ = step (ξ-∙₂ V-ƛ M₂—→N₂)
...                               | value VM₂ = step (β-ƛ VM₂)
progress Z = value V-Z
progress (S M) with progress M
...                | step M—→N = step (ξ-S M—→N)
...                | value VM = value (V-S VM)
progress case M [Z⇒ M₁ |S⇒ M₂ ] with progress M
...                                | step M—→N = step (ξ-case-`ℕ M—→N)
...                                | value V-Z = step β-Z
...                                | value (V-S V-M) = step (β-S V-M)
progress ⟪ M₁ , M₂ ⟫ with progress M₁
...                     | step M₁—→N₁ = step (ξ-⟪,⟫₁ M₁—→N₁)
...                     | value VM₁ with progress M₂
...                                    | step M₂—→N₂ = step (ξ-⟪,⟫₂ VM₁ M₂—→N₂)
...                                    | value VM₂ = value (V-⟪,⟫ VM₁ VM₂)
progress case M [⟪,⟫⇒ M' ] with progress M
...                           | step M—→N = step (ξ-case-⊗ M—→N)
...                           | value (V-⟪,⟫ VM₁ VM₂) = step (β-⟪,⟫ VM₁ VM₂)
progress (μ M) = step β-μ

-- we really need a way to automate this!
deterministic : ∀ {Γ A} {M M' M'' : Γ ⊢ A} → (M —→ M') → (M —→ M'') → M' ≡ M''
deterministic (ξ-∙₁ L—→L') (ξ-∙₁ L—→L'') rewrite deterministic L—→L' L—→L'' = refl
deterministic (ξ-∙₁ L—→L') (ξ-∙₂ VL _) = ⊥-elim (V¬—→ VL L—→L')
deterministic (ξ-∙₂ VL _) (ξ-∙₁ L—→L'') = ⊥-elim (V¬—→ VL L—→L'')
deterministic (ξ-∙₂ _ L—→L') (ξ-∙₂ _ L—→L'') rewrite deterministic L—→L' L—→L'' = refl
deterministic (ξ-∙₂ _ L—→L') (β-ƛ VL) = ⊥-elim (V¬—→ VL L—→L')
deterministic (β-ƛ VL) (ξ-∙₂ _ L—→L'') = ⊥-elim (V¬—→ VL L—→L'')
deterministic (β-ƛ _) (β-ƛ _) = refl
deterministic (ξ-S L—→L') (ξ-S L—→L'') rewrite deterministic L—→L' L—→L'' = refl
deterministic (ξ-case-`ℕ L—→L') (ξ-case-`ℕ L—→L'') rewrite deterministic L—→L' L—→L'' = refl
deterministic (ξ-case-`ℕ L—→L') (β-S VL) = ⊥-elim (V¬—→ (V-S VL) L—→L')
deterministic β-Z β-Z = refl
deterministic (β-S VL) (ξ-case-`ℕ L—→L'') = ⊥-elim (V¬—→ (V-S VL) L—→L'')
deterministic (β-S _) (β-S _) = refl
deterministic (ξ-⟪,⟫₁ L—→L') (ξ-⟪,⟫₁ L—→L'') rewrite deterministic L—→L' L—→L'' = refl
deterministic (ξ-⟪,⟫₁ L—→L') (ξ-⟪,⟫₂ VL _) = ⊥-elim (V¬—→ VL L—→L')
deterministic (ξ-⟪,⟫₂ VL _) (ξ-⟪,⟫₁ L—→L'') = ⊥-elim (V¬—→ VL L—→L'')
deterministic (ξ-⟪,⟫₂ _ L—→L') (ξ-⟪,⟫₂ _ L—→L'') rewrite deterministic L—→L' L—→L'' = refl
deterministic (ξ-case-⊗ L—→L') (ξ-case-⊗ L—→L'') rewrite deterministic L—→L' L—→L'' = refl
deterministic (ξ-case-⊗ L—→L') (β-⟪,⟫ VL₁ VL₂) = ⊥-elim (V¬—→ (V-⟪,⟫ VL₁ VL₂) L—→L')
deterministic (β-⟪,⟫ VL₁ VL₂) (ξ-case-⊗ L—→L'') = ⊥-elim (V¬—→ (V-⟪,⟫ VL₁ VL₂) L—→L'')
deterministic (β-⟪,⟫ _ _) (β-⟪,⟫ _ _) = refl
deterministic β-μ β-μ = refl

data Steps {A} (M : ∅ ⊢ A) : Set where
  more : ∀ {N} → M —↠ N → Steps M
  done : ∀ {V} → M —↠ V → Value V → Steps M

eval : ∀ {A} → ℕ → (M : ∅ ⊢ A) → Steps M
eval zero M = more (M ∎)
eval (suc n) M with progress M
...               | value VM = done (M ∎) VM
...               | step {N} M—→N with eval n N
...                                  | more N—↠N' = more (M —→⟨ M—→N ⟩ N—↠N')
...                                  | done N—↠V V = done (M —→⟨ M—→N ⟩ N—↠V) V

result : ∀ {A} {M : ∅ ⊢ A} → Steps M → Maybe (∅ ⊢ A)
result (more _) = nothing
result (done {V} _ _) = just V

-- Examples of evaluations

`inf : ∅ ⊢ `ℕ
`inf = μ S # 0

_ : result (eval 100 `inf) ≡ nothing
_ = refl

_ : result (eval 20 (`plus ∙ `two ∙ `two)) ≡ just ⌜ 4 ⌝
_ = refl

_ : result (eval 3 (`proj₁ ∙ ⟪ `two , `two ⟫)) ≡ just `two
_ = refl

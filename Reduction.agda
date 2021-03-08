{-# OPTIONS --safe --without-K #-}
module Reduction where

open import Terms
open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

private
  variable
    Γ : Context
    A B A₁ A₂ : Type

-- Reduction

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {M : Γ , A ⊢ B} → Value (ƛ A ⇒ M)
  V-Z : Value (Z {Γ})
  V-S : ∀ {V : Γ ⊢ `ℕ} → Value V → Value (S V)
  V-⟪,⟫ : ∀ {V₁ : Γ ⊢ A₁} {V₂ : Γ ⊢ A₂} → Value V₁ → Value V₂ → Value ⟪ V₁ , V₂ ⟫

infix 0 _—→_
data _—→_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where
  ξ-∙₁ : ∀ {M M' : Γ ⊢ A ↠ B} {N : Γ ⊢ A} → M —→ M' → M ∙ N —→ M' ∙ N
  ξ-∙₂ : ∀ {V : Γ ⊢ A ↠ B} {N N' : Γ ⊢ A} → Value V → N —→ N' → V ∙ N —→ V ∙ N'
  β-ƛ : ∀ {M : Γ , A ⊢ B} {V : Γ ⊢ A} → Value V → (ƛ A ⇒ M) ∙ V —→ M [ V ]
  ξ-S : ∀ {M M' : Γ ⊢ `ℕ} → M —→ M' → S M —→ S M'
  ξ-case-`ℕ : ∀ {M M' : Γ ⊢ `ℕ} {N₁ : Γ ⊢ A} {N₂ : Γ , `ℕ ⊢ A} → M —→ M' →
    case M [Z⇒ N₁ |S⇒ N₂ ] —→ case M' [Z⇒ N₁ |S⇒ N₂ ]
  β-Z : ∀ {N₁ : Γ ⊢ A} {N₂ : Γ , `ℕ ⊢ A} → case Z [Z⇒ N₁ |S⇒ N₂ ] —→ N₁
  β-S : ∀ {V : Γ ⊢ `ℕ} {N₁ : Γ ⊢ A} {N₂ : Γ , `ℕ ⊢ A} → Value V → case S V [Z⇒ N₁ |S⇒ N₂ ] —→ N₂ [ V ]
  ξ-⟪,⟫₁ : ∀ {M₁ M₁' : Γ ⊢ A₁} {M₂ : Γ ⊢ A₂} → M₁ —→ M₁' → ⟪ M₁ , M₂ ⟫ —→ ⟪ M₁' , M₂ ⟫
  ξ-⟪,⟫₂ : ∀ {V₁ : Γ ⊢ A₁} {M₂ M₂' : Γ ⊢ A₂} → Value V₁ → M₂ —→ M₂' → ⟪ V₁ , M₂ ⟫ —→ ⟪ V₁ , M₂' ⟫
  ξ-case-⊗ : ∀ {M M' : Γ ⊢ A₁ ⊗ A₂} {N : Γ , A₁ , A₂ ⊢ B} → M —→ M' → case M [⟪,⟫⇒ N ] —→ case M' [⟪,⟫⇒ N ]
  β-⟪,⟫ : ∀ {V₁ : Γ ⊢ A₁} {V₂ : Γ ⊢ A₂} {N : Γ , A₁ , A₂ ⊢ B} → Value V₁ → Value V₂ →
    case ⟪ V₁ , V₂ ⟫ [⟪,⟫⇒ N ] —→ N [ V₂ ♯ ] [ V₁ ]
  β-μ : ∀ {M : Γ , A ⊢ A} → μ M —→ M [ μ M ]

infixr 0 _—↠_
infix 1 _∎
infixr 0 _—→⟨_⟩_
infixr 0 _—≡→⟨_⟩_
infixr 0 _—↠⟨_⟩_

data _—↠_ : Γ ⊢ A → Γ ⊢ A → Set where
  _∎ : ∀ (M : Γ ⊢ A) → M —↠ M
  _—→⟨_⟩_ : ∀ {M N} (L : Γ ⊢ A) → L —→ M → M —↠ N → L —↠ N

_—≡→⟨_⟩_ : ∀ {M N} (L : Γ ⊢ A) → L ≡ M → M —↠ N → L —↠ N
_ —≡→⟨ refl ⟩ M—↠N = M—↠N

_—↠⟨_⟩_ : ∀ {M N} (L : Γ ⊢ A) → L —↠ M → M —↠ N → L —↠ N
L —↠⟨ _ ∎ ⟩ M—↠N = M—↠N
L —↠⟨ _ —→⟨ L—→L' ⟩ L'—↠M ⟩ M—↠N = L —→⟨ L—→L' ⟩ _ —↠⟨ L'—↠M ⟩ M—↠N

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

V¬—→ : ∀ {M N : Γ ⊢ A} → Value M → ¬ (M —→ N)
V¬—→ (V-S VM) (ξ-S M—→N) = V¬—→ VM M—→N
V¬—→ (V-⟪,⟫ VM₁ VM₂) (ξ-⟪,⟫₁ M₁—→N₁) = V¬—→ VM₁ M₁—→N₁
V¬—→ (V-⟪,⟫ VM₁ VM₂) (ξ-⟪,⟫₂ _ M₂—→N₂) = V¬—→ VM₂ M₂—→N₂

data Progress (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A} → M —→ N → Progress M
  value : Value M → Progress M

progress : ∀ (M : ∅ ⊢ A) → Progress M
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
deterministic : ∀ {M M' M'' : Γ ⊢ A} → (M —→ M') → (M —→ M'') → M' ≡ M''
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

data Steps (M : ∅ ⊢ A) : Set where
  more : ∀ {N} → M —↠ N → Steps M
  done : ∀ {V} → M —↠ V → Value V → Steps M

eval : ℕ → ∀ (M : ∅ ⊢ A) → Steps M
eval zero M = more (M ∎)
eval (suc n) M with progress M
...               | value VM = done (M ∎) VM
...               | step {N} M—→N with eval n N
...                                  | more N—↠N' = more (M —→⟨ M—→N ⟩ N—↠N')
...                                  | done N—↠V V = done (M —→⟨ M—→N ⟩ N—↠V) V

result : ∀ {M : ∅ ⊢ A} → Steps M → Maybe (∅ ⊢ A)
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

-- Property of `plus, formalized as a metatheorem
V-⌜_⌝ : ∀ (n : ℕ) → Value {Γ} ⌜ n ⌝
V-⌜ zero ⌝ = V-Z
V-⌜ suc n ⌝ = V-S V-⌜ n ⌝

-- this should be generalized to a definition of closed terms and a proof that closed terms are substitution invariant
rename-⌜_⌝ : ∀ {M : ∅ ⊢ A} (n : ℕ) → ⌜ n ⌝ ♯ [ M ] ≡ ⌜ n ⌝
rename-⌜ zero ⌝ = refl
rename-⌜ suc n ⌝ = cong S_ rename-⌜ n ⌝

ξ-S' : ∀ {Γ} {M M' : Γ ⊢ `ℕ} → M —↠ M' → S M —↠ S M'
ξ-S' {M = M} (_ ∎) = S M ∎
ξ-S' {M = M} (_ —→⟨ M—→L ⟩ L—↠M') = S M —→⟨ ξ-S M—→L ⟩ ξ-S' L—↠M'

`plus-+ : ∀ (m n : ℕ) → `plus {∅} ∙ ⌜ m ⌝ ∙ ⌜ n ⌝ —↠ ⌜ m + n ⌝
`plus-+ zero n =
    `plus ∙ ⌜ zero ⌝ ∙ ⌜ n ⌝
  —→⟨ ξ-∙₁ (ξ-∙₁ β-μ) ⟩
    (ƛ `ℕ ⇒ ƛ `ℕ ⇒ case # 1 [Z⇒ # 0 |S⇒ S (`plus ∙ # 0 ∙ # 1) ]) ∙ Z ∙ ⌜ n ⌝
  —→⟨ ξ-∙₁ (β-ƛ V-Z) ⟩
    (ƛ `ℕ ⇒ case Z [Z⇒ # 0 |S⇒ S (`plus ∙ # 0 ∙ # 1) ]) ∙ ⌜ n ⌝
  —→⟨ β-ƛ V-⌜ n ⌝ ⟩
    case Z [Z⇒ ⌜ n ⌝ |S⇒ S (`plus ∙ # 0 ∙ ⌜ n ⌝ ♯) ]
  —→⟨ β-Z ⟩
    ⌜ n ⌝
  ∎
`plus-+ (suc m) n =
    `plus ∙ ⌜ suc m ⌝ ∙ ⌜ n ⌝
  —→⟨ ξ-∙₁ (ξ-∙₁ β-μ) ⟩
    (ƛ `ℕ ⇒ ƛ `ℕ ⇒ case # 1 [Z⇒ # 0 |S⇒ S (`plus ∙ # 0 ∙ # 1) ]) ∙ ⌜ suc m ⌝ ∙ ⌜ n ⌝
  —→⟨ ξ-∙₁ (β-ƛ V-⌜ suc m ⌝ ) ⟩
    (ƛ `ℕ ⇒ case S ⌜ m ⌝ ♯ [Z⇒ # 0 |S⇒ S (`plus ∙ # 0 ∙ # 1) ]) ∙ ⌜ n ⌝
  —→⟨ β-ƛ V-⌜ n ⌝ ⟩
    case S (⌜ m ⌝ ♯ [ ⌜ n ⌝ ]) [Z⇒ ⌜ n ⌝ |S⇒ S (`plus ∙ # 0 ∙ ⌜ n ⌝ ♯) ]
  —≡→⟨ cong (λ M → case S M [Z⇒ ⌜ n ⌝ |S⇒ S (`plus ∙ # 0 ∙ ⌜ n ⌝ ♯) ]) (rename-⌜ m ⌝) ⟩
    case S ⌜ m ⌝ [Z⇒ ⌜ n ⌝ |S⇒ S (`plus ∙ # 0 ∙ ⌜ n ⌝ ♯) ]
  —→⟨ β-S V-⌜ m ⌝ ⟩
    S (`plus ∙ ⌜ m ⌝ ∙ ⌜ n ⌝ ♯ [ ⌜ m ⌝ ])
  —≡→⟨ cong (λ M → S (`plus ∙ ⌜ m ⌝ ∙ M)) rename-⌜ n ⌝ ⟩
    S (`plus ∙ ⌜ m ⌝ ∙ ⌜ n ⌝)
  —↠⟨ ξ-S' (`plus-+ m n) ⟩
    ⌜ suc (m + n) ⌝
  ∎

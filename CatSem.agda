{-# OPTIONS --without-K #-}

open import Stlc
open import Categories.Category.Core
open import Level
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning

postulate
  extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

subst-≡ : ∀ {Γ Δ} {ρ σ : Subst Γ Δ} → (∀ {A} (∋A : Δ ∋ A) → ρ _ ∋A ≡ σ _ ∋A) → ρ ≡ σ
subst-≡ pt≡ = extensionality (λ A → extensionality (pt≡ {A}))

idₛ : ∀ {Γ} → Subst Γ Γ
idₛ _ ∋A = ` ∋A

-- This signature leads to an infinitude of troubles with explicit/implicit arguments.
-- In the end I had to change the definition of Subst to make the type parameter explicit.
-- Someone should fix this.  Really.
idₛ♯≡idₛ : ∀ (Γ : Context) (A : Type) → idₛ {Γ} ⋆ A ≡ idₛ
idₛ♯≡idₛ Γ A = subst-≡ (λ{head → refl; (tail _) → refl})

subst-idₛ : ∀ {Γ} {A : Type} (M : Γ ⊢ A) → subst idₛ M ≡ M
subst-idₛ (` x) = refl
subst-idₛ {Γ} {A ⇒ B} (ƛ .A ⇒ M) rewrite idₛ♯≡idₛ Γ A | subst-idₛ M = refl
subst-idₛ (M₁ ∙ M₂) rewrite subst-idₛ M₁ | subst-idₛ M₂ = refl
subst-idₛ `Z = refl
subst-idₛ (`S M) rewrite subst-idₛ M = refl
subst-idₛ {Γ} case M [Z⇒ M₁ |S⇒ M₂ ] rewrite subst-idₛ M
                                           | subst-idₛ M₁
                                           | idₛ♯≡idₛ Γ `ℕ | subst-idₛ M₂ = refl
subst-idₛ {Γ} {A} (μ M) rewrite idₛ♯≡idₛ Γ A | subst-idₛ M = refl

infixr 9 _∘ₛ_
_∘ₛ_ : ∀ {Γ Δ Θ} → Subst Δ Θ → Subst Γ Δ → Subst Γ Θ
(σ ∘ₛ ρ) _ ∋A = subst ρ (σ _ ∋A)

⋆-distr-∘ₛ : ∀ {Γ Δ Θ} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (A : Type) →
  (σ ∘ₛ ρ) ⋆ A ≡ (σ ⋆ A) ∘ₛ (ρ ⋆ A)
⋆-distr-∘ₛ ρ σ A = subst-≡ (pt≡ ρ σ A)
  where
  helper : ∀ {Γ Δ B} (ρ : Subst Γ Δ) (M : Δ ⊢ B) (A : Type) →
    rename tail (subst ρ M) ≡ subst (ρ ⋆ A) (rename tail M)
  helper ρ (` x) A = refl
  helper ρ (ƛ C ⇒ M) A = {!!}
  helper ρ (M₁ ∙ M₂) A rewrite helper ρ M₁ A | helper ρ M₂ A = refl
  helper ρ `Z A = refl
  helper ρ (`S M) A rewrite helper ρ M A = refl
  helper ρ case M [Z⇒ M₁ |S⇒ M₂ ] A rewrite helper ρ M A
                                          | helper ρ M₁ A
                                          = {!!}
  helper {B = B} ρ (μ M) A = {!!}

  pt≡ : ∀ {Γ Δ Θ} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (A : Type) {B} (∋B : Θ , A ∋ B) →
    ((σ ∘ₛ ρ) ⋆ A )_ ∋B ≡ (σ ⋆ A ∘ₛ ρ ⋆ A) _ ∋B
  pt≡ ρ σ A head = refl
  pt≡ ρ σ A (tail ∋B) = helper _ (σ _ ∋B) _

subst-∘ₛ : ∀ {Γ Δ Θ A} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (M : Θ ⊢ A) → subst ρ (subst σ M) ≡ subst (σ ∘ₛ ρ) M
subst-∘ₛ ρ σ (` x) = refl
subst-∘ₛ ρ σ (ƛ A ⇒ M) rewrite ⋆-distr-∘ₛ ρ σ A | subst-∘ₛ (ρ ♯) (σ ♯) M = refl
subst-∘ₛ ρ σ (M₁ ∙ M₂) rewrite subst-∘ₛ ρ σ M₁ | subst-∘ₛ ρ σ M₂ = refl
subst-∘ₛ ρ σ `Z = refl
subst-∘ₛ ρ σ (`S M) rewrite subst-∘ₛ ρ σ M = refl
subst-∘ₛ ρ σ case M [Z⇒ M₁ |S⇒ M₂ ] rewrite subst-∘ₛ ρ σ M
                                          | subst-∘ₛ ρ σ M₁
                                          | ⋆-distr-∘ₛ ρ σ `ℕ | subst-∘ₛ (ρ ♯) (σ ♯) M₂ = refl
subst-∘ₛ {A = A} ρ σ (μ M) rewrite ⋆-distr-∘ₛ ρ σ A | subst-∘ₛ (ρ ♯) (σ ♯) M = refl

∘ₛ-identityʳ : ∀ {Γ Δ} {ρ : Subst Γ Δ} → ρ ∘ₛ idₛ ≡ ρ
∘ₛ-identityʳ {ρ = ρ} = subst-≡ (pt≡ ρ)
  where
  pt≡ : ∀ {Γ Δ A} (ρ : Subst Γ Δ) (∋A : Δ ∋ A) → (ρ ∘ₛ idₛ) _ ∋A ≡ ρ _ ∋A
  pt≡ ρ ∋A rewrite subst-idₛ (ρ _ ∋A) = refl

∘ₛ-assoc : ∀ {Γ Δ Θ Ξ} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (τ : Subst Θ Ξ) → (τ ∘ₛ σ) ∘ₛ ρ ≡ τ ∘ₛ (σ ∘ₛ ρ)
∘ₛ-assoc ρ σ τ = subst-≡ (λ ∋A → subst-∘ₛ ρ σ (τ _ ∋A))

ContextCategory : Category 0ℓ 0ℓ 0ℓ
ContextCategory = record
                    { Obj = Context
                    ; _⇒_ = Subst
                    ; _≈_ = _≡_
                    ; id = idₛ
                    ; _∘_ = _∘ₛ_
                    ; assoc = λ {_ _ _ _ ρ σ τ} → ∘ₛ-assoc ρ σ τ
                    ; sym-assoc = λ {_ _ _ _ ρ σ τ} → sym (∘ₛ-assoc ρ σ τ)
                    ; identityˡ = refl
                    ; identityʳ = ∘ₛ-identityʳ
                    ; identity² = refl
                    ; equiv = Eq.isEquivalence
                    ; ∘-resp-≈ = λ{refl refl → refl}
                    }

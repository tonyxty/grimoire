open import Stlc
open import Categories.Category.Core
open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning

postulate
  extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

idₛ : ∀ {Γ} → Subst Γ Γ
idₛ _ ∋A = ` ∋A

-- This signature leads to an infinitude of troubles with explicit/implicit arguments.
-- In the end I had to change the definition of Subst to make the type parameter explicit.
-- Someone should fix this.  Really.
ext-idₛ≡idₛ : ∀ (Γ : Context) (A : Type) → ext-subst {Γ} {Γ} {A} idₛ ≡ idₛ
ext-idₛ≡idₛ Γ A = extensionality helper'
  where
  helper : ∀ {Γ A B} (∋B : Γ , A ∋ B) → ext-subst {Γ} {Γ} {A} idₛ _ ∋B ≡ idₛ _ ∋B
  helper head = refl
  helper (tail ∋B) = refl

  helper' : ∀ {Γ A} (B : Type) → ext-subst {Γ} {Γ} {A} idₛ B ≡ idₛ {Γ , A} B
  helper' B = extensionality helper

infixr 9 _∘ₛ_
_∘ₛ_ : ∀ {Γ Δ Θ} → Subst Δ Θ → Subst Γ Δ → Subst Γ Θ
(σ ∘ₛ ρ) _ ∋A = subst ρ (σ _ ∋A)

idₛ-subst : ∀ {Γ} {A : Type} (M : Γ ⊢ A) → subst idₛ M ≡ M
idₛ-subst (` x) = refl
idₛ-subst {Γ} {A ⇒ B} (ƛ .A ⇒ M) rewrite ext-idₛ≡idₛ Γ A | idₛ-subst M = refl
idₛ-subst (M₁ ∙ M₂) rewrite idₛ-subst M₁ | idₛ-subst M₂ = refl
idₛ-subst `Z = refl
idₛ-subst (`S M) rewrite idₛ-subst M = refl
idₛ-subst {Γ} case M [Z⇒ M₁ |S⇒ M₂ ] rewrite idₛ-subst M
                                           | idₛ-subst M₁
                                           | ext-idₛ≡idₛ Γ `ℕ | idₛ-subst M₂ = refl
idₛ-subst {Γ} {A} (μ M) rewrite ext-idₛ≡idₛ Γ A | idₛ-subst M = refl

∘ₛ-identityʳ : ∀ {Γ Δ} {ρ : Subst Γ Δ} → ρ ∘ₛ idₛ ≡ ρ
∘ₛ-identityʳ {ρ = ρ} = extensionality (helper' ρ)
  where
  helper : ∀ {Γ Δ A} → (ρ : Subst Γ Δ) → (∋A : Δ ∋ A) → (ρ ∘ₛ idₛ) _ ∋A ≡ ρ _ ∋A
  helper ρ ∋A rewrite idₛ-subst (ρ _ ∋A) = refl

  helper' : ∀ {Γ Δ} → (ρ : Subst Γ Δ) → (A : Type) → (ρ ∘ₛ idₛ) A ≡ ρ A
  helper' ρ A = extensionality (helper ρ)

∘ₛ-assoc : ∀ {Γ Δ Θ Ξ} {ρ : Subst Γ Δ} {σ : Subst Δ Θ} {τ : Subst Θ Ξ} →
  τ ∘ₛ (σ ∘ₛ ρ) ≡ (τ ∘ₛ σ) ∘ₛ ρ
∘ₛ-assoc {Γ} {Δ} {Θ} {Ξ} {ρ} {σ} {τ} = {!!}
∘ₛ-assoc {Γ} {Δ} {Θ} {Ξ} {ρ} {σ} {τ} = {!!}

ContextCategory : Category lzero lzero lzero
ContextCategory = record
                    { Obj = Context
                    ; _⇒_ = Subst
                    ; _≈_ = _≡_
                    ; id = idₛ
                    ; _∘_ = _∘ₛ_
                    ; assoc = {!!}
                    ; sym-assoc = {!!}
                    ; identityˡ = refl
                    ; identityʳ = ∘ₛ-identityʳ
                    ; identity² = refl
                    ; equiv = Eq.isEquivalence
                    ; ∘-resp-≈ = λ{refl refl → refl}
                    }

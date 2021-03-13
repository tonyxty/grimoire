{-# OPTIONS --safe --without-K #-}
module Subst where

open import Terms hiding (module Rename)
open import Level using (0ℓ)
open import Function using (_∘_)
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong₂)

private
  variable
    Γ Δ Θ Ξ : Context
    A A' : Type

module Rename where
  open Terms.Rename
  renameVar-weaken : ∀ (ρ : Rename Γ Δ) (x : Δ ∋ A) → renameVar (Terms.Rename.weaken {A = A'} ρ) x ≡ suc (renameVar ρ x)
  renameVar-weaken (_ , _) zero = refl
  renameVar-weaken (ρ , _) (suc x) = renameVar-weaken ρ x

  renameVar-id : ∀ (x : Γ ∋ A) → renameVar idRename x ≡ x
  renameVar-id zero = refl
  renameVar-id (suc x) = trans (renameVar-weaken idRename x) (cong suc (renameVar-id x))

  rename-id : ∀ (M : Γ ⊢ A) → rename idRename M ≡ M
  rename-id (` x) rewrite renameVar-id x = refl
  rename-id (ƛ A ⇒ M) rewrite rename-id M = refl
  rename-id (M₁ ∙ M₂) rewrite rename-id M₁ | rename-id M₂ = refl
  rename-id Z = refl
  rename-id (S M) rewrite rename-id M = refl
  rename-id case M [Z⇒ M₁ |S⇒ M₂ ] rewrite rename-id M | rename-id M₁ | rename-id M₂ = refl
  rename-id ⟪ M₁ , M₂ ⟫ rewrite rename-id M₁ | rename-id M₂ = refl
  rename-id (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M') rewrite rename-id M | rename-id M' = refl
  rename-id (μ M) rewrite rename-id M = refl

substVar-weaken : ∀ (σ : Subst Γ Δ) (x : Δ ∋ A) → substVar (weaken {A = A'} σ) x ≡ substVar σ x ♯
substVar-weaken (_ , _) zero = refl
substVar-weaken (σ , _) (suc x) = substVar-weaken σ x

Var♯ : ∀ (x : Γ ∋ A) → (` x) ♯ A' ≡ ` suc x
Var♯ x = cong `_ (trans (renameVar-weaken Terms.Rename.idRename x) (cong suc (renameVar-id x))) where open Rename

substVar-id : ∀ (x : Γ ∋ A) → substVar idSubst x ≡ ` x
substVar-id zero = refl
substVar-id (suc x) = trans (substVar-weaken idSubst x) (trans (cong _♯ (substVar-id x)) (Var♯ x))

subst-id : ∀ (M : Γ ⊢ A) → subst idSubst M ≡ M
subst-id (` x) = substVar-id x
subst-id (ƛ A ⇒ M) rewrite subst-id M = refl
subst-id (M₁ ∙ M₂) rewrite subst-id M₁ | subst-id M₂ = refl
subst-id Z = refl
subst-id (S M) rewrite subst-id M = refl
subst-id case M [Z⇒ M₁ |S⇒ M₂ ] rewrite subst-id M | subst-id M₁ | subst-id M₂ = refl
subst-id ⟪ M₁ , M₂ ⟫ rewrite subst-id M₁ | subst-id M₂ = refl
subst-id (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M') rewrite subst-id M | subst-id M' = refl
subst-id (μ M) rewrite subst-id M = refl

-- substitutions are determined by their action on variables, and, via restriction, terms.
-- from the categorical point of view, this means the presheaf of terms is actually a faithful functor,
-- i.e., 𝑪^op is a concrete category where 𝑪 is the syntactic category.  it follows that 𝑪 is concrete, too.
-- this can greatly simplify the proof of identity and associativity laws.
subst-≡ : ∀ {ρ σ : Subst Γ Δ} → (∀ {A} (x : Δ ∋ A) → substVar ρ x ≡ substVar σ x) → ρ ≡ σ
subst-≡ {ρ = ∅} {σ = ∅} _ = refl
subst-≡ {ρ = ρ , M} {σ = σ , N} e = cong₂ _,_ (subst-≡ (e ∘ suc)) (e zero)

infixr 9 _∘ₛ_
_∘ₛ_ : Subst Δ Θ → Subst Γ Δ → Subst Γ Θ
∅ ∘ₛ _ = ∅
(ρ , M) ∘ₛ σ = ρ ∘ₛ σ , subst σ M

substVar-∘ₛ : ∀ (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (x : Θ ∋ A) → substVar (σ ∘ₛ ρ) x ≡ subst ρ (substVar σ x)
substVar-∘ₛ ρ (_ , _) zero = refl
substVar-∘ₛ ρ (σ , _) (suc x) = substVar-∘ₛ ρ σ x

subst-⋆-♯ : ∀ (σ : Subst Γ Δ) (M : Δ ⊢ A) (A' : Type) → subst (σ ⋆ A') (M ♯) ≡ (subst σ M) ♯
subst-⋆-♯ σ (` x) A' = trans (cong (subst (σ ⋆)) (Var♯ x)) (substVar-weaken σ x)
-- rewrite refuses to work here for some reason
subst-⋆-♯ σ (ƛ A ⇒ M) A' = {!!}
subst-⋆-♯ σ (M₁ ∙ M₂) A' rewrite subst-⋆-♯ σ M₁ A' | subst-⋆-♯ σ M₂ A' = refl
subst-⋆-♯ σ Z A' = refl
subst-⋆-♯ σ (S M) A' rewrite subst-⋆-♯ σ M A' = refl
subst-⋆-♯ σ case M [Z⇒ M₁ |S⇒ M₂ ] A' = {!!}
subst-⋆-♯ σ ⟪ M₁ , M₂ ⟫ A' = {!!}
subst-⋆-♯ σ case M [⟪,⟫⇒ M' ] A' = {!!}
subst-⋆-♯ σ (μ M) A' = {!!}

∘ₛ-⋆ : ∀ (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (A : Type) → (σ ∘ₛ ρ) ⋆ A ≡ σ ⋆ ∘ₛ ρ ⋆
∘ₛ-⋆ ρ σ A = cong (_, ` zero) (helper ρ σ A)
  where
  helper : ∀ (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (A : Type) → weaken (σ ∘ₛ ρ) ≡ weaken σ ∘ₛ (ρ ⋆ A)
  helper _ ∅ _ = refl
  helper ρ (σ , M) A = cong₂ _,_ (helper ρ σ A) (sym (subst-⋆-♯ ρ M A))

subst-∘ₛ : ∀ (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (M : Θ ⊢ A) → subst (σ ∘ₛ ρ) M ≡ subst ρ (subst σ M)
subst-∘ₛ ρ σ (` x) = substVar-∘ₛ ρ σ x
subst-∘ₛ ρ σ (ƛ A ⇒ M) rewrite ∘ₛ-⋆ ρ σ A | subst-∘ₛ (ρ ⋆) (σ ⋆) M = refl
subst-∘ₛ ρ σ (M₁ ∙ M₂) rewrite subst-∘ₛ ρ σ M₁ | subst-∘ₛ ρ σ M₂ = refl
subst-∘ₛ ρ σ Z = refl
subst-∘ₛ ρ σ (S M) rewrite subst-∘ₛ ρ σ M = refl
subst-∘ₛ ρ σ case M [Z⇒ M₁ |S⇒ M₂ ]
  rewrite subst-∘ₛ ρ σ M | subst-∘ₛ ρ σ M₁ | ∘ₛ-⋆ ρ σ `ℕ | subst-∘ₛ (ρ ⋆) (σ ⋆) M₂ = refl
subst-∘ₛ ρ σ ⟪ M₁ , M₂ ⟫ rewrite subst-∘ₛ ρ σ M₁ | subst-∘ₛ ρ σ M₂ = refl
subst-∘ₛ ρ σ case M [⟪,⟫⇒ M' ] = begin
    case subst (σ ∘ₛ ρ) M [⟪,⟫⇒ subst ((σ ∘ₛ ρ) ⋆ ⋆) M' ]
  ≡⟨ cong (λ N → case N [⟪,⟫⇒ subst ((σ ∘ₛ ρ) ⋆ ⋆) M' ]) (subst-∘ₛ ρ σ M) ⟩
    case subst ρ (subst σ M) [⟪,⟫⇒ subst ((σ ∘ₛ ρ) ⋆ ⋆) M' ]
  ≡⟨ cong (λ τ → case subst ρ (subst σ M) [⟪,⟫⇒ subst (τ ⋆) M' ]) (∘ₛ-⋆ ρ σ _) ⟩
    case subst ρ (subst σ M) [⟪,⟫⇒ subst ((σ ⋆ ∘ₛ ρ ⋆) ⋆) M' ]
  ≡⟨ cong (λ τ → case subst ρ (subst σ M) [⟪,⟫⇒ subst τ M' ]) (∘ₛ-⋆ (ρ ⋆) (σ ⋆) _) ⟩
    case subst ρ (subst σ M) [⟪,⟫⇒ subst ((σ ⋆ ⋆) ∘ₛ (ρ ⋆ ⋆)) M' ]
  ≡⟨ cong (λ N → case subst ρ (subst σ M) [⟪,⟫⇒ N ]) (subst-∘ₛ (ρ ⋆ ⋆) (σ ⋆ ⋆) M') ⟩
    case subst ρ (subst σ M) [⟪,⟫⇒ subst (ρ ⋆ ⋆) (subst (σ ⋆ ⋆) M') ]
  ∎ where open Eq.≡-Reasoning
  -- why, agda seems to be refusing to rewrite my terms again
subst-∘ₛ ρ σ (μ_ {A = A} M) rewrite ∘ₛ-⋆ ρ σ A | subst-∘ₛ (ρ ⋆) (σ ⋆) M = refl


∘ₛ-assoc : ∀ {ρ : Subst Γ Δ} {σ : Subst Δ Θ} {τ : Subst Θ Ξ} → (τ ∘ₛ σ) ∘ₛ ρ ≡ τ ∘ₛ σ ∘ₛ ρ
∘ₛ-assoc {ρ = ρ} {σ = σ} {τ = τ} = subst-≡ (helper ρ σ τ)
  where
  helper : ∀ (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (τ : Subst Θ Ξ) (x : Ξ ∋ A) →
    substVar ((τ ∘ₛ σ) ∘ₛ ρ) x ≡ substVar (τ ∘ₛ σ ∘ₛ ρ) x
  helper ρ σ τ x = begin
    substVar ((τ ∘ₛ σ) ∘ₛ ρ) x        ≡⟨ substVar-∘ₛ ρ (τ ∘ₛ σ) x ⟩
    subst ρ (substVar (τ ∘ₛ σ) x)     ≡⟨ cong (subst ρ) (substVar-∘ₛ σ τ x) ⟩
    subst ρ (subst σ (substVar τ x))  ≡⟨ sym (subst-∘ₛ ρ σ (substVar τ x)) ⟩
    subst (σ ∘ₛ ρ) (substVar τ x)     ≡⟨ sym (substVar-∘ₛ (σ ∘ₛ ρ) τ x) ⟩
    substVar (τ ∘ₛ σ ∘ₛ ρ) x
    ∎ where open Eq.≡-Reasoning

∘ₛ-identityˡ : ∀ {σ : Subst Γ Δ} → idSubst ∘ₛ σ ≡ σ
∘ₛ-identityˡ {σ = σ} = subst-≡ λ x → trans (substVar-∘ₛ σ idSubst x) (helper x)
  where
  helper : ∀ {σ : Subst Γ Δ} (x : Δ ∋ A) → subst σ (substVar idSubst x) ≡ substVar σ x
  helper x rewrite substVar-id x = refl

∘ₛ-identityʳ : ∀ {σ : Subst Γ Δ} → σ ∘ₛ idSubst ≡ σ
∘ₛ-identityʳ {σ = σ} = subst-≡ λ x → trans (substVar-∘ₛ idSubst σ x) (subst-id _)

-- a direct proof is also possible
∘ₛ-identityʳ' : ∀ {σ : Subst Γ Δ} → σ ∘ₛ idSubst ≡ σ
∘ₛ-identityʳ' {σ = ∅} = refl
∘ₛ-identityʳ' {σ = σ , M} = cong₂ _,_ ∘ₛ-identityʳ' (subst-id M)

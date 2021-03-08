{-# OPTIONS --without-K #-}
module Subst where

open import Terms hiding (module Rename)
open import Categories.Category.Core
open import Level using (0ℓ)
open import Function using (_∘_)
open import Data.Sum
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning

private
  variable
    Γ Δ Θ : Context
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

♯-suc : ∀ (x : Γ ∋ A) → (` x) ♯ A' ≡ ` suc x
♯-suc x = cong `_ (trans (renameVar-weaken Terms.Rename.idRename x) (cong suc (renameVar-id x))) where open Rename

substVar-id : ∀ (x : Γ ∋ A) → substVar idSubst x ≡ ` x
substVar-id zero = refl
substVar-id (suc x) = trans (substVar-weaken idSubst x) (trans (cong _♯ (substVar-id x)) (♯-suc x))

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

-- substitutions are determined by their action on variables
-- from the categorical point of view, this means the syntactic category is a concrete category
subst-≡ : ∀ (ρ σ : Subst Γ Δ) → (∀ {A} (x : Δ ∋ A) → substVar ρ x ≡ substVar σ x) → ρ ≡ σ
subst-≡ ∅ ∅ _ = refl
subst-≡ (ρ , M) (σ , N) e = cong₂ _,_ (subst-≡ ρ σ (e ∘ suc)) (e zero)

infixr 9 _∘ₛ_
_∘ₛ_ : Subst Δ Θ → Subst Γ Δ → Subst Γ Θ
∅ ∘ₛ ρ = ∅
(σ , M) ∘ₛ ρ = σ ∘ₛ ρ , subst ρ M

∘ₛ-identityʳ : ∀ {σ : Subst Γ Δ} → σ ∘ₛ idSubst ≡ σ
∘ₛ-identityʳ {σ = ∅} = refl
∘ₛ-identityʳ {σ = σ , M} = cong₂ _,_ ∘ₛ-identityʳ (subst-id M)

{-
_++_ : Context → Context → Context
Γ ++ ∅ = Γ
Γ ++ (E , A) = Γ ++ E , A

liftˡ : ∀ {Γ} (E : Context) → Rename (Γ ++ E) Γ
liftˡ ∅ x = x
liftˡ (E , _) x = tail (liftˡ E x)

liftʳ : ∀ {E} (Γ : Context) → Rename (Γ ++ E) E
liftʳ Γ head = head
liftʳ Γ (tail x) = tail (liftʳ Γ x)

++-∋ : ∀ {A} (Γ E : Context) (x : Γ ++ E ∋ A) → Σ[ x' ∈ (Γ ∋ A) ] (x ≡ liftˡ E x') ⊎ Σ[ x' ∈ (E ∋ A) ] (x ≡ liftʳ Γ x')
++-∋ Γ ∅ x = inj₁ (x , refl)
++-∋ Γ (_ , _) head = inj₂ (head , refl)
++-∋ Γ (E , _) (tail x) with ++-∋ Γ E x
...                        | inj₁ (x' , refl) = inj₁ (x' , refl)
...                        | inj₂ (x' , refl) = inj₂ (tail x' , refl)

++-∋-liftˡ : ∀ {A Γ E} (x : Γ ∋ A) → ++-∋ Γ E (liftˡ E x) ≡ inj₁ (x , refl)
++-∋-liftˡ {E = ∅} x = refl
++-∋-liftˡ {E = E , _} x rewrite ++-∋-liftˡ {E = E} x = refl

++-∋-liftʳ : ∀ {A Γ E} (x : E ∋ A) → ++-∋ Γ E (liftʳ Γ x) ≡ inj₂ (x , refl)
++-∋-liftʳ head = refl
++-∋-liftʳ {Γ = Γ} (tail x) rewrite ++-∋-liftʳ {Γ = Γ} x = refl

exts : ∀ {Γ Δ} → Rename Γ Δ → ∀ (E : Context) → Rename (Γ ++ E) (Δ ++ E)
exts ρ ∅ = ρ
exts ρ (E , A) = ext (exts ρ E)

infixl 10 _⋆⋆_
_⋆⋆_ : ∀ {Γ Δ} → Subst Γ Δ → ∀ (E : Context) → Subst (Γ ++ E) (Δ ++ E)
ρ ⋆⋆ ∅ = ρ
ρ ⋆⋆ (E , A) = (ρ ⋆⋆ E) ⋆ A

_⋆⋆ : ∀ {Γ Δ E} → Subst Γ Δ → Subst (Γ ++ E) (Δ ++ E)
ρ ⋆⋆ = ρ ⋆⋆ _

ext-subst-var : ∀ {Γ Δ E B} (ρ : Subst Γ Δ) (x : Δ ++ E ∋ B) (A : Type) →
  rename (exts tail E) ((ρ ⋆⋆ E) x) ≡ (ρ ⋆ A ⋆⋆ E) (exts tail E x)
ext-subst-var {Γ = Γ} {Δ = Δ} {E = E} ρ x A with ++-∋ Δ E x
... | inj₁ (x' , refl) = fromˡ ρ x' A
  where
  subst-liftˡ : ∀ {Γ Δ A} (ρ : Subst Γ Δ) (E : Context) (x : Δ ∋ A) → (ρ ⋆⋆ E) (liftˡ E x) ≡ rename (liftˡ E) (ρ x)
  subst-liftˡ ρ ∅ x = sym (rename-id (ρ x))
  subst-liftˡ ρ (E , A') x rewrite subst-liftˡ ρ E x
                                 | sym (rename-∘ (tail {B = A'}) (liftˡ E) (ρ x)) = refl

  exts-liftˡ : ∀ {Γ Δ A} (ρ : Rename Γ Δ) (E : Context) (x : Δ ∋ A) → exts ρ E (liftˡ E x) ≡ liftˡ E (ρ x)
  exts-liftˡ ρ ∅ x = refl
  exts-liftˡ ρ (E , A') head rewrite exts-liftˡ ρ E head = refl
  exts-liftˡ ρ (E , A') (tail x) rewrite exts-liftˡ ρ E (tail x) = refl

  fromˡ : ∀ {Γ Δ E B} (ρ : Subst Γ Δ) (x : Δ ∋ B) (A : Type) →
    rename (exts tail E) ((ρ ⋆⋆ E) (liftˡ E x)) ≡ (ρ ⋆ A ⋆⋆ E) (exts tail E (liftˡ E x))
  fromˡ {Γ = Γ} {E = E} ρ x A rewrite subst-liftˡ ρ E x
                                    | exts-liftˡ (tail {B = A}) E x
                                    | subst-liftˡ (ρ ⋆ A) E (tail x)
                                    | sym (rename-∘ (exts (tail {B = A}) E) (liftˡ E) (ρ x))
                                    | sym (rename-∘ (liftˡ E) (tail {B = A}) (ρ x))
    = cong (λ (σ : Rename ((Γ , A) ++ E) Γ) → rename σ (ρ x)) (rename-≡ (exts-liftˡ tail E))

... | inj₂ (x' , refl) = fromʳ ρ x' A
  where
  ⋆⋆-liftʳ : ∀ {Γ Δ A} (E : Context) (ρ : Subst Γ Δ) (x : E ∋ A) → (ρ ⋆⋆ E) (liftʳ Δ x) ≡ ` liftʳ Γ x
  ⋆⋆-liftʳ (E , A') ρ head = refl
  ⋆⋆-liftʳ (E , A') ρ (tail x) rewrite ⋆⋆-liftʳ E ρ x = refl

  exts-liftʳ : ∀ {A} (Γ E : Context) (x : E ∋ A) (B : Type) → exts (tail {B = B}) E (liftʳ Γ x) ≡ liftʳ (Γ , B) x
  exts-liftʳ Γ (_ , _) head B = refl
  exts-liftʳ Γ (E , _) (tail x) B rewrite exts-liftʳ Γ E x B = refl

  fromʳ : ∀ {Γ Δ E B} (ρ : Subst Γ Δ) (x : E ∋ B) (A : Type) →
    rename (exts tail E) ((ρ ⋆⋆ E) (liftʳ Δ x)) ≡ (ρ ⋆ A ⋆⋆ E) (exts tail E (liftʳ Δ x))
  fromʳ {Γ = Γ} {Δ = Δ} {E = E} ρ x A rewrite ⋆⋆-liftʳ _ ρ x
                                            | exts-liftʳ Δ E x A
                                            | exts-liftʳ Γ E x A
                                            | ⋆⋆-liftʳ E (ρ ⋆ A) x = refl

ext-subst : ∀ {Γ Δ B E} (ρ : Subst Γ Δ) (M : Δ ++ E ⊢ B) (A : Type) →
  rename (exts tail E) (subst (ρ ⋆⋆ E) M) ≡ subst (ρ ⋆ A ⋆⋆ E) (rename (exts tail E) M)
ext-subst ρ (` x) A = ext-subst-var ρ x A
ext-subst ρ (ƛ A' ⇒ M) A rewrite ext-subst ρ M A = refl
ext-subst ρ (M₁ ∙ M₂) A rewrite ext-subst ρ M₁ A
                      | ext-subst ρ M₂ A = refl
ext-subst ρ Z A = refl
ext-subst ρ (S M) A rewrite ext-subst ρ M A = refl
ext-subst ρ case M [Z⇒ M₁ |S⇒ M₂ ] A rewrite ext-subst ρ M A
                                           | ext-subst ρ M₁ A
                                           | ext-subst ρ M₂ A = refl
ext-subst ρ ⟪ M₁ , M₂ ⟫ A rewrite ext-subst ρ M₁ A
                                | ext-subst ρ M₂ A = refl
ext-subst ρ case M [⟪,⟫⇒ M' ] A rewrite ext-subst ρ M A
                                      | ext-subst ρ M' A = refl
ext-subst ρ (μ M) A rewrite ext-subst ρ M A = refl

⋆-distr-∘ₛ : ∀ {Γ Δ Θ} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (A : Type) → (σ ∘ₛ ρ) ⋆ A ≡ₛ (σ ⋆ A) ∘ₛ (ρ ⋆ A)
⋆-distr-∘ₛ ρ σ A = subst-≡ (pt≡ ρ σ A)
  where
  helper : ∀ {Γ Δ B} (ρ : Subst Γ Δ) (M : Δ ⊢ B) (A : Type) →
    rename tail (subst ρ M) ≡ subst (ρ ⋆ A) (rename tail M)
  helper ρ M A = ext-subst ρ M A

  pt≡ : ∀ {Γ Δ Θ} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (A : Type) {B} (x : Θ , A ∋ B) →
    ((σ ∘ₛ ρ) ⋆ A) x ≡ (σ ⋆ A ∘ₛ ρ ⋆ A) x
  pt≡ ρ σ A head = refl
  pt≡ ρ σ A (tail x) = helper _ (σ x) _

subst-∘ₛ : ∀ {Γ Δ Θ A} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (M : Θ ⊢ A) → subst ρ (subst σ M) ≡ subst (σ ∘ₛ ρ) M
subst-∘ₛ ρ σ (` x) = refl
subst-∘ₛ ρ σ (ƛ A ⇒ M) rewrite ⋆-distr-∘ₛ ρ σ A
                             | subst-∘ₛ (ρ ⋆) (σ ⋆) M = refl
subst-∘ₛ ρ σ (M₁ ∙ M₂) rewrite subst-∘ₛ ρ σ M₁
                             | subst-∘ₛ ρ σ M₂ = refl
subst-∘ₛ ρ σ Z = refl
subst-∘ₛ ρ σ (S M) rewrite subst-∘ₛ ρ σ M = refl
subst-∘ₛ ρ σ case M [Z⇒ M₁ |S⇒ M₂ ] rewrite subst-∘ₛ ρ σ M
                                          | subst-∘ₛ ρ σ M₁
                                          | ⋆-distr-∘ₛ ρ σ `ℕ
                                          | subst-∘ₛ (ρ ⋆) (σ ⋆) M₂ = refl
subst-∘ₛ ρ σ ⟪ M₁ , M₂ ⟫ rewrite subst-∘ₛ ρ σ M₁
                               | subst-∘ₛ ρ σ M₂ = refl
subst-∘ₛ ρ σ (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M') rewrite subst-∘ₛ ρ σ M
                                                           | ⋆-distr-∘ₛ ρ σ A₁
                                                           | ⋆-distr-∘ₛ (ρ ⋆ A₁) (σ ⋆ A₁) A₂
                                                           | subst-∘ₛ (ρ ⋆ ⋆) (σ ⋆ ⋆) M' = refl
subst-∘ₛ {A = A} ρ σ (μ M) rewrite ⋆-distr-∘ₛ ρ σ A
                                 | subst-∘ₛ (ρ ⋆) (σ ⋆) M = refl

∘ₛ-identityʳ : ∀ {Γ Δ} {ρ : Subst Γ Δ} → ρ ∘ₛ idSubst ≡ₛ ρ
∘ₛ-identityʳ {ρ = ρ} = subst-≡ (pt≡ ρ)
  where
  pt≡ : ∀ {Γ Δ A} (ρ : Subst Γ Δ) (x : Δ ∋ A) → (ρ ∘ₛ idSubst) x ≡ ρ x
  pt≡ ρ x rewrite subst-id (ρ x) = refl

∘ₛ-assoc : ∀ {Γ Δ Θ Ξ} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (τ : Subst Θ Ξ) → (τ ∘ₛ σ) ∘ₛ ρ ≡ₛ τ ∘ₛ (σ ∘ₛ ρ)
∘ₛ-assoc ρ σ τ = subst-≡ (λ x → subst-∘ₛ ρ σ (τ x))
-}

open Category

instance ContextCategory : Category 0ℓ 0ℓ 0ℓ
ContextCategory .Obj = Context
ContextCategory .Category._⇒_ = Subst
ContextCategory ._≈_ = _≡_
ContextCategory .id = idSubst
ContextCategory .Category._∘_ = _∘ₛ_
ContextCategory .assoc {h = h} = {!!} -- ∘ₛ-assoc _ _ h
ContextCategory .sym-assoc {h = h} = {!!} -- sym (∘ₛ-assoc _ _ h)
ContextCategory .identityˡ = {!!}
ContextCategory .identityʳ = ∘ₛ-identityʳ
ContextCategory .identity² = {!!}
ContextCategory .equiv = Eq.isEquivalence
ContextCategory .∘-resp-≈ refl refl = refl

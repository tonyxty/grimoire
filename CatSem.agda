{-# OPTIONS --without-K #-}
module CatSem where

open import Terms
open import Categories.Category.Core
open import Level
open import Function using (_∘_)
open import Data.Sum
open import Data.Product renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning

module _ {A : Set} {B : A → Set} where
  private F = ∀ {x} → B x
  postulate extensionality' : {f g : F} → (∀ (x : A) → f {x} ≡ g {x}) → _≡_ {A = F} f g

  extensionality : {f g : ∀ (x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g
  extensionality {f = f} {g = g} p = lemma (g _) (extensionality' p)
    where -- hacking the η-law in Agda tycker
    lemma : (g′ : F) → (λ {x} → f x) ≡ g′ → f ≡ (λ x → g′ {x})
    lemma _ p rewrite sym p = refl

rename-≡ : ∀ {Γ Δ} {ρ σ : Rename Γ Δ} → (∀ {A} (x : Δ ∋ A) → ρ x ≡ σ x) → _≡_ {A = Rename Γ Δ} ρ σ
rename-≡ {ρ = ρ} {σ = σ} pt≡ = extensionality' (λ A' → extensionality (pt≡ {A'}))

idᵣ : ∀ {Γ} → Rename Γ Γ
idᵣ x = x

ext-id≡id : ∀ (Γ : Context) (A : Type) → (λ {A'} (x : Γ , A ∋ A') → ext idᵣ x) ≡ (λ {A'} x → idᵣ x)
ext-id≡id Γ A = rename-≡ λ{head → refl; (tail x) → refl}

rename-id : ∀ {Γ A} (M : Γ ⊢ A) → rename idᵣ M ≡ M
rename-id (` x) = refl
rename-id {Γ = Γ} (ƛ A ⇒ M) rewrite ext-id≡id Γ A | rename-id M = refl
rename-id (M₁ ∙ M₂) rewrite rename-id M₁ | rename-id M₂ = refl
rename-id Z = refl
rename-id (S M) rewrite rename-id M = refl
rename-id {Γ = Γ} case M [Z⇒ M₁ |S⇒ M₂ ] rewrite rename-id M | rename-id M₁ | ext-id≡id Γ `ℕ | rename-id M₂ = refl
rename-id ⟪ M₁ , M₂ ⟫ rewrite rename-id M₁ | rename-id M₂ = refl
rename-id {Γ = Γ} (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M')
  rewrite rename-id M | ext-id≡id Γ A₁ | ext-id≡id (Γ , A₁) A₂ | rename-id M' = refl
rename-id {Γ} {A} (μ M) rewrite ext-id≡id Γ A | rename-id M = refl

ext-∘ : ∀ {Γ Δ Θ} (ρ : Rename Γ Δ) (σ : Rename Δ Θ) (A : Type) →
  (λ {B} (x : Θ , A ∋ B) → ext (ρ ∘ σ) x) ≡ (λ {B} x → ext ρ (ext σ x))
ext-∘ ρ σ A = rename-≡ (λ{head → refl; (tail x) → refl})

rename-∘ : ∀ {Γ Δ Θ A} (ρ : Rename Γ Δ) (σ : Rename Δ Θ) (M : Θ ⊢ A) → rename (ρ ∘ σ) M ≡ rename ρ (rename σ M)
rename-∘ ρ σ (` x) = refl
rename-∘ ρ σ (ƛ A ⇒ M) rewrite ext-∘ ρ σ A | rename-∘ (ext ρ) (ext σ) M = refl
rename-∘ ρ σ (M₁ ∙ M₂) rewrite rename-∘ ρ σ M₁ | rename-∘ ρ σ M₂ = refl
rename-∘ ρ σ Z = refl
rename-∘ ρ σ (S M) rewrite rename-∘ ρ σ M = refl
rename-∘ ρ σ case M [Z⇒ M₁ |S⇒ M₂ ] rewrite
  rename-∘ ρ σ M | rename-∘ ρ σ M₁ | ext-∘ ρ σ `ℕ | rename-∘ (ext ρ) (ext σ) M₂ = refl
rename-∘ ρ σ ⟪ M₁ , M₂ ⟫ rewrite rename-∘ ρ σ M₁ | rename-∘ ρ σ M₂ = refl
rename-∘ ρ σ (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M')
  rewrite rename-∘ ρ σ M | ext-∘ ρ σ A₁ | ext-∘ (ext {A = A₁} ρ) (ext σ) A₂ | rename-∘ (ext (ext ρ)) (ext (ext σ)) M'
  = refl
rename-∘ {A = A} ρ σ (μ M) rewrite ext-∘ ρ σ A | rename-∘ (ext ρ) (ext σ) M = refl

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
subst-idₛ {Γ = Γ} (ƛ A ⇒ M) rewrite idₛ♯≡idₛ Γ A | subst-idₛ M = refl
subst-idₛ (M₁ ∙ M₂) rewrite subst-idₛ M₁ | subst-idₛ M₂ = refl
subst-idₛ Z = refl
subst-idₛ (S M) rewrite subst-idₛ M = refl
subst-idₛ {Γ = Γ} case M [Z⇒ M₁ |S⇒ M₂ ] rewrite subst-idₛ M
                                               | subst-idₛ M₁
                                               | idₛ♯≡idₛ Γ `ℕ
                                               | subst-idₛ M₂ = refl
subst-idₛ ⟪ M₁ , M₂ ⟫ rewrite subst-idₛ M₁ | subst-idₛ M₂ = refl
subst-idₛ {Γ = Γ} (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M') rewrite subst-idₛ M
                                                                | idₛ♯≡idₛ Γ A₁
                                                                | idₛ♯≡idₛ (Γ , A₁) A₂
                                                                | subst-idₛ M' = refl
subst-idₛ {Γ} {A} (μ M) rewrite idₛ♯≡idₛ Γ A | subst-idₛ M = refl

infixr 9 _∘ₛ_
_∘ₛ_ : ∀ {Γ Δ Θ} → Subst Δ Θ → Subst Γ Δ → Subst Γ Θ
(σ ∘ₛ ρ) _ ∋A = subst ρ (σ _ ∋A)

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
++-∋ Γ ∅ x = inj₁ ⟨ x , refl ⟩
++-∋ Γ (_ , _) head = inj₂ ⟨ head , refl ⟩
++-∋ Γ (E , _) (tail x) with ++-∋ Γ E x
...                        | inj₁ ⟨ x' , refl ⟩ = inj₁ ⟨ x' , refl ⟩
...                        | inj₂ ⟨ x' , refl ⟩ = inj₂ ⟨ tail x' , refl ⟩

extRename : ∀ {Γ Δ} → Rename Γ Δ → ∀ (E : Context) → Rename (Γ ++ E) (Δ ++ E)
extRename ρ ∅ = ρ
extRename ρ (E , A) = ext (extRename ρ E)

infixl 10 _⋆⋆_
_⋆⋆_ : ∀ {Γ Δ} → Subst Γ Δ → ∀ (E : Context) → Subst (Γ ++ E) (Δ ++ E)
ρ ⋆⋆ ∅ = ρ
ρ ⋆⋆ (E , A) = (ρ ⋆⋆ E) ⋆ A

ext-subst-comm-var : ∀ {Γ Δ E B} (ρ : Subst Γ Δ) (x : Δ ++ E ∋ B) (A : Type) →
  rename (extRename tail E) ((ρ ⋆⋆ E) _ x) ≡ (ρ ⋆ A ⋆⋆ E) _ (extRename tail E x)
ext-subst-comm-var {Γ = Γ} {Δ = Δ} {E = E} ρ x A with ++-∋ Δ E x
... | inj₁ ⟨ x' , refl ⟩ = fromˡ ρ x' A
  where
  subst-liftˡ : ∀ {Γ Δ A} (ρ : Subst Γ Δ) (E : Context) (x : Δ ∋ A) → (ρ ⋆⋆ E) _ (liftˡ E x) ≡ rename (liftˡ E) (ρ _ x)
  subst-liftˡ ρ ∅ x = sym (rename-id (ρ _ x))
  subst-liftˡ ρ (E , A') x rewrite subst-liftˡ ρ E x | sym (rename-∘ (tail {B = A'}) (liftˡ E) (ρ _ x)) = refl

  extRename-liftˡ : ∀ {Γ Δ A} (ρ : Rename Γ Δ) (E : Context) (x : Δ ∋ A) → extRename ρ E (liftˡ E x) ≡ liftˡ E (ρ x)
  extRename-liftˡ ρ ∅ x = refl
  extRename-liftˡ ρ (E , A') head rewrite extRename-liftˡ ρ E head = refl
  extRename-liftˡ ρ (E , A') (tail x) rewrite extRename-liftˡ ρ E (tail x) = refl

  fromˡ : ∀ {Γ Δ E B} (ρ : Subst Γ Δ) (x : Δ ∋ B) (A : Type) →
    rename (extRename tail E) ((ρ ⋆⋆ E) _ (liftˡ E x)) ≡ (ρ ⋆ A ⋆⋆ E) _ (extRename tail E (liftˡ E x))
  fromˡ {Γ = Γ} {E = E} ρ x A rewrite
    subst-liftˡ ρ E x | extRename-liftˡ (tail {B = A}) E x | subst-liftˡ (ρ ⋆ A) E (tail x) |
    sym (rename-∘ (extRename (tail {B = A}) E) (liftˡ E) (ρ _ x)) | sym (rename-∘ (liftˡ E) (tail {B = A}) (ρ _ x))
    = cong (λ (σ : Rename ((Γ , A) ++ E) Γ) → rename σ (ρ _ x)) (rename-≡ (extRename-liftˡ tail E))

... | inj₂ ⟨ x' , refl ⟩ = fromʳ ρ x' A
  where
  ⋆⋆-liftʳ : ∀ {Γ Δ A} (E : Context) (ρ : Subst Γ Δ) (x : E ∋ A) → (ρ ⋆⋆ E) _ (liftʳ Δ x) ≡ ` liftʳ Γ x
  ⋆⋆-liftʳ (E , A') ρ head = refl
  ⋆⋆-liftʳ (E , A') ρ (tail x) rewrite ⋆⋆-liftʳ E ρ x = refl

  extRename-liftʳ : ∀ {A} (Γ E : Context) (x : E ∋ A) (B : Type) → extRename (tail {B = B}) E (liftʳ Γ x) ≡ liftʳ (Γ , B) x
  extRename-liftʳ Γ (_ , _) head B = refl
  extRename-liftʳ Γ (E , _) (tail x) B rewrite extRename-liftʳ Γ E x B = refl

  fromʳ : ∀ {Γ Δ E B} (ρ : Subst Γ Δ) (x : E ∋ B) (A : Type) →
    rename (extRename tail E) ((ρ ⋆⋆ E) _ (liftʳ Δ x)) ≡ (ρ ⋆ A ⋆⋆ E) _ (extRename tail E (liftʳ Δ x))
  fromʳ {Γ = Γ} {Δ = Δ} {E = E} ρ x A rewrite ⋆⋆-liftʳ _ ρ x | extRename-liftʳ Δ E x A
                                            | extRename-liftʳ Γ E x A | ⋆⋆-liftʳ E (ρ ⋆ A) x = refl


ext-subst-comm : ∀ {Γ Δ B E} (ρ : Subst Γ Δ) (M : Δ ++ E ⊢ B) (A : Type) →
  rename (extRename tail E) (subst (ρ ⋆⋆ E) M) ≡ subst (ρ ⋆ A ⋆⋆ E) (rename (extRename tail E) M)
ext-subst-comm ρ (` x) A = ext-subst-comm-var ρ x A
ext-subst-comm ρ (ƛ A' ⇒ M) A rewrite ext-subst-comm ρ M A = refl
ext-subst-comm ρ (M₁ ∙ M₂) A rewrite ext-subst-comm ρ M₁ A | ext-subst-comm ρ M₂ A = refl
ext-subst-comm ρ Z A = refl
ext-subst-comm ρ (S M) A rewrite ext-subst-comm ρ M A = refl
ext-subst-comm ρ case M [Z⇒ M₁ |S⇒ M₂ ] A rewrite ext-subst-comm ρ M A | ext-subst-comm ρ M₁ A | ext-subst-comm ρ M₂ A = refl
ext-subst-comm ρ ⟪ M₁ , M₂ ⟫ A rewrite ext-subst-comm ρ M₁ A | ext-subst-comm ρ M₂ A = refl
ext-subst-comm ρ case M [⟪,⟫⇒ M' ] A rewrite ext-subst-comm ρ M A | ext-subst-comm ρ M' A = refl
ext-subst-comm ρ (μ M) A rewrite ext-subst-comm ρ M A = refl

⋆-distr-∘ₛ : ∀ {Γ Δ Θ} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (A : Type) → (σ ∘ₛ ρ) ⋆ A ≡ (σ ⋆ A) ∘ₛ (ρ ⋆ A)
⋆-distr-∘ₛ ρ σ A = subst-≡ (pt≡ ρ σ A)
  where
  helper : ∀ {Γ Δ B} (ρ : Subst Γ Δ) (M : Δ ⊢ B) (A : Type) → rename tail (subst ρ M) ≡ subst (ρ ⋆ A) (rename tail M)
  helper ρ M A = ext-subst-comm ρ M A

  pt≡ : ∀ {Γ Δ Θ} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (A : Type) {B} (∋B : Θ , A ∋ B) →
    ((σ ∘ₛ ρ) ⋆ A) _ ∋B ≡ (σ ⋆ A ∘ₛ ρ ⋆ A) _ ∋B
  pt≡ ρ σ A head = refl
  pt≡ ρ σ A (tail ∋B) = helper _ (σ _ ∋B) _

subst-∘ₛ : ∀ {Γ Δ Θ A} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (M : Θ ⊢ A) → subst ρ (subst σ M) ≡ subst (σ ∘ₛ ρ) M
subst-∘ₛ ρ σ (` x) = refl
subst-∘ₛ ρ σ (ƛ A ⇒ M) rewrite ⋆-distr-∘ₛ ρ σ A | subst-∘ₛ (ρ ♯) (σ ♯) M = refl
subst-∘ₛ ρ σ (M₁ ∙ M₂) rewrite subst-∘ₛ ρ σ M₁ | subst-∘ₛ ρ σ M₂ = refl
subst-∘ₛ ρ σ Z = refl
subst-∘ₛ ρ σ (S M) rewrite subst-∘ₛ ρ σ M = refl
subst-∘ₛ ρ σ case M [Z⇒ M₁ |S⇒ M₂ ] rewrite subst-∘ₛ ρ σ M
                                          | subst-∘ₛ ρ σ M₁
                                          | ⋆-distr-∘ₛ ρ σ `ℕ
                                          | subst-∘ₛ (ρ ♯) (σ ♯) M₂ = refl
subst-∘ₛ ρ σ ⟪ M₁ , M₂ ⟫ rewrite subst-∘ₛ ρ σ M₁ | subst-∘ₛ ρ σ M₂ = refl
subst-∘ₛ ρ σ (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M') rewrite subst-∘ₛ ρ σ M
                                                           | ⋆-distr-∘ₛ ρ σ A₁
                                                           | ⋆-distr-∘ₛ (ρ ⋆ A₁) (σ ⋆ A₁) A₂
                                                           | subst-∘ₛ (ρ ♯ ♯) (σ ♯ ♯) M' = refl
subst-∘ₛ {A = A} ρ σ (μ M) rewrite ⋆-distr-∘ₛ ρ σ A | subst-∘ₛ (ρ ♯) (σ ♯) M = refl

∘ₛ-identityʳ : ∀ {Γ Δ} {ρ : Subst Γ Δ} → ρ ∘ₛ idₛ ≡ ρ
∘ₛ-identityʳ {ρ = ρ} = subst-≡ (pt≡ ρ)
  where
  pt≡ : ∀ {Γ Δ A} (ρ : Subst Γ Δ) (∋A : Δ ∋ A) → (ρ ∘ₛ idₛ) _ ∋A ≡ ρ _ ∋A
  pt≡ ρ ∋A rewrite subst-idₛ (ρ _ ∋A) = refl

∘ₛ-assoc : ∀ {Γ Δ Θ Ξ} (ρ : Subst Γ Δ) (σ : Subst Δ Θ) (τ : Subst Θ Ξ) → (τ ∘ₛ σ) ∘ₛ ρ ≡ τ ∘ₛ (σ ∘ₛ ρ)
∘ₛ-assoc ρ σ τ = subst-≡ (λ ∋A → subst-∘ₛ ρ σ (τ _ ∋A))

open Category renaming (_⇒_ to _C⇒_; _∘_ to _∘c_)

instance ContextCategory : Category 0ℓ 0ℓ 0ℓ
ContextCategory .Obj = Context
ContextCategory ._C⇒_ = Subst
ContextCategory ._≈_ = _≡_
ContextCategory .id = idₛ
ContextCategory ._∘c_ = _∘ₛ_
ContextCategory .assoc {h = h} = ∘ₛ-assoc _ _ h
ContextCategory .sym-assoc {h = h} = sym (∘ₛ-assoc _ _ h)
ContextCategory .identityˡ = refl
ContextCategory .identityʳ = ∘ₛ-identityʳ
ContextCategory .identity² = refl
ContextCategory .equiv = Eq.isEquivalence
ContextCategory .∘-resp-≈ refl refl = refl

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

-- I think Agda's implicit insertion mechanism is too eager.
-- If we just write ρ ≡ σ here, the implicit type argument will be inserted, which is arguably counter-intuitive.
rename-≡ : ∀ {Γ Δ} {ρ σ : Rename Γ Δ} → (∀ {A} (x : Δ ∋ A) → ρ x ≡ σ x) → _≡_ {A = Rename Γ Δ} ρ σ
rename-≡ pt≡ = extensionality' (λ A' → extensionality (pt≡ {A'}))

idRename : ∀ {Γ} → Rename Γ Γ
idRename x = x

ext-idRename : ∀ (Γ : Context) (A : Type) → (λ {A'} (x : Γ , A ∋ A') → ext idRename x) ≡ (λ {A'} x → idRename x)
ext-idRename Γ A = rename-≡ λ{head → refl; (tail x) → refl}

rename-id : ∀ {Γ A} (M : Γ ⊢ A) → rename idRename M ≡ M
rename-id (` x) = refl
rename-id {Γ = Γ} (ƛ A ⇒ M) rewrite ext-idRename Γ A
                                    | rename-id M = refl
rename-id (M₁ ∙ M₂) rewrite rename-id M₁
                          | rename-id M₂ = refl
rename-id Z = refl
rename-id (S M) rewrite rename-id M = refl
rename-id {Γ = Γ} case M [Z⇒ M₁ |S⇒ M₂ ] rewrite rename-id M
                                               | rename-id M₁
                                               | ext-idRename Γ `ℕ
                                               | rename-id M₂ = refl
rename-id ⟪ M₁ , M₂ ⟫ rewrite rename-id M₁
                            | rename-id M₂ = refl
rename-id {Γ = Γ} (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M') rewrite rename-id M
                                                                | ext-idRename Γ A₁
                                                                | ext-idRename (Γ , A₁) A₂
                                                                | rename-id M' = refl
rename-id {Γ} {A} (μ M) rewrite ext-idRename Γ A
                              | rename-id M = refl

ext-∘ : ∀ {Γ Δ Θ} (ρ : Rename Γ Δ) (σ : Rename Δ Θ) (A : Type) →
  (λ {B} (x : Θ , A ∋ B) → ext (ρ ∘ σ) x) ≡ (λ {B} x → ext ρ (ext σ x))
ext-∘ ρ σ A = rename-≡ (λ{head → refl; (tail x) → refl})

rename-∘ : ∀ {Γ Δ Θ A} (ρ : Rename Γ Δ) (σ : Rename Δ Θ) (M : Θ ⊢ A) → rename (ρ ∘ σ) M ≡ rename ρ (rename σ M)
rename-∘ ρ σ (` x) = refl
rename-∘ ρ σ (ƛ A ⇒ M) rewrite ext-∘ ρ σ A
                             | rename-∘ (ext ρ) (ext σ) M = refl
rename-∘ ρ σ (M₁ ∙ M₂) rewrite rename-∘ ρ σ M₁
                             | rename-∘ ρ σ M₂ = refl
rename-∘ ρ σ Z = refl
rename-∘ ρ σ (S M) rewrite rename-∘ ρ σ M = refl
rename-∘ ρ σ case M [Z⇒ M₁ |S⇒ M₂ ] rewrite rename-∘ ρ σ M
                                          | rename-∘ ρ σ M₁
                                          | ext-∘ ρ σ `ℕ
                                          | rename-∘ (ext ρ) (ext σ) M₂ = refl
rename-∘ ρ σ ⟪ M₁ , M₂ ⟫ rewrite rename-∘ ρ σ M₁
                               | rename-∘ ρ σ M₂ = refl
rename-∘ ρ σ (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M') rewrite rename-∘ ρ σ M
                                                           | ext-∘ ρ σ A₁
                                                           | ext-∘ (ext {A = A₁} ρ) (ext σ) A₂
                                                           | rename-∘ (ext (ext ρ)) (ext (ext σ)) M' = refl
rename-∘ {A = A} ρ σ (μ M) rewrite ext-∘ ρ σ A
                                 | rename-∘ (ext ρ) (ext σ) M = refl

infix 4 _≡ₛ_
_≡ₛ_ : ∀ {Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
ρ ≡ₛ σ = _≡_ {A = Subst _ _} ρ σ

subst-≡ : ∀ {Γ Δ} {ρ σ : Subst Γ Δ} → (∀ {A} (x : Δ ∋ A) → ρ x ≡ σ x) → ρ ≡ₛ σ
subst-≡ pt≡ = extensionality' (λ A → extensionality (pt≡ {A}))

idSubst : ∀ {Γ} → Subst Γ Γ
idSubst x = ` x

idSubst⋆ : ∀ (Γ : Context) (A : Type) → idSubst {Γ} ⋆ A ≡ₛ idSubst
idSubst⋆ Γ A = subst-≡ λ{head → refl; (tail x) → refl}

subst-id : ∀ {Γ} {A : Type} (M : Γ ⊢ A) → subst idSubst M ≡ M
subst-id (` x) = refl
subst-id {Γ = Γ} (ƛ A ⇒ M) rewrite idSubst⋆ Γ A
                                 | subst-id M = refl
subst-id (M₁ ∙ M₂) rewrite subst-id M₁
                         | subst-id M₂ = refl
subst-id Z = refl
subst-id (S M) rewrite subst-id M = refl
subst-id {Γ = Γ} case M [Z⇒ M₁ |S⇒ M₂ ] rewrite subst-id M
                                              | subst-id M₁
                                              | idSubst⋆ Γ `ℕ
                                              | subst-id M₂ = refl
subst-id ⟪ M₁ , M₂ ⟫ rewrite subst-id M₁
                           | subst-id M₂ = refl
subst-id {Γ = Γ} (case_[⟪,⟫⇒_] {A₁ = A₁} {A₂ = A₂} M M') rewrite subst-id M
                                                                 | idSubst⋆ Γ A₁
                                                                 | idSubst⋆ (Γ , A₁) A₂
                                                                 | subst-id M' = refl
subst-id {Γ} {A} (μ M) rewrite idSubst⋆ Γ A | subst-id M = refl

infixr 9 _∘ₛ_
_∘ₛ_ : ∀ {Γ Δ Θ} → Subst Δ Θ → Subst Γ Δ → Subst Γ Θ
(σ ∘ₛ ρ) x = subst ρ (σ x)

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

++-∋-liftˡ : ∀ {A Γ E} (x : Γ ∋ A) → ++-∋ Γ E (liftˡ E x) ≡ inj₁ ⟨ x , refl ⟩
++-∋-liftˡ {E = ∅} x = refl
++-∋-liftˡ {E = E , _} x rewrite ++-∋-liftˡ {E = E} x = refl

++-∋-liftʳ : ∀ {A Γ E} (x : E ∋ A) → ++-∋ Γ E (liftʳ Γ x) ≡ inj₂ ⟨ x , refl ⟩
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
... | inj₁ ⟨ x' , refl ⟩ = fromˡ ρ x' A
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

... | inj₂ ⟨ x' , refl ⟩ = fromʳ ρ x' A
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

open Category renaming (_⇒_ to _C⇒_; _∘_ to _∘c_)

instance ContextCategory : Category 0ℓ 0ℓ 0ℓ
ContextCategory .Obj = Context
ContextCategory ._C⇒_ = Subst
ContextCategory ._≈_ = _≡_
ContextCategory .id = idSubst
ContextCategory ._∘c_ = _∘ₛ_
ContextCategory .assoc {h = h} = ∘ₛ-assoc _ _ h
ContextCategory .sym-assoc {h = h} = sym (∘ₛ-assoc _ _ h)
ContextCategory .identityˡ = refl
ContextCategory .identityʳ = ∘ₛ-identityʳ
ContextCategory .identity² = refl
ContextCategory .equiv = Eq.isEquivalence
ContextCategory .∘-resp-≈ refl refl = refl

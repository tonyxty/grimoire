{-# OPTIONS --without-K #-}
module MoreCat where

open import CatSem
open import Terms
open import Categories.Object.Terminal ContextCategory
open import Categories.Object.Product ContextCategory
open import Categories.Morphism ContextCategory
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

∅-isTerminal : IsTerminal ∅
∅-isTerminal = record { ! = λ () ; !-unique = λ f → subst-≡ λ () }

module _ {Γ Δ : Context} where
  combine : ∀ {Θ} → Subst Θ Γ → Subst Θ Δ → Subst Θ (Γ ++ Δ)
  combine ρ σ x with ++-∋ Γ Δ x
  ...              | inj₁ ⟨ x' , refl ⟩ = ρ x'
  ...              | inj₂ ⟨ x' , refl ⟩ = σ x'

  combine-liftˡ : ∀ {Θ A} {ρ : Subst Θ Γ} {σ : Subst Θ Δ} (x : Γ ∋ A) → combine ρ σ (liftˡ Δ x) ≡ ρ x
  combine-liftˡ x rewrite ++-∋-liftˡ {E = Δ} x = refl

  combine-liftʳ : ∀ {Θ A} {ρ : Subst Θ Γ} {σ : Subst Θ Δ} (x : Δ ∋ A) → combine ρ σ (liftʳ Γ x) ≡ σ x
  combine-liftʳ x rewrite ++-∋-liftʳ {Γ = Γ} x = refl

  combine-proj : ∀ {Θ A} {ρ : Subst Θ Γ} {σ : Subst Θ Δ} {ρσ : Subst Θ (Γ ++ Δ)} →
    ρ ≡ₛ (λ x → ` liftˡ Δ x) ∘ₛ ρσ → σ ≡ₛ (λ x → ` liftʳ Γ x) ∘ₛ ρσ → ∀ (x : Γ ++ Δ ∋ A) → ρσ x ≡ combine ρ σ x
  combine-proj e₁ e₂ rewrite e₁ | e₂ = helper
    where
    helper : ∀ {Θ A} {ρσ : Subst Θ (Γ ++ Δ)} (x : Γ ++ Δ ∋ A) →
      ρσ x ≡ combine (λ x → ρσ (liftˡ Δ x)) (λ x → ρσ (liftʳ Γ x)) x
    helper x with ++-∋ Γ Δ x
    ...         | inj₁ ⟨ x' , refl ⟩ = refl
    ...         | inj₂ ⟨ x' , refl ⟩ = refl

  ++-Product : Product Γ Δ
  ++-Product = record
                 { A×B = Γ ++ Δ
                 ; π₁ = λ x → ` liftˡ Δ x
                 ; π₂ = λ x → ` liftʳ Γ x
                 ; ⟨_,_⟩ = combine
                 ; project₁ = subst-≡ combine-liftˡ
                 ; project₂ = subst-≡ combine-liftʳ
                 ; unique = λ e₁ e₂ → subst-≡ λ x → sym (combine-proj (sym e₁) (sym e₂) x)
                 }

module _ {A B : Type} where
  ⊗≅, : (∅ , A , B) ≅ (∅ , A ⊗ B)
  ⊗≅, = record
          { from = λ{head → ⟪ # 1 , # 0 ⟫}
          ; to = λ{head → case # 0 [⟪,⟫⇒ # 0 ]; (tail head) → case # 0 [⟪,⟫⇒ # 1 ]}
          ; iso = record
                    { isoˡ = subst-≡ λ{head → {!!}; (tail head) → {!!}}
                    ; isoʳ = {!!} }
          }

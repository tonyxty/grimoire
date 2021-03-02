{-# OPTIONS --without-K #-}
module MoreCat where

open import CatSem
open import Terms
open import Categories.Object.Terminal
open import Categories.Object.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

∅-isTerminal : IsTerminal ContextCategory ∅
∅-isTerminal = record { ! = λ () ; !-unique = λ f → subst-≡ λ () }

,-Product : ∀ (A B : Type) → Product ContextCategory (∅ , A) (∅ , B)
,-Product = λ A B → record
                      { A×B = ∅ , A , B
                      ; π₁ = λ{head → ` tail head}
                      ; π₂ = λ{head → ` head}
                      ; ⟨_,_⟩ = λ ρ σ → λ{head → σ head; (tail head) → ρ head}
                      ; project₁ = subst-≡ λ{head → refl}
                      ; project₂ = subst-≡ λ{head → refl}
                      ; unique = λ ≡₁ ≡₂ → subst-≡ (λ{head → cong (λ f → f head) (sym ≡₂)
                                                   ; (tail head) → cong (λ f → f head) (sym ≡₁)})
                      }

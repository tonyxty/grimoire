open import Data.Maybe
open import Data.Nat
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infixr 2 _⇒_
data Type : Set where
  `ℕ : Type
  _⇒_ : Type → Type → Type

infixr 1 _,_
data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

infix 0 _∋_
data _∋_ : Context → Type → Set where
  head : ∀ {Γ A} → Γ , A ∋ A
  tail : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

infix 0 _⊢_
infix 5 `_
infix 2 ƛ_⇒_
infixl 3 _∙_
infix 4 `S
infix 2 μ_
data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  ƛ_⇒_ : ∀ {Γ B} (A : Type) → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _∙_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  `Z : ∀ {Γ} → Γ ⊢ `ℕ
  `S : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case_[Z⇒_|S⇒_] : ∀ {Γ A} → Γ ⊢ `ℕ → Γ ⊢ A → Γ , `ℕ ⊢ A → Γ ⊢ A
  μ_ : ∀ {Γ A} → Γ , A ⊢ A → Γ ⊢ A
  -- Note that μ without termination check breaks soundness

length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ)

at : (Γ : Context) → (i : ℕ) → (i<len : i < length Γ) → Type
at (_ , A) zero i<len = A
at (Γ , x) (suc i) (s≤s i<len) = at Γ i i<len

lookup : (Γ : Context) → (i : ℕ) → (i<len : i < length Γ) → Γ ∋ (at Γ i i<len)
lookup (_ , _) zero _ = head
lookup (Γ , _) (suc i) (s≤s i<len) = tail (lookup Γ i i<len)

# : ∀ (i : ℕ) → {Γ : Context} → {i<len : True (i <? length Γ)} → Γ ⊢ at Γ i (toWitness i<len)
# i {Γ} {i<len} = ` lookup Γ i (toWitness i<len)

-- Examples

`one : ∀ {Γ} → Γ ⊢ `ℕ
`one = `S `Z

`two : ∀ {Γ} → Γ ⊢ `ℕ
`two = `S (`S `Z)

`suc : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
`suc = ƛ `ℕ ⇒ `S (# 0)

`plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
`plus = μ (ƛ `ℕ ⇒ ƛ `ℕ ⇒
           case # 1
           [Z⇒ # 0
           |S⇒ `S (# 3 ∙ # 0 ∙ # 1) ])

-- Substitution

Rename : Context → Context → Set
Rename Γ Δ = ∀ {A : Type} → Δ ∋ A → Γ ∋ A

ext : ∀ {Γ Δ} → Rename Γ Δ → ∀ {A} → Rename (Γ , A) (Δ , A)
ext ρ head = head
ext ρ (tail x) = tail (ρ x)

-- note how this is contravariant
rename : ∀ {Γ Δ} → Rename Γ Δ → ∀ {A} → Δ ⊢ A → Γ ⊢ A
rename ρ (` x) = ` ρ x
rename ρ (ƛ A ⇒ M) = ƛ A ⇒ rename (ext ρ) M
rename ρ (M₁ ∙ M₂) = rename ρ M₁ ∙ rename ρ M₂
rename ρ `Z = `Z
rename ρ (`S M) = `S (rename ρ M)
rename ρ case M [Z⇒ N₁ |S⇒ N₂ ] = case rename ρ M [Z⇒ rename ρ N₁ |S⇒ rename (ext ρ) N₂ ]
rename ρ (μ M) = μ rename (ext ρ) M

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A : Type} → Δ ∋ A → Γ ⊢ A

ext-subst : ∀ {Γ Δ} → Subst Γ Δ → ∀ {A} → Subst (Γ , A) (Δ , A)
ext-subst σ head = ` head
ext-subst σ (tail x) = rename tail (σ x)

ext-term : ∀ {Γ A} → Γ ⊢ A → Subst Γ (Γ , A)
ext-term M head = M
ext-term M (tail ∋A) = ` ∋A

subst : ∀ {Γ Δ} → Subst Γ Δ → ∀ {A} → Δ ⊢ A → Γ ⊢ A
subst σ (` x) = σ x
subst σ (ƛ A ⇒ M) = ƛ A ⇒ (subst (ext-subst σ) M)
subst σ (M₁ ∙ M₂) = subst σ M₁ ∙ subst σ M₂
subst σ `Z = `Z
subst σ (`S M) = `S (subst σ M)
subst σ case M [Z⇒ N₁ |S⇒ N₂ ] = case subst σ M [Z⇒ subst σ N₁ |S⇒ subst (ext-subst σ) N₂ ]
subst σ (μ M) = μ subst (ext-subst σ) M

_[_] : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
_[_] M N = subst (ext-term N) M

-- Reduction

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {Γ A B} → {M : Γ , A ⊢ B} → Value (ƛ A ⇒ M)
  V-Z : ∀ {Γ} → Value (`Z {Γ})
  V-S : ∀ {Γ} → {V : Γ ⊢ `ℕ} → Value V → Value (`S V)

infix 0 _—→_
data _—→_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where
  ξ-∙₁ : ∀ {Γ A B} → {M M' : Γ ⊢ A ⇒ B} → {N : Γ ⊢ A} → M —→ M' → M ∙ N —→ M' ∙ N
  ξ-∙₂ : ∀ {Γ A B} → {V : Γ ⊢ A ⇒ B} → {N N' : Γ ⊢ A} → Value V → N —→ N' → V ∙ N —→ V ∙ N'
  β-ƛ : ∀ {Γ A B} → {M : Γ , A ⊢ B} → {V : Γ ⊢ A} → Value V → (ƛ A ⇒ M) ∙ V —→ M [ V ]
  ξ-S : ∀ {Γ} → {M M' : Γ ⊢ `ℕ} → M —→ M' → (`S M) —→ (`S M')
  ξ-case : ∀ {Γ A} → {M M' : Γ ⊢ `ℕ} → {N₁ : Γ ⊢ A} → {N₂ : Γ , `ℕ ⊢ A} → M —→ M' →
    case M [Z⇒ N₁ |S⇒ N₂ ] —→ case M' [Z⇒ N₁ |S⇒ N₂ ]
  β-Z : ∀ {Γ A} → {N₁ : Γ ⊢ A} → {N₂ : Γ , `ℕ ⊢ A} → case `Z [Z⇒ N₁ |S⇒ N₂ ] —→ N₁
  β-S : ∀ {Γ A} → {V : Γ ⊢ `ℕ} → {N₁ : Γ ⊢ A} → {N₂ : Γ , `ℕ ⊢ A} → Value V → case `S V [Z⇒ N₁ |S⇒ N₂ ] —→ N₂ [ V ]
  β-μ : ∀ {Γ A} → {M : Γ , A ⊢ A} → μ M —→ M [ μ M ]

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
    (ƛ `ℕ ⇒ ƛ `ℕ ⇒ case # 1 [Z⇒ # 0 |S⇒ `S (`plus ∙ # 0 ∙ # 1) ]) ∙ `one ∙ `one
  —→⟨ ξ-∙₁ (β-ƛ (V-S V-Z)) ⟩
    (ƛ `ℕ ⇒ case `one [Z⇒ # 0 |S⇒ `S (`plus ∙ # 0 ∙ # 1) ]) ∙ `one
  —→⟨ β-ƛ (V-S V-Z) ⟩
    case `one [Z⇒ `one |S⇒ `S (`plus ∙ # 0 ∙ `one) ]
  —→⟨ β-S V-Z ⟩
    `S (`plus ∙ `Z ∙ `one)
  —→⟨ ξ-S (ξ-∙₁ (ξ-∙₁ β-μ)) ⟩
    `S ((ƛ `ℕ ⇒ ƛ `ℕ ⇒ case # 1 [Z⇒ # 0 |S⇒ `S (`plus ∙ # 0 ∙ # 1) ]) ∙ `Z ∙ `one)
  —→⟨ ξ-S (ξ-∙₁ (β-ƛ V-Z)) ⟩
    `S ((ƛ `ℕ ⇒ case `Z [Z⇒ # 0 |S⇒ `S (`plus ∙ # 0 ∙ # 1) ]) ∙ `one)
  —→⟨ ξ-S (β-ƛ (V-S V-Z)) ⟩
    `S (case `Z [Z⇒ `one |S⇒ `S (`plus ∙ # 0 ∙ `one) ])
  —→⟨ ξ-S β-Z ⟩
    `two
  ∎

-- Properties of reduction

V¬—→ : ∀ {Γ A} → {M N : Γ ⊢ A} → Value M → ¬ (M —→ N)
V¬—→ (V-S VM) (ξ-S M—→N) = V¬—→ VM M—→N

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
progress `Z = value V-Z
progress (`S M) with progress M
...                | step M—→N = step (ξ-S M—→N)
...                | value VM = value (V-S VM)
progress case M [Z⇒ M₁ |S⇒ M₂ ] with progress M
...                                | step M—→N = step (ξ-case M—→N)
...                                | value V-Z = step β-Z
...                                | value (V-S V-M) = step (β-S V-M)
progress (μ M) = step β-μ

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
`inf = μ `S (# 0)

_ : result (eval 100 `inf) ≡ nothing
_ = refl

_ : result (eval 20 (`plus ∙ `two ∙ `two)) ≡ just (`S (`S (`S (`S `Z))))
_ = refl

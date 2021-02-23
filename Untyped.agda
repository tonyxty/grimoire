{-# OPTIONS --safe --without-K #-}
module Untyped where

open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec hiding ([_])
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Here we will use library types wherever possible.

Context = ℕ
∅ : Context
∅ = zero
_,* : Context → Context
Γ ,* = suc Γ

Var = Fin

infix 7 `_
infixr 5 ƛ_
infixl 6 _∙_
data Term : Context → Set where
  `_ : ∀ {Γ} → Var Γ → Term Γ
  ƛ_ : ∀ {Γ} → Term (Γ ,*) → Term Γ
  _∙_ : ∀ {Γ} → Term Γ → Term Γ → Term Γ

-- Examples

helper : ∀ {Γ} → ℕ → Term (2 + Γ)
helper zero = ` # 0
helper (suc n) = ` # 1 ∙ helper n

⌜_⌝ : ∀ {Γ} → ℕ → Term Γ
⌜ n ⌝ = ƛ ƛ helper n

`id : ∀ {Γ} → Term Γ
`id = ƛ ` # 0

`two : ∀ {Γ} → Term Γ
`two = ⌜ 2 ⌝

`plus : ∀ {Γ} → Term Γ
`plus = ƛ ƛ ƛ ƛ ` # 3 ∙ ` # 1 ∙ (` # 2 ∙ ` # 1 ∙ ` # 0)

-- Substitution

-- Vec.Functional may also be used
Rename : Context → Context → Set
Rename Γ Δ = Vec (Var Γ) Δ

ext : ∀ {Γ Δ} (ρ : Rename Γ Δ) → Rename (Γ ,*) (Δ ,*)
ext ρ = zero ∷ Data.Vec.map suc ρ

rename : ∀ {Γ Δ} (ρ : Rename Γ Δ) → Term Δ → Term Γ
rename ρ (` x) = ` lookup ρ x
rename ρ (ƛ M) = ƛ rename (ext ρ) M
rename ρ (M₁ ∙ M₂) = rename ρ M₁ ∙ rename ρ M₂

idRename : ∀ (Γ : Context) → Rename Γ Γ
idRename zero = []
idRename (suc Γ) = zero ∷ Data.Vec.map suc (idRename Γ)

weaken : ∀ (Γ : Context) → Rename (Γ ,*) Γ
weaken zero = []
weaken (suc Γ) = # 1 ∷ Data.Vec.map suc (weaken Γ)

_♯ : ∀ {Γ} → Term Γ → Term (Γ ,*)
M ♯ = rename (weaken _) M

Subst : Context → Context → Set
Subst Γ Δ = Vec (Term Γ) Δ

_⋆ : ∀ {Γ Δ} (ρ : Subst Γ Δ) → Subst (Γ ,*) (Δ ,*)
ρ ⋆ = ` zero ∷ Data.Vec.map _♯ ρ

subst : ∀ {Γ Δ} → Subst Γ Δ → Term Δ → Term Γ
subst ρ (` x) = lookup ρ x
subst ρ (ƛ M) = ƛ subst (ρ ⋆) M
subst ρ (M₁ ∙ M₂) = subst ρ M₁ ∙ subst ρ M₂

idSubst : ∀ (Γ : Context) → Subst Γ Γ
idSubst Γ = Data.Vec.map `_ (idRename Γ)

substByTerm : ∀ {Γ} (M : Term Γ) → Subst Γ (Γ ,*)
substByTerm {Γ} M = M ∷ idSubst Γ

_[_] : ∀ {Γ} (M : Term (Γ ,*)) (N : Term Γ) → Term Γ
M [ N ] = subst (substByTerm N) M

-- Reduction

data Neutral : ∀ {Γ} → Term Γ → Set
data Normal : ∀ {Γ} → Term Γ → Set

data Neutral where
  `_ : ∀ {Γ} (x : Var Γ) → Neutral (` x)
  _∙_ : ∀ {Γ} {M₁ M₂ : Term Γ} → Neutral M₁ → Normal M₂ → Neutral (M₁ ∙ M₂)

infix 8 ′_
data Normal where
  ′_ : ∀ {Γ} {M : Term Γ} → Neutral M → Normal M
  ƛ_ : ∀ {Γ} {M : Term (Γ ,*)} → Normal M → Normal (ƛ M)

_ : Normal (`two {∅})
_ = ƛ ƛ ′ (` # 1 ∙ ′ (` # 1 ∙ ′ (` # 0)))

infix 2 _—→_
data _—→_ : ∀ {Γ} → Term Γ → Term Γ → Set where
  ξ₁ : ∀ {Γ} {M₁ M₁' M₂ : Term Γ} → M₁ —→ M₁' → M₁ ∙ M₂ —→ M₁' ∙ M₂
  ξ₂ : ∀ {Γ} {M₁ M₂ M₂' : Term Γ} → M₂ —→ M₂' → M₁ ∙ M₂ —→ M₁ ∙ M₂'
  β : ∀ {Γ} {M : Term (Γ ,*)} {N : Term Γ} → (ƛ M) ∙ N —→ M [ N ]
  ζ : ∀ {Γ} {M M' : Term (Γ ,*)} → M —→ M' → ƛ M —→ ƛ M'

infix 1 _—↠_
infix 2 _∎
infixr 1 _—→⟨_⟩_
data _—↠_ {Γ} : Term Γ → Term Γ → Set where
  _∎ : ∀ (M : Term Γ) → M —↠ M
  _—→⟨_⟩_ : ∀ {M' M''} (M : Term Γ) → M —→ M' → M' —↠ M'' → M —↠ M''

_ : `plus {∅} ∙ `two ∙ `two —↠ ⌜ 4 ⌝
_ =
    `plus ∙ `two ∙ `two
  —→⟨ ξ₁ β ⟩
    _
  —→⟨ β ⟩
    ƛ ƛ `two ∙ ` # 1 ∙ (`two ∙ ` # 1 ∙ ` # 0)
  —→⟨ ζ (ζ (ξ₁ β)) ⟩
    _
  —→⟨ ζ (ζ (ξ₂ (ξ₁ β))) ⟩
    _
  —→⟨ ζ (ζ (ξ₂ β)) ⟩
    _
  —→⟨ ζ (ζ β) ⟩
    ⌜ 4 ⌝
  ∎

progress : ∀ {Γ} → (M : Term Γ) → ∃[ M' ] (M —→ M') ⊎ Normal M
progress (` x) = inj₂ (′ (` x))
progress (ƛ M) with progress M
...               | inj₁ (_ , M—→M') = inj₁ (-, ζ M—→M')
...               | inj₂ NM = inj₂ (ƛ NM)
progress (M₁ ∙ M₂) with progress M₁
...                     | inj₁ (_ , M₁—→M₁') = inj₁ (-, ξ₁ M₁—→M₁')
...                     | inj₂ (ƛ NM₁) = inj₁ (-, β)
...                     | inj₂ (′ x) with progress M₂
...                                       | inj₁ (_ , M₂—→M₂') = inj₁ (-, ξ₂ M₂—→M₂')
...                                       | inj₂ NM₂           = inj₂ (′ (x ∙ NM₂))

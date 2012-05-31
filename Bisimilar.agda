open import Common

module Bisimilar {A E : Set} (transition : A → Rel E) where

private
  infix 3 _⊢_⤇_
  _⊢_⤇_ : A → Rel E
  _⊢_⤇_ = transition

mutual
  infix 4 _≼_ _≽_ _≈_
  _≼_ : Rel E
  x ≼ y = ∀ {α x′} (x⤇x′ : α ⊢ x ⤇ x′) → ∃ λ y′ → α ⊢ y ⤇ y′ × x′ ≈ y′
  _≽_ : Rel E
  _≽_ = flip _≼_

  record _≈_ (x y : E) : Set where
    constructor _∧_
    field
      ≈→≼ : ∞ (x ≼ y)
      ≈→≽ : ∞ (x ≽ y)

open _≈_ public

mutual
  ≼-refl : Reflexive _≼_
  ≼-refl x⤇x′ = _ , x⤇x′ , ≈-refl

  ≈-refl : Reflexive _≈_
  ≈-refl = ♯ ≼-refl ∧ ♯ ≼-refl

≈-sym : Symmetric _≈_
≈-sym (x≼y ∧ x≽y) = x≽y ∧ x≼y

mutual
  ≼-trans : Transitive _≼_
  ≼-trans x≼y y≼z x⤇x′ with x≼y x⤇x′
  ... | y′ , y⤇y′ , x′≈y′ with y≼z y⤇y′
  ...   | z′ , z⤇z′ , y′≈z′ = z′ , z⤇z′ , ≈-trans x′≈y′ y′≈z′

  ≈-trans : Transitive _≈_
  ≈-trans (x≼y ∧ x≽y) (y≼z ∧ y≽z) = ♯ ≼-trans (♭ x≼y) (♭ y≼z) ∧ ♯ ≼-trans (♭ y≽z) (♭ x≽y)

≈-setoid : Setoid
≈-setoid = record
  { Carrier = E
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈-refl
    ; sym = ≈-sym
    ; trans = ≈-trans
    }
  }

import Relation.Binary.EqReasoning as EqR
module ≈-Reasoning = EqR ≈-setoid

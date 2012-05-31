module Correct where

open import Common
open import Language
open import Complete
open import Sound
import Bisimilar
open Bisimilar _⊢_⤇_

#↦̸ : ∀ {α h m x′ x″ } →
  α ≢ τ →
  h , ↦⟨ # m ⟩ ↠⋆ x′ →
  α ⊢ x′ ↠ x″ →
  ⊥
#↦̸ α≢τ [] (↠-↦ (↦-mutate h′)) = α≢τ ≡.refl
#↦̸ α≢τ (↠-↦ (↦-mutate h′) ∷ x↠⋆x′) x′↠x″ = #↦̸ α≢τ x↠⋆x′ x′↠x″

#↣̸ : ∀ {α h m x′ x″} →
  α ≢ τ →
  h , ↣⟨ ○ , # m ⟩ ↠⋆ x′ →
  α ⊢ x′ ↠ x″ →
  ⊥
#↣̸ α≢τ [] (↠-↣ (↣-mutate h′)) = α≢τ ≡.refl
#↣̸ α≢τ (↠-↣ (↣-mutate h′) ∷ x↠⋆x′) x′↠x″ = #↣̸ α≢τ x↠⋆x′ x′↠x″

correct : ∀ h e → h , ↦⟨ e ⟩ ≈ h , ↣⟨ ○ , e ⟩
correct h (# m) = ♯ ↦≼↣ ∧ ♯ ↣≼↦ where
  ↦≼↣ : h , ↦⟨ # m ⟩ ≼ h , ↣⟨ ○ , # m ⟩
  ↦≼↣ (⤇: α≢τ c↠⋆c′ c′↠c″) = ⊥-elim (#↦̸ α≢τ c↠⋆c′ c′↠c″)

  ↣≼↦ : h , ↣⟨ ○ , # m ⟩ ≼ h , ↦⟨ # m ⟩
  ↣≼↦ (⤇: α≢τ c↠⋆c′ c′↠c″) = ⊥-elim (#↣̸ α≢τ c↠⋆c′ c′↠c″)

correct h (a ⊕ b) = ♯ ↦≼↣ ∧ ♯ ↣≼↦ where
  ↦≼↣ : h , ↦⟨ a ⊕ b ⟩ ≼ h , ↣⟨ ○ , a ⊕ b ⟩
  ↦≼↣ e⤇e′ = {!!}

  ↣≼↦ : h , ↣⟨ ○ , a ⊕ b ⟩ ≼ h , ↦⟨ a ⊕ b ⟩
  ↣≼↦ e⤇e′ = {!!}

correct h (atomic e) = ♯ ↦≼↣ ∧ ♯ ↣≼↦ where
  ↦≼↣ : h , ↦⟨ atomic e ⟩ ≼ h , ↣⟨ ○ , atomic e ⟩
  ↦≼↣ {x′ = h″ , c″} e⤇e′ with ↦-extract e⤇e′
  ... | h₀ , m , ≡.refl , c″≡m , h≟h₀ , e↦′⋆m rewrite c″≡m with ↦′⋆→↣′⋆ ∅-Consistent ∅-Equivalent e↦′⋆m
  ...   | l′ , cons′ , equiv′ , e↣′⋆m rewrite Commit-Update cons′ equiv′ ∶ h″ ≡ Update h₀ l′ = _ , e⤇m , correct _ _ where

    mutate? : ∀ {c′} → Dec (h ≡ h₀) →
      h₀ , ↣⟨ ○ , atomic e ⟩ ↠⋆ h₀ , c′ →
      h  , ↣⟨ ○ , atomic e ⟩ ↠⋆ h₀ , c′
    mutate? (yes h≡h₀) rewrite h≡h₀ = id
    mutate? (no  h≢h₀) = _∷_ (↠-↣ (↣-mutate _))

    e↣⋆m : h₀ , ↣⟨ ○ , atomic e ⟩ ↠⋆ h₀ , ↣⟨ ● (e , l′) , atomic (# m) ⟩
    e↣⋆m = ↠-↣ ↣-begin ∷ ⋆.gmap _ (↠-↣ ∘ ↣-step) e↣′⋆m

    e⤇m : ☢ ⊢ h , ↣⟨ ○ , atomic e ⟩ ⤇ Update h₀ l′ , ↣⟨ ○ , # m ⟩
    e⤇m = ⤇: (λ ()) (mutate? h≟h₀ e↣⋆m) (↠-↣ (↣-commit cons′))

  ↣≼↦ : h , ↣⟨ ○ , atomic e ⟩ ≼ h , ↦⟨ atomic e ⟩
  ↣≼↦ (⤇: {h′} α≢τ c↠⋆c′ c′↠c″) with ↣-extract α≢τ c↠⋆c′ c′↠c″
  ... | l′ , m , ≡.refl , ≡.refl , ≡.refl , cons , e↣⋆m with ↣′⋆→↦′⋆ ∅-Consistent ∅-Equivalent (↣′⋆-swap cons e↣⋆m)
  ...   | h″ , _ , equiv , e↦′⋆m rewrite Commit-Update cons equiv ∶ h″ ≡ Update h′ l′ = (_ , _) , e⤇m , ↣≈↦ where
    -- Termination checker can't see through ≈-sym, so we inline it.
    ↦≈↣ = correct _ _
    ↣≈↦ = ≈→≽ ↦≈↣ ∧ ≈→≼ ↦≈↣

    mutate? : ∀ {h₀} → Dec (h ≡ h₀) → h , ↦⟨ atomic e ⟩ ↠⋆ h₀ , ↦⟨ atomic e ⟩
    mutate? (yes ≡.refl) = []
    mutate? (no h≢h₀) = ↠-↦ (↦-mutate _) ∷ []

    e⤇m : ☢ ⊢ h , ↦⟨ atomic e ⟩ ⤇ Update h′ l′ , ↦⟨ # m ⟩
    e⤇m = ⤇: (λ ()) (mutate? (h ≟Heap _)) (↠-↦ (↦-atomic e↦′⋆m))

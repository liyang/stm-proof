module Complete where

open import Common
open import Language

-- Equivalence of _↦′_ and _↣′_

-- The easy direction
↦′→↣′ : ∀ {h₀ l h e h′ e′} →
  Consistent h₀ l →
  Equivalent h₀ l h →
  h , e  ↦′  h′ , e′ →
  ∃ λ l′ →
  Consistent h₀ l′ ×
  Equivalent h₀ l′ h′ ×
  h₀ ⊢  l , e  ↣′  l′ , e′
↦′→↣′ cons equiv ↦′-ℕ = , cons , equiv , ↣′-ℕ
↦′→↣′ cons equiv (↦′-R m b↦b′) = Σ.map id (Σ.map id (Σ.map id (↣′-R m))) (↦′→↣′ cons equiv b↦b′)
↦′→↣′ cons equiv (↦′-L b a↦a′) = Σ.map id (Σ.map id (Σ.map id (↣′-L b))) (↦′→↣′ cons equiv a↦a′)
↦′→↣′ cons equiv (↦′-writeE e↦e′) = Σ.map id (Σ.map id (Σ.map id ↣′-writeE)) (↦′→↣′ cons equiv e↦e′)
↦′→↣′ cons equiv ↦′-writeℕ = , cons , Write-Equivalent equiv , ↣′-writeℕ
↦′→↣′ {h₀} {ρ ∧ ω} cons equiv (↦′-read v) with equiv v | ↣′-read (ρ ∧ ω) v
... | equiv-v | ↣-read′ with Vec.lookup v ω
...   | ● m rewrite equiv-v = , cons , equiv , ↣-read′
...   | ○ with Vec.lookup v ρ | ≡.inspect (Vec.lookup v) ρ
...     | ● m | _ rewrite equiv-v = , cons , equiv , ↣-read′
...     | ○   | [ ρ[v]≡○ ] rewrite equiv-v = _
          , Equivalence.to (Read-Consistent (ρ ∧ ω) v ρ[v]≡○) ⟨$⟩ cons
          , Read-Equivalent cons equiv , ↣-read′

↦′⋆→↣′⋆ : ∀ {h₀ l h e h′ e′} →
  Consistent h₀ l →
  Equivalent h₀ l h →
  h , e  ↦′⋆  h′ , e′ →
  ∃ λ l′ →
  Consistent h₀ l′ ×
  Equivalent h₀ l′ h′ ×
  h₀ ⊢ l , e  ↣′⋆ l′ , e′
↦′⋆→↣′⋆ cons equiv [] = _ , cons , equiv , []
↦′⋆→↣′⋆ cons equiv (e↦e′ ∷ e′↦⋆e″) with ↦′→↣′ cons equiv e↦e′
... | l′ , cons′ , equiv′ , e↣e′ with ↦′⋆→↣′⋆ cons′ equiv′ e′↦⋆e″
...   | l″ , cons″ , equiv″ , e′↣⋆e″ = l″ , cons″ , equiv″ , e↣e′ ∷ e′↣⋆e″
module Lemmas where

open import Common
open import Language


{-- No progress

infix 3 _⇉̸ _↠̸ _⤇̸
_↦̸ : Expression → Set
e ↦̸ = ∀ {α h h′e′} → α ⊢ h , e ↦ h′e′ → ⊥

_⇉̸ : Combined → Set
c ⇉̸ = ∀ {α h h′c′} → α ⊢ h , c ⇉ h′c′ → ⊥

_↠̸ : Soup → Set
s ↠̸ = ∀ {α h h′s′} → α ⊢ h , s ↠ h′s′ → ⊥

_⤇̸ : Soup → Set
s ⤇̸ = ∀ {α h h′s′} → α ⊢ h , s ⤇ h′s′ → ⊥

↦̸→⇉̸ : ∀ {e} → e ↦̸ → ↦⟨ e ⟩ ⇉̸
↦̸→⇉̸ e↦̸ (⇉-↦ e↦) = e↦̸ e↦

⇉̸→↠̸ : ∀ {c} → c ⇉̸ → c ∷ [] ↠̸
⇉̸→↠̸ c⇉̸ (↠-⇉ c⇉) = c⇉̸ c⇉
⇉̸→↠̸ c⇉̸ (↠-… ())

⇉̸→⤇̸ : ∀ {c} → c ⇉̸ → c ∷ [] ⤇̸
⇉̸→⤇̸ c⇉̸ (⤇: α≢τ [] c↠) = ⇉̸→↠̸ c⇉̸ c↠
⇉̸→⤇̸ c⇉̸ (⤇: α≢τ (c↠ ∷ _) _) = ⇉̸→↠̸ c⇉̸ c↠

↦⟨#⟩⇉̸ : ∀ {m} → ↦⟨ # m ⟩ ⇉̸
↦⟨#⟩⇉̸ (⇉-↦ ())

↣⟨#⟩⇉̸ : ∀ {m} → ↣⟨ ○ , # m ⟩ ⇉̸
↣⟨#⟩⇉̸ (⇉-↣ ())

↦̸τ : ∀ {h e h′e′} → τ ⊢ h , e ↦ h′e′ → ⊥
↦̸τ ()
-}

{-
-- Transitions that preserve things

↣τ→h≡h′ : ∀ {h te h′ t′e′} →
  τ ⊢  h , te  ↣  h′ , t′e′ →
  h ≡ h′
{-
↣τ→h≡h′ (↣-R m b↣b′) = ↣τ→h≡h′ b↣b′
↣τ→h≡h′ (↣-L b a↣a′) = ↣τ→h≡h′ a↣a′
-}
↣τ→h≡h′ ↣-begin = ≡.refl
↣τ→h≡h′ (↣-step e↣e′) = ≡.refl
↣τ→h≡h′ (↣-abort ¬cons) = ≡.refl

⇉τ→h≡h′ : ∀ {h tc h′ t′c′} →
  τ ⊢  h , tc  ⇉  h′ , t′c′ →
  h ≡ h′
⇉τ→h≡h′ (⇉-↦ e↦e′) = ⊥-elim (↦̸τ e↦e′)
⇉τ→h≡h′ (⇉-↣ e↣e′) = ↣τ→h≡h′ e↣e′

↠τ→h≡h′ : ∀ {h h′ s s′} →
  h , s  ↠τ  h′ , s′ →
  h ≡ h′
↠τ→h≡h′ (↠-⇉ c⇉c′) = ⇉τ→h≡h′ c⇉c′
↠τ→h≡h′ (↠-… s↠s′) = ↠τ→h≡h′ s↠s′

↠⋆→h≡h′ : ∀ {h h′ s s′} →
  h , s  ↠⋆  h′ , s′ →
  h ≡ h′
↠⋆→h≡h′ [] = ≡.refl
↠⋆→h≡h′ (x↠x′ ∷ x′↠⋆x″) with ↠τ→h≡h′ x↠x′ | ↠⋆→h≡h′ x′↠⋆x″
... | ≡.refl | ≡.refl = ≡.refl
-}

-- Equivalence of _↦′_ and _↣′_

{-
↦→↣ : ∀ {h₀ l h e h′ e′} →
  Consistent h₀ l →
  Equivalent h h₀ l →
  h , e  ↦′  h′ , e′ →
  ∃ λ l′ →
  Consistent h₀ l′ ×
  Equivalent h′ h₀ l′ ×
  h₀ ⊢  l , e  ↣′  l′ , e′
↦→↣ cons equiv ↦-ℕ = , cons , equiv , ↣-ℕ
↦→↣ cons equiv (↦-R m b↦b′) = Σ.map id (Σ.map id (Σ.map id (↣-R m))) (↦→↣ cons equiv b↦b′)
↦→↣ cons equiv (↦-L b a↦a′) = Σ.map id (Σ.map id (Σ.map id (↣-L b))) (↦→↣ cons equiv a↦a′)
↦→↣ {h₀} {ρ ∧ ω} cons equiv (↦-read v) with equiv v | ↣-read (ρ ∧ ω) v
... | equiv-v | ↣-read′ with Vec.lookup v ω
...   | ● m rewrite equiv-v = , cons , equiv , ↣-read′
...   | ○ with Vec.lookup v ρ | ≡.inspect (Vec.lookup v) ρ
...     | ● m | _ rewrite equiv-v = , cons , equiv , ↣-read′
...     | ○   | [ ρ[v]≡○ ] rewrite equiv-v = _ 
          , Equivalence.to (Read-Consistent (ρ ∧ ω) v ρ[v]≡○) ⟨$⟩ cons
          , Read-Equivalent cons equiv , ↣-read′
↦→↣ cons equiv (↦-writeE e↦e′) = Σ.map id (Σ.map id (Σ.map id ↣-writeE)) (↦→↣ cons equiv e↦e′)
↦→↣ cons equiv ↦-writeℕ = , cons , Write-Equivalent equiv , ↣-writeℕ
-}

{-
↦⋆→↣⋆ : ∀ {h₀ l h e h′ e′ R} →
  Consistent h₀ l →
  Equivalent h h₀ l →
  h , e  ↦⋆  h′ , e′ →
  ∃ λ l′ →
  Consistent h₀ l′ ×
  Equivalent h′ h₀ l′ ×
  h₀ , ● (R , l) , atomic e  ↣⋆  h₀ , ● (R , l′) , atomic e′
↦⋆→↣⋆ cons equiv [] = _ , cons , equiv , []
↦⋆→↣⋆ cons equiv (e↦e′ ∷ e′↦⋆e″) with ↦→↣ cons equiv e↦e′
... | l′ , cons′ , equiv′ , e↣e′ with ↦⋆→↣⋆ cons′ equiv′ e′↦⋆e″
...   | l″ , cons″ , equiv″ , e′↣⋆e″ = l″ , cons″ , equiv″ , ↣-step e↣e′ ∷ e′↣⋆e″
-}

{-
↣⋆→↦⋆ : ∀ {h hR l e l′ e′ h₀ h₀′ R} →
  Consistent h₀ l →
  Equivalent h h₀ l →
  hR , R ↦⋆ h , e →
  h₀ , ● (R , l) , atomic e  ↣⋆  h₀′ , ● (R , l′) , atomic e′ →
  ∃ λ h′ →
  Consistent h₀′ l′ ×
  Equivalent h′ h₀′ l′ ×
  hR , R  ↦⋆  h′ , e′
↣⋆→↦⋆ cons equiv R↦⋆e [] = _ , cons , equiv , R↦⋆e
↣⋆→↦⋆ cons equiv R↦⋆e (↣-step e↣e′ ∷ xs) = {!!}
↣⋆→↦⋆ cons equiv R↦⋆e (↣-mutate ∷ xs) = {!!}
↣⋆→↦⋆ cons equiv R↦⋆e (↣-abort ¬cons ∷ xs) = ↣⋆→↦⋆ ∅-Consistent ∅-Equivalent [] {!xs!} --  {!xs!}
-}

{-
↣→↦ : ∀ {h l e l′ e′ h₀} →
  Consistent h₀ l →
  Equivalent h h₀ l →
  h₀ ⊢  l , e  ↣′  l′ , e′ →
  ∃ λ h′ →
  Consistent h₀ l′ ×
  Equivalent h′ h₀ l′ ×
  h , e ↦′ h′ , e′
↣→↦ cons equiv ↣-ℕ = , cons , equiv , ↦-ℕ
↣→↦ cons equiv (↣-R m b↣b′) = Σ.map id (Σ.map id (Σ.map id (↦-R m))) (↣→↦ cons equiv b↣b′)
↣→↦ cons equiv (↣-L b a↣a′) = Σ.map id (Σ.map id (Σ.map id (↦-L b))) (↣→↦ cons equiv a↣a′)
↣→↦ {h} {l} cons equiv (↣-read {v = v}) with equiv v | ↦-read {h} {v}
... | equiv-v | ↦-read′ with Vec.lookup v (Logs.ω l)
...   | ● m rewrite equiv-v = , cons , equiv , ↦-read′
...   | ○ with Vec.lookup v (Logs.ρ l)
...     | ● m rewrite equiv-v = , cons , equiv , ↦-read′
...     | ○ rewrite equiv-v = , Read-Consistent l cons , Read-Equivalent cons equiv , ↦-read′
↣→↦ cons equiv (↣-writeE e↣e′) = Σ.map id (Σ.map id (Σ.map id ↦-writeE)) (↣→↦ cons equiv e↣e′)
↣→↦ cons equiv ↣-writeℕ = , cons , Write-Equivalent equiv , ↦-writeℕ

↠⋆-↣-step : ∀ R {h l e l′ e′ s} →
  h ⊢ l , e ↣⋆ l′ , e′ →
  h , ↣⟨ ● (R , l) , atomic e ⟩ ∷ s  ↠⋆  h , ↣⟨ ● (R , l′) , atomic e′ ⟩ ∷ s
↠⋆-↣-step R = ⋆.gmap _ (↠-⇉ ∘ ⇉-↣ ∘ ↣-step)

↣⋆→↦⋆ : ∀ {h l e l′ e′ h₀} →
  Consistent h₀ l →
  Equivalent h h₀ l →
  h₀ ⊢  l , e  ↣⋆  l′ , e′ →
  ∃ λ h′ →
  Consistent h₀ l′ ×
  Equivalent h′ h₀ l′ ×
  h , e  ↦⋆  h′ , e′
↣⋆→↦⋆ cons equiv [] = , cons , equiv , []
↣⋆→↦⋆ cons equiv (e↣e′ ∷ e′↣⋆e″) with ↣→↦ cons equiv e↣e′
... | h′ , cons′ , equiv′ , e↦e′ with ↣⋆→↦⋆ cons′ equiv′ e′↣⋆e″
...   | h″ , cons″ , equiv″ , e′↦⋆e″ = h″ , cons″ , equiv″ , e↦e′ ∷ e′↦⋆e″
-}

↣-Consistent : ∀ {h l e l′ e′} →
  h ⊢  l , e  ↣′  l′ , e′ →
  Consistent h l ⇔ Consistent h l′
↣-Consistent ↣-ℕ = Equivalence.id
↣-Consistent (↣-R m b↣b′) = ↣-Consistent b↣b′
↣-Consistent (↣-L b a↣a′) = ↣-Consistent a↣a′
↣-Consistent (↣-read l v) = Read-Consistent′ l v
↣-Consistent (↣-writeE e↣e′) = ↣-Consistent e↣e′
↣-Consistent ↣-writeℕ = Equivalence.id

{-
boo : ∀ {l h h′} v → let l′∧m = Read h l v in
  Consistent h (fst l′∧m) →
  Consistent h′ l →
  Read h l v ≡ Read h′ l v
boo {l} {h} {h′} v cons cons′ with Vec.lookup v (Logs.ω l)
... | ● m = ≡.refl
... | ○ with Vec.lookup v (Logs.ρ l)
...   | ● m = ≡.refl
...   | ○ = {!cons v (Vec.lookup v h′)!}
-}

Contained : ∀ {h l e c′} → h ⊢ l , e ↣′ c′ → Set
Contained ↣-ℕ = ⊤
Contained (↣-R m b↣b′) = Contained b↣b′
Contained (↣-L b a↣a′) = Contained a↣a′
Contained {h} (↣-read l v) = l ≡ fst (Read h l v)
Contained (↣-writeE e↣e′) = Contained e↣e′
Contained ↣-writeℕ = ⊤

moo : ∀ {h h′ l e l′ e′} →
  Consistent h l′ →
  Consistent h′ l′ →
  h  ⊢  l , e  ↣′  l′ , e′ →
  h′ ⊢  l , e  ↣′  l′ , e′
moo cons cons′ ↣-ℕ = ↣-ℕ
moo cons cons′ (↣-R m b↣b′) = ↣-R m (moo cons cons′ b↣b′)
moo cons cons′ (↣-L b a↣a′) = ↣-L b (moo cons cons′ a↣a′)
moo cons cons′ (↣-writeE e↣e′) = ↣-writeE (moo cons cons′ e↣e′)
moo cons cons′ ↣-writeℕ = ↣-writeℕ
moo {h} {h′} cons cons′ (↣-read l v) = {!↣-read {h′} l v!}

bar : ∀ {h h′ l e l′ e′} →
  Consistent h  l′ →
  Consistent h′ l′ →
  h  ⊢ l , e ↣⋆ l′ , e′ →
  h′ ⊢ l , e ↣⋆ l′ , e′
bar cons cons′ e↣e′ = {!!}

↠⋆/↣-step : ∀ {α R h l e h′ c′ h″ c″} →
  h ⊢ ∅ , R ↣⋆ l , e →
  α ≢ τ →
  h , ↣⟨ ● (R , l) , atomic e ⟩  ↠⋆  h′ , c′ →
  α ⊢  h′ , c′  ↠  h″ , c″ →
  ∃₂ λ l′ m →
  c′ ≡ ↣⟨ ● (R , l′) , atomic (# m) ⟩ ×
  h′ ⊢  ∅ , R  ↣⋆  l′ , # m ×
  Consistent h′ l′ ×
  Equivalent h′ l′ h″
↠⋆/↣-step R↣⋆e α≢τ [] (↠-↣ (↣-step e↣e′)) = ⊥-elim (α≢τ ≡.refl)
↠⋆/↣-step R↣⋆e α≢τ [] (↠-↣ (↣-mutate h′)) = ⊥-elim (α≢τ ≡.refl)
↠⋆/↣-step R↣⋆e α≢τ [] (↠-↣ (↣-abort ¬cons)) = ⊥-elim (α≢τ ≡.refl)
↠⋆/↣-step R↣⋆e α≢τ [] (↠-↣ (↣-commit cons)) = _ , _ , ≡.refl , R↣⋆e , cons , Update-Equivalent cons
↠⋆/↣-step R↣⋆e α≢τ (↠-↣ (↣-step e↣e′) ∷ c′↠c″) c″↠c‴ = ↠⋆/↣-step (R↣⋆e ◅◅ e↣e′ ∷ []) α≢τ c′↠c″ c″↠c‴
↠⋆/↣-step {l = l} R↣⋆e α≢τ (↠-↣ (↣-mutate h′) ∷ c′↠c″) c″↠c‴ with Consistent? h′ l
... | yes cons = ↠⋆/↣-step {!R↣⋆e!} α≢τ c′↠c″ c″↠c‴
... | no ¬cons = {!!}
↠⋆/↣-step R↣⋆e α≢τ (↠-↣ (↣-abort ¬cons) ∷ c′↠c″) c″↠c‴ = ↠⋆/↣-step [] α≢τ c′↠c″ c″↠c‴

{- with cons?
... | yes c rewrite ≡.sym (Commit-Update c equiv)
  = _ , _ , ≡.refl , {!R↣⋆e!} , cons , {!!}
... | no ¬cons = {!⊥-elim (¬cons cons)!}
-}


{-
↠⋆/↣-step : ∀ {α R h l e h′ c′ h″ c″} →
  h′ ⊢ ∅ , R  ↣⋆  l , e →
  Dec (Consistent h l) →
  α ≢ τ →
  h , ↣⟨ ● (R , l) , atomic e ⟩  ↠⋆  h′ , c′ →
  α ⊢  h′ , c′  ↠  h″ , c″ →
  ∃₂ λ l′ m →
  c′ ≡ ↣⟨ ● (R , l′) , atomic (# m) ⟩ ×
  h′ ⊢  ∅ , R  ↣⋆  l′ , # m ×
  Consistent h′ l′
↠⋆/↣-step R↣⋆e cons? α≢τ [] (↠-↣ (↣-step e↣e′)) = ⊥-elim (α≢τ ≡.refl)
↠⋆/↣-step R↣⋆e cons? α≢τ [] (↠-↣ (↣-mutate h′)) = ⊥-elim (α≢τ ≡.refl)
↠⋆/↣-step R↣⋆e cons? α≢τ [] (↠-↣ (↣-abort ¬cons)) = ⊥-elim (α≢τ ≡.refl)
↠⋆/↣-step R↣⋆e cons? α≢τ [] (↠-↣ (↣-commit cons)) with cons?
... | yes _ = _ , _ , ≡.refl , R↣⋆e , cons
... | no ¬cons = ⊥-elim (¬cons cons)
↠⋆/↣-step R↣⋆e cons? α≢τ (↠-↣ (↣-step e↣e′) ∷ e′↠⋆e″) c″↠c‴ = ↠⋆/↣-step
  (R↣⋆e ◅◅ moo {!!} e↣e′ ∷ []) cons′? α≢τ e′↠⋆e″ c″↠c‴ where
  cons′? = Dec.map (↣-Consistent e↣e′) cons?
↠⋆/↣-step R↣⋆e cons? α≢τ (↠-↣ (↣-abort ¬cons) ∷ R↠⋆e′) c′↠c″ = ↠⋆/↣-step
  [] (yes ∅-Consistent) α≢τ R↠⋆e′ c′↠c″
↠⋆/↣-step {l = l} R↣⋆e cons? α≢τ (↠-↣ (↣-mutate h′) ∷ e↠⋆e′) c′↠c″ = ↠⋆/↣-step
  R↣⋆e (Consistent? h′ l) α≢τ e↠⋆e′ c′↠c″
-}

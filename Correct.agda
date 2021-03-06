open import Common
module Correct (∣Heap∣ : ℕ) where

open import Language ∣Heap∣
open import Lemmas ∣Heap∣
open import Complete ∣Heap∣
open import Sound ∣Heap∣
open import Bisimilar ∣Heap∣

#⊢↦≈↣ : ∀ {h m} → h , # m ⊢ ↦: ≈ ↣: ○
#⊢↦≈↣ = ♯ (⊥-elim ∘ #⤇̸) ∧ ♯ (⊥-elim ∘ #⤇̸)

m⊕n⊢↦≈↣ : ∀ {h m n} → h , # m ⊕ # n ⊢ ↦: ≈ ↣: ○
m⊕n⊢↦≈↣ {h} {m} {n} = ♯ ↦≼↣ ∧ ♯ ↣≼↦ where
  ↦≼↣ : h , # m ⊕ # n ⊢ ↦: ≼ ↣: ○
  ↦≼↣ (⤇: α≢τ [] (↠-↦ ↦-ℕ)) = _ , ⤇: α≢τ [] (↠-↣ ↣-ℕ) , #⊢↦≈↣
  ↦≼↣ (⤇: α≢τ [] (↠-↦ (↦-R ._ b↦b′))) = ⊥-elim (#↦̸ b↦b′)
  ↦≼↣ (⤇: α≢τ [] (↠-↦ (↦-L ._ a↦a′))) = ⊥-elim (#↦̸ a↦a′)
  ↦≼↣ (⤇: α≢τ (↠-↦ (↦-R ._ b↦b′) ∷ c′↠⋆c″) c″↠c‴) = ⊥-elim (#↦̸ b↦b′)
  ↦≼↣ (⤇: α≢τ (↠-↦ (↦-L ._ a↦a′) ∷ c′↠⋆c″) c″↠c‴) = ⊥-elim (#↦̸ a↦a′)

  ↣≼↦ : h , # m ⊕ # n ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: α≢τ [] (↠-↣ ↣-ℕ)) = _ , ⤇: α≢τ [] (↠-↦ ↦-ℕ) , ≈-sym #⊢↦≈↣
  ↣≼↦ (⤇: α≢τ [] (↠-↣ (↣-R ._ b↣b′))) = ⊥-elim (#↣̸ b↣b′)
  ↣≼↦ (⤇: α≢τ [] (↠-↣ (↣-L ._ a↣a′))) = ⊥-elim (#↣̸ a↣a′)
  ↣≼↦ (⤇: α≢τ (↠-↣ (↣-R ._ b↣b′) ∷ c′↠⋆c″) c″↠c‴) = ⊥-elim (#↣̸ b↣b′)
  ↣≼↦ (⤇: α≢τ (↠-↣ (↣-L ._ a↣a′) ∷ c′↠⋆c″) c″↠c‴) = ⊥-elim (#↣̸ a↣a′)

eval-right : ∀ {h m b} →
  h , b ⊢ ↦: ≈ ↣: ○ →
  h , # m ⊕ b ⊢ ↦: ≈ ↣: ○
eval-right {h} {m} {b} b⊢↦≈↣ = ♯ ↦≼↣ ∧ ♯ ↣≼↦ where

  ↦≼↣ : h , # m ⊕ b ⊢ ↦: ≼ ↣: ○
  ↦≼↣ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↦-R α≢τ e↠⋆e′ e′↠e″
  ... | inl (n , b≡n , ≡.refl , ≡.refl , ≡.refl) rewrite b≡n = ♭ (≈→≼ m⊕n⊢↦≈↣) (⤇: α≢τ [] (↠-↦ ↦-ℕ))
  ... | inr (h′ , b′ , h″ , b″ , ≡.refl , ≡.refl , b↠⋆b′ , b′↠b″) with ♭ (≈→≼ b⊢↦≈↣) (⤇: α≢τ b↠⋆b′ b′↠b″)
  ...   | c″ , b⤇b″ , b″⊢↦≈↣ with ⤇∘↣-R m b⤇b″
  ...     | c″≡↣ , m⊕b⤇m⊕b″ rewrite c″≡↣ = _ , m⊕b⤇m⊕b″ , eval-right b″⊢↦≈↣

  ↣≼↦ : h , # m ⊕ b ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↣-R α≢τ e↠⋆e′ e′↠e″
  ... | inl (n , b≡n , ≡.refl , ≡.refl , ≡.refl) rewrite b≡n = ♭ (≈→≽ m⊕n⊢↦≈↣) (⤇: α≢τ [] (↠-↣ ↣-ℕ))
  ... | inr (h′ , t′ , b′ , h″ , b″ , ≡.refl , ≡.refl , b↠⋆b′ , b′↠b″) with ♭ (≈→≽ b⊢↦≈↣) (⤇: α≢τ b↠⋆b′ b′↠b″)
  ...   | c″ , b⤇b″ , b″⊢↣≈↦ with ⤇∘↦-R m b⤇b″
  ...     | c″≡↦ , m⊕b⤇m⊕b″ rewrite c″≡↦ = _ , m⊕b⤇m⊕b″ , ↣≈↦ where
    -- Termination checker can't see through ≈-sym, so we inline it.
    ↦≈↣ = eval-right (≈-sym b″⊢↣≈↦)
    ↣≈↦ = ≈→≽ ↦≈↣ ∧ ≈→≼ ↦≈↣

eval-left : ∀ {h a b} →
  h , a ⊢ ↦: ≈ ↣: ○ →
  (∀ h′ → h′ , b ⊢ ↦: ≈ ↣: ○) →
  h , a ⊕ b ⊢ ↦: ≈ ↣: ○
eval-left {h} {a} {b} a⊢↦≈↣ ∀b⊢↦≈↣ = ♯ ↦≼↣ ∧ ♯ ↣≼↦ where

  ↦≼↣ : h , a ⊕ b ⊢ ↦: ≼ ↣: ○
  ↦≼↣ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↦-L α≢τ e↠⋆e′ e′↠e″
  ... | inl (m , a≡m) rewrite a≡m = ♭ (≈→≼ (eval-right (∀b⊢↦≈↣ h))) (⤇: α≢τ e↠⋆e′ e′↠e″)
  ... | inr (h′ , a′ , h″ , a″ , ≡.refl , ≡.refl , a↠⋆a′ , a′↠a″) with ♭ (≈→≼ a⊢↦≈↣) (⤇: α≢τ a↠⋆a′ a′↠a″)
  ...   | c″ , a⤇a″ , a″⊢↦≈↣ with ⤇∘↣-L b a⤇a″
  ...     | c″≡↣ , a⊕b⤇a″⊕b rewrite c″≡↣ = _ , a⊕b⤇a″⊕b , eval-left a″⊢↦≈↣ ∀b⊢↦≈↣

  ↣≼↦ : h , a ⊕ b ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↣-L α≢τ e↠⋆e′ e′↠e″
  ... | inl (m , a≡m) rewrite a≡m = ♭ (≈→≽ (eval-right (∀b⊢↦≈↣ h))) (⤇: α≢τ e↠⋆e′ e′↠e″)
  ... | inr (h′ , t′ , a′ , h″ , a″ , ≡.refl , ≡.refl , a↠⋆a′ , a′↠a″) with ♭ (≈→≽ a⊢↦≈↣) (⤇: α≢τ a↠⋆a′ a′↠a″)
  ...   | c″ , a⤇a″ , a″⊢↣≈↦ with ⤇∘↦-L b a⤇a″
  ...     | c″≡↦ , a⊕b⤇a″⊕b rewrite c″≡↦ = _ , a⊕b⤇a″⊕b , ↣≈↦ where
    -- The termination/productivity checker can't see through the outer ≈-sym in
    -- ≈-sym (eval-left (≈-sym a″⊢↣≈↦) ∀b⊢↦≈↣) ; fortunately inlining it helps.
    ↦≈↣ = eval-left (≈-sym a″⊢↣≈↦) ∀b⊢↦≈↣
    ↣≈↦ = ≈→≽ ↦≈↣ ∧ ≈→≼ ↦≈↣

transaction : ∀ {h e} → h , atomic e ⊢ ↦: ≈ ↣: ○
transaction {h} {e} = ♯ ↦≼↣ ∧ ♯ ↣≼↦ where
  ↦≼↣ : h , atomic e ⊢ ↦: ≼ ↣: ○
  ↦≼↣ {h″} e⤇e′ with ↦-extract e⤇e′
  ... | h₀ , m , ≡.refl , ≡.refl , h≟h₀ , e↦′⋆m with ↦′⋆→↣′⋆ ∅-Consistent ∅-Equivalent e↦′⋆m
  ...   | l′ , cons′ , equiv′ , e↣′⋆m rewrite h″ ≡ Update h₀ l′ ∋ Commit-Update cons′ equiv′ = _ , e⤇m , #⊢↦≈↣ where

    mutate? : ∀ {c′} → Dec (h ≡ h₀) →
      h₀ , ↣: ● (e , ∅) , atomic e ↠⋆ h₀ , c′ →
      h  , ↣: ● (e , ∅) , atomic e ↠⋆ h₀ , c′
    mutate? (yes h≡h₀) rewrite h≡h₀ = id
    mutate? (no  h≢h₀) = _∷_ (↠-↣ (↣-mutate _))

    e↣⋆m : h₀ , ↣: ● (e , ∅) , atomic e ↠⋆ h₀ , ↣: ● (e , l′) , atomic (# m)
    e↣⋆m = ⋆.gmap _ (↠-↣ ∘ ↣-step) e↣′⋆m

    e⤇m : ☢ ⊢ h , ↣: ○ , atomic e ⤇ Update h₀ l′ , ↣: ○ , # m
    e⤇m = ⤇: (λ ()) (↠-↣ ↣-begin ∷ mutate? h≟h₀ e↣⋆m) (↠-↣ (↣-commit cons′))

  ↣≼↦ : h , atomic e ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: {h′} α≢τ c↠⋆c′ c′↠c″) with ↣-extract α≢τ c↠⋆c′ c′↠c″
  ... | l′ , m , ≡.refl , ≡.refl , ≡.refl , cons , e↣⋆m with ↣′⋆→↦′⋆ ∅-Consistent ∅-Equivalent (↣′⋆-swap cons e↣⋆m)
  ...   | h″ , _ , equiv , e↦′⋆m rewrite h″ ≡ Update h′ l′ ∋ Commit-Update cons equiv = _ , e⤇m , ≈-sym #⊢↦≈↣ where

    mutate? : ∀ {h₀} → Dec (h ≡ h₀) → h , ↦: , atomic e ↠⋆ h₀ , ↦: , atomic e
    mutate? (yes ≡.refl) = []
    mutate? (no h≢h₀) = ↠-↦ (↦-mutate _) ∷ []

    e⤇m : ☢ ⊢ h , ↦: , atomic e ⤇ Update h′ l′ , ↦: , # m
    e⤇m = ⤇: (λ ()) (mutate? (h ≟Heap _)) (↠-↦ (↦-atomic e↦′⋆m))

correct : ∀ h e → h , e ⊢ ↦: ≈ ↣: ○
correct h (# m) = #⊢↦≈↣
correct h (a ⊕ b) = eval-left (correct h a) (λ h′ → correct h′ b)
correct h (atomic e) = transaction

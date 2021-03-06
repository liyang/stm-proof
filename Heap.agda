open import Common
module Heap (∣Heap∣ : ℕ) where

Variable : Set
Variable = Fin ∣Heap∣

infix 5 _∧_
record Logs : Set where
  constructor _∧_
  field
    ρ ω : Vec (Maybe ℕ) ∣Heap∣

∅ : Logs
∅ = Vec.replicate ○ ∧ Vec.replicate ○

Heap : Set
Heap = Vec ℕ ∣Heap∣

infix 4 _≟Heap_
_≟Heap_ : ∀ (h h′ : Heap) → Dec (h ≡ h′)
h ≟Heap h′ = Dec.map Vec.Pointwise-≡ (Vec.Pointwise.decidable _≟ℕ_ h h′)

infix 8 _[_]≔_
_[_]≔_ : {α : Set} {N : ℕ} → Vec α N → Fin N → α → Vec α N
_[_]≔_ = Vec._[_]≔_

Read : Heap → Logs → Variable → Logs × ℕ
Read h (ρ ∧ ω) v with Vec.lookup v ω
... | ● m = ρ ∧ ω , m
... | ○ with Vec.lookup v ρ
...   | ● m = ρ ∧ ω , m
...   | ○ = ρ [ v ]≔ ● m ∧ ω , m where
  m = Vec.lookup v h

Write : Logs → Variable → ℕ → Logs
Write (ρ ∧ ω) v m = ρ ∧ ω [ v ]≔ ● m

Update : Heap → Logs → Heap
Update h (ρ ∧ ω) = Vec.tabulate (λ v → Maybe.from (Vec.lookup v h) (Vec.lookup v ω))

Consistent : Heap → Logs → Set
Consistent h (ρ ∧ _) = ∀ v m → Vec.lookup v ρ ≡ ● m → Vec.lookup v h ≡ m

Consistent? : Decidable Consistent
Consistent? h (ρ ∧ ω) = Dec.map′ Vec.Pointwise.app Vec.Pointwise.ext
    (Vec.Pointwise.decidable dec h ρ) where
  dec : (h[v] : ℕ) (ρ[v] : Maybe ℕ) → Dec (∀ m → ρ[v] ≡ ● m → h[v] ≡ m)
  dec h[v] (● m) with h[v] ≟ℕ m
  ... | yes h[v]≡m rewrite h[v]≡m = yes (λ _ → ●-inj)
  ... | no h[v]≢m = no (λ p → h[v]≢m (p m ≡.refl))
  dec h[v] ○ = yes (λ m ())

Equivalent : Heap → Logs → Heap → Set
Equivalent h₀ l h′ = flip Vec.lookup h′ ≗ snd ∘ Read h₀ l

private
  ∅[v]≡○ : ∀ {N} (v : Fin N) → Vec.lookup v (Vec.replicate ○) ≡ ○
  ∅[v]≡○ v = Morphism.op-pure (Vec.lookup-morphism v) (Maybe ℕ ∋ ○)

∅-Consistent : ∀ {h} → Consistent h ∅
∅-Consistent v rewrite ∅[v]≡○ v = λ m ()

∅-Equivalent : ∀ {h} → Equivalent h ∅ h
∅-Equivalent v rewrite ∅[v]≡○ v | ∅[v]≡○ v = ≡.refl

Read-Consistent : ∀ {h} l v → let open Logs l in Vec.lookup v ρ ≡ ○ →
  Consistent h l ⇔ Consistent h (ρ [ v ]≔ ● (Vec.lookup v h) ∧ ω)
Read-Consistent {h} (ρ ∧ ω) v ρ[v]≡○ = equivalence t f where
  t : Consistent h (ρ ∧ ω) → Consistent h (ρ [ v ]≔ ● (Vec.lookup v h) ∧ ω)
  t cons v′ with v′ ≟Fin v
  ... | yes v′≡v rewrite v′≡v | Vec.lookup∘update v ρ (● (Vec.lookup v h)) = λ m → ●-inj
  ... | no v′≢v rewrite Vec.lookup∘update′ v′≢v ρ (● (Vec.lookup v h)) = cons v′

  f : Consistent h (ρ [ v ]≔ ● (Vec.lookup v h) ∧ ω) → Consistent h (ρ ∧ ω)
  f cons v′ with v′ ≟Fin v
  ... | yes v′≡v rewrite v′≡v | ρ[v]≡○ = λ m ()
  ... | no v′≢v rewrite ≡.sym $ Vec.lookup∘update′ v′≢v ρ (● (Vec.lookup v h)) = cons v′

Read-Consistent′ : ∀ {h} l v →
  Consistent h l ⇔ Consistent h (fst (Read h l v))
Read-Consistent′ (ρ ∧ ω) v with Vec.lookup v ω
... | ● n = Equivalence.id
... | ○ with Vec.lookup v ρ | ≡.inspect (Vec.lookup v) ρ
...   | ● n | _ = Equivalence.id
...   | ○   | [ ρ[v]≡○ ] = Read-Consistent (ρ ∧ ω) v ρ[v]≡○

Read-Equivalent : ∀ {h₀ l h′ v} → let open Logs l in
  Consistent h₀ l → Equivalent h₀ l h′ → Equivalent h₀ (ρ [ v ]≔ ● (Vec.lookup v h₀) ∧ ω) h′
Read-Equivalent {h₀} {ρ ∧ ω} {h′} {v} cons equiv v′ with cons v′ | equiv v′
... | cons-v′ | equiv-v′ with Vec.lookup v′ ω
...   | ● m = equiv-v′
...   | ○ with v′ ≟Fin v

Read-Equivalent {h₀} {ρ ∧ ω} {h′} {v} cons equiv v′
    | cons-v′ | equiv-v′ | ○
        | yes v′≡v rewrite v′≡v | Vec.lookup∘update v ρ (● (Vec.lookup v h₀)) with Vec.lookup v ρ
...       | ● m = ≡.trans equiv-v′ (≡.sym (cons-v′ m ≡.refl))
...       | ○ = equiv-v′

Read-Equivalent {h₀} {ρ ∧ ω} {h′} {v} cons equiv v′
    | cons-v′ | equiv-v′ | ○
        | no v′≢v rewrite Vec.lookup∘update′ v′≢v ρ (● (Vec.lookup v h₀)) with Vec.lookup v′ ρ
...       | ● m = equiv-v′
...       | ○ = equiv-v′

Read-Equivalent′ : ∀ h l {h′} v →
  Consistent h l →
  Equivalent h l h′ →
  Equivalent h (fst (Read h l v)) h′
Read-Equivalent′ h (ρ ∧ ω) v cons equiv v′ with Vec.lookup v ω
... | ● m = equiv v′
... | ○ with Vec.lookup v ρ
...   | ● m = equiv v′
...   | ○ = Read-Equivalent cons equiv v′

Write-Equivalent : ∀ {h h₀ l v m} →
  Equivalent h₀ l h →
  Equivalent h₀ (Write l v m) (h [ v ]≔ m)
Write-Equivalent {h} {l = ρ ∧ ω} {v} {m} equiv v′ with equiv v′
... | equiv-v′ with v′ ≟Fin v
...   | yes v′≡v rewrite v′≡v | Vec.lookup∘update v ω (● m) = Vec.lookup∘update v h m
...   | no v′≢v rewrite Vec.lookup∘update′ v′≢v h m | Vec.lookup∘update′ v′≢v ω (● m) with Vec.lookup v′ ω
...     | ● n = equiv-v′
...     | ○ with Vec.lookup v′ ρ
...       | ● n = equiv-v′
...       | ○ = equiv-v′

Commit-Update : ∀ {h′ h l} → let open Logs l in
  Consistent h l → Equivalent h l h′ → h′ ≡ Update h l
Commit-Update {h′} {h} {l} cons equiv = Equivalence.to Vec.Pointwise-≡ ⟨$⟩ Vec.Pointwise.ext h′≗hω where
  open import Function.Equality using (_⟨$⟩_)
  open Logs l
  h′≗hω : ∀ v → Vec.lookup v h′ ≡ Vec.lookup v (Update h l)
  h′≗hω v rewrite Vec.lookup∘tabulate (λ v → Maybe.from (Vec.lookup v h) (Vec.lookup v ω)) v with Vec.lookup v ω | equiv v
  ... | ● m | equiv-v = equiv-v
  ... | ○   | equiv-v with Vec.lookup v ρ | ≡.inspect (Vec.lookup v) ρ
  ...   | ● m | [ ρ[v]≡m ] = ≡.trans equiv-v (≡.sym (cons v m ρ[v]≡m))
  ...   | ○   | _ = equiv-v

Update-Equivalent : ∀ {h l} → Consistent h l → Equivalent h l (Update h l)
Update-Equivalent {h} {l} cons v = ≡.trans (Vec.lookup∘tabulate _ v) update-v where
  open Logs l
  update-v : maybe id (Vec.lookup v h) (Vec.lookup v (Logs.ω l)) ≡ snd (Read h l v)
  update-v with Vec.lookup v ω
  ... | ● m = ≡.refl
  ... | ○ with Vec.lookup v ρ | ≡.inspect (Vec.lookup v) ρ
  ...   | ● m | [ ρ[v]≡m ] = cons v m ρ[v]≡m
  ...   | ○   | _ = ≡.refl

{-
Commit-Update′ : ∀ {h′ h l} → let open Logs l in
  Consistent h l → Equivalent h l h′ ⇔ h′ ≡ Update h l
Commit-Update′ {h′} {h} {l} cons equiv = {!Equivalence.to Vec.Pointwise-≡ ⟨$⟩ Vec.Pointwise.ext h′≗hω!} where
  open import Function.Equality using (_⟨$⟩_)
  open Logs l
  h′≗hω : ∀ v → Vec.lookup v h′ ≡ Vec.lookup v (Update h l)
  h′≗hω v rewrite Vec.lookup∘tabulate (λ v → Maybe.from (Vec.lookup v h) (Vec.lookup v ω)) v with Vec.lookup v ω | equiv v
  ... | ● m | equiv-v = equiv-v
  ... | ○   | equiv-v with Vec.lookup v ρ | ≡.inspect (Vec.lookup v) ρ
  ...   | ● m | [ ρ[v]≡m ] = ≡.trans equiv-v (≡.sym (cons v m ρ[v]≡m))
  ...   | ○   | _ = equiv-v
-}

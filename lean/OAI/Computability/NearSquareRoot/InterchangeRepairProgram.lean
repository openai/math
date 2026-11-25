import OAI.Computability.NearSquareRoot.InterchangeRepairSchedule

/-!
# The Hermite repair schedule on finite banks of records

The same accounting proof applies to time certificates and to bounded
stack executions. Sequencing adds the costs of both runs. Forking
also adds both costs and retains their outputs in separate registers.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace Interchange.RepairProgram

open RepairSchedule SwapRepair OAI.LinearAlgebra.FiniteFourier Matrix

variable {I A B C E : Type} {X : I → Type}

/-- A row family has finite register types and one common address type on each input. -/
abbrev Values (X : I → Type) (A E : Type) := (i : I) → A → X i → E

abbrev Relation (X : I → Type) (E : Type) :=
  ∀ {A B : Type}, ℕ → Values X A E → Values X B E → Prop

def both (x : Values X A E) (y : Values X B E) : Values X (A ⊕ B) E :=
  fun i => Sum.elim (x i) (y i)

/-- Local finite tables and the three register operations required by the repair.
Each concrete backend discharges these laws on its physical bank representation. -/
structure Rules (R : Relation X E) : Prop where
  table {A B : Type} [Fintype A] [Fintype B] [Nonempty A] (x : Values X A E) (f : (A → E) → B → E) :
    R 0 x (fun i b k => f (fun a => x i a k) b)
  seq {A B C : Type} [Fintype B] {x : Values X A E} {y : Values X B E} {z : Values X C E}
    {p q : ℕ} : R p x y → R q y z → R (p+q) x z
  fork {A B C : Type} [Fintype B] [Fintype C] {x : Values X A E} {y : Values X B E}
    {z : Values X C E} {p q : ℕ} : R p x y → R q x z → R (p+q) x (both y z)
  keep {A B : Type} [Fintype A] [Fintype B] {x : Values X A E} {y : Values X B E}
    {p : ℕ} : R p x y → R p x (both x y)
  empty {A B : Type} [IsEmpty B] (x : Values X A E) (y : Values X B E) : R 0 x y

abbrev Rows (L : Type) (n : ℕ) := L × Fin n

def flatten {K L : Type} [Field K] {n m : ℕ} (x : (i : I) → Data K L (X i) n m) :
    Values X (Rows L n) (Coeff K m) := fun i t => x i t.1 t.2

variable {K L : Type} [Field K] [Fintype L] {m : ℕ}
variable {R : Relation X (Coeff K m)} (machine : Rules R)

abbrev Mask (R : Relation X (Coeff K m)) (tag : (i : I) → X i → Pattern m) : Prop :=
  ∀ {S U : Type} [Fintype S] [Fintype U] [Nonempty S] (v : Values X S (Coeff K m))
    (f : Pattern m → (S → Coeff K m) → U → Coeff K m),
    R 0 v (fun i t a => f (tag i a) (fun k => v i k a) t)

abbrev Sweeps (R : Relation X E) (price : ℕ) (F : (i : I) → (X i → E) → X i → E) : Prop :=
  ∀ {S : Type} [Fintype S] (x : Values X S E), R (Fintype.card S * price) x (fun i s => F i (x i s))

include machine
private theorem mix {S : Type} [Fintype S] [Nonempty S] {n s : ℕ} (H : Matrix (Fin s) (Fin n) (Coeff K m))
    (v : Values X S (Coeff K m)) (sel : Rows L n → S) :
    R 0 v
      (flatten (fun i w => repairMixRows H (fun k => v i (sel (w,k))))) := by
  let f (u : S → Coeff K m) (t : Rows L s) := ∑ k, H t.2 k * u (sel (t.1,k))
  have h := machine.table v f
  convert h using 2
  funext t a
  simp [flatten, f, repairMixRows, Finset.sum_apply]

private theorem select {S U : Type} [Fintype S] [Fintype U] [Nonempty S] (v : Values X S (Coeff K m))
    (sel : U → S) : R 0 v (fun i t => v i (sel t)) :=
  machine.table v (fun u t => u (sel t))

private instance width_ne_zero : NeZero (width m) :=
  ⟨by unfold width primePredictorRows SwapRepair.order countPencilOrder; positivity⟩

private theorem checked [Nonempty L] (e : Environment K m) (T : Table K m)
    (tag : (i : I) → X i → Pattern m) (mask : Mask R tag)
    (F G : (i : I) → (X i → Coeff K m) → X i → Coeff K m)
    (paid : ℕ)
    (hf : Sweeps R paid F)
    (hg : Sweeps R paid G)
    (x px : (i : I) → Data K L (X i) (width m) m) :
    let H := repairCheck e.nodes (checks m)
    let t i := checksTable T (tag i) (F i) (G i)
      (fun w => repairMixRows H (px i w)) (fun w => repairMixRows H (x i w))
    R (4 * Fintype.card L * checks m * paid)
      (both (flatten x) (flatten px)) (both (flatten (fun i => (t i).1)) (flatten (fun i => (t i).2))) := by
  intro H t
  let S := Rows L (checks m)
  let b := both (flatten x) (flatten px)
  let c := both (flatten (fun i w => repairMixRows H (px i w)))
    (flatten (fun i w => repairMixRows H (x i w)))
  have h₁ : R 0 b c :=
    machine.fork (mix machine H b Sum.inr) (mix machine H b Sum.inl)
  let v i (k : S ⊕ S) := F i (c i k)
  have h₂ := hf c
  let lookup (t : Pattern m) (u : S ⊕ S → Coeff K m) (w : L) :=
    T t (fun k => u (.inl (w,k)), fun k => u (.inr (w,k)))
  let τ t u : S ⊕ S → Coeff K m := Sum.elim
    (fun z => (lookup t u z.1).1 z.2) (fun z => (lookup t u z.1).2 z.2)
  let y i z a := τ (tag i a) (fun k => v i k a) z
  have h₃ : R 0 v y := by
    by_cases hS : Nonempty (S ⊕ S)
    · exact mask v τ
    · have : IsEmpty (S ⊕ S) := not_nonempty_iff.mp hS
      exact machine.empty v y
  have h₄ := hg y
  have h := machine.seq (machine.seq (machine.seq h₁ h₂) h₃) h₄
  have price : 0 + Fintype.card (S ⊕ S) * paid + 0 + Fintype.card (S ⊕ S) * paid =
      4 * Fintype.card L * checks m * paid := by
    simp only [S, Rows, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; ring
  rw [price] at h
  convert h using 2
  funext z a
  cases z <;> rfl

/-- Execute the four predictors and the four check-row sweeps, retaining each
intermediate exactly where its later use requires it. `paid` is the cost of
one complete conversion of one extension row, including its basis components. -/
theorem execute [Nonempty L] (e : Environment K m) (T : Table K m)
    (tag : (i : I) → X i → Pattern m) (mask : Mask R tag)
    (F G : (i : I) → (X i → Coeff K m) → X i → Coeff K m)
    (P : (i : I) → Data K L (X i) (width m) m → Data K L (X i) (width m) m)
    (pred paid : ℕ)
    (hp : ∀ x, R pred (flatten x) (flatten fun i => P i (x i)))
    (hf : Sweeps R paid F)
    (hg : Sweeps R paid G)
    (x : (i : I) → Data K L (X i) (width m) m) :
    R (4 * pred + 4 * Fintype.card L * checks m * paid)
      (flatten x) (flatten (fun i => schedule e T (tag i) (F i) (G i) (P i) (x i))) := by
  let H := repairCheck e.nodes (checks m)
  let px i := P i (x i)
  let t i := checksTable T (tag i) (F i) (G i)
    (fun w => repairMixRows H (px i w)) (fun w => repairMixRows H (x i w))
  let old := both (flatten x) (flatten px)
  let hist := both old (both (flatten (fun i => (t i).1)) (flatten (fun i => (t i).2)))
  have seed := machine.keep (hp x)
  have table := machine.keep (checked machine e T tag mask F G paid hf hg x px)
  have cube₀ : R 0 hist (flatten px) :=
    select machine hist (fun t => Sum.inl (.inr t))
  have cube := machine.seq (machine.seq cube₀ (hp px)) (hp fun i => P i (px i))
  let z₀ i w := repairMixRows Hᵀ ((t i).1 w)
  have corr₀ : R 0 hist (flatten z₀) :=
    mix machine Hᵀ hist (fun t => Sum.inr (.inl t))
  have corr := machine.seq corr₀ (hp z₀)
  have pair := machine.keep (machine.fork cube corr)
  let all := both hist (both (flatten (fun i => P i (P i (px i)))) (flatten (fun i => P i (z₀ i))))
  let W := Rows L (width m)
  let S := Rows L (checks m)
  let finish (u : (((W ⊕ W) ⊕ (S ⊕ S)) ⊕ (W ⊕ W)) → Coeff K m) (t : Rows L (width m)) :=
    let px := u (.inl (.inl (.inr t)))
    let cube := u (.inr (.inl t))
    let corr := u (.inr (.inr t))
    px - e.invRadix * (cube - px) - corr + ∑ k, Hᵀ t.2 k * u (.inl (.inr (.inr (t.1,k))))
  have done' : R 0 all
      (flatten (fun i => schedule e T (tag i) (F i) (G i) (P i) (x i))) := by
    have h := machine.table all finish
    convert h using 2
    funext row a
    simp [all, hist, old, both, flatten, finish, schedule, t, px, z₀, H, repairMixRows,
      Finset.sum_apply]
  have run := machine.seq (machine.seq (machine.seq seed table) pair) done'
  convert run using 1
  ring

end Interchange.RepairProgram

end

end NearSquareRoot
end Computability
end OAI

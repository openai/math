import OAI.ThreeFlat.Routing.TypedWiring
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Composition and size of deterministic spill compaction

Each halving tests the graph of a partial function on bit arrays. Gluing two
stages sums the intermediate array exactly once when both packed outputs
exist. The total charge for a sequence of halvings telescopes, even when
some intermediate banks shrink by more than a factor of two.
-/

noncomputable section
open scoped Classical BigOperators

namespace ThreeFlat.Routing.Spill

universe u

/-- A checked transformation between two finite arrays of pins. Failure of
the transformation gives coefficient zero for every proposed output. -/
structure Stage (F : Type*) [CommSemiring F] (A B : Type u) [Fintype A] [Fintype B] where
  network : BitNetwork F (Fintype.card (A ⊕ B))
  run : (A → Bool) → Option (B → Bool)
  checked : ∀ input output, TypedWiring.value network (Sum.elim input output) =
    if run input = some output then 1 else 0

namespace Stage

variable {F : Type*} [CommSemiring F] {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]

private def port (A B C : Type u) : Bool → Type u
  | false => A ⊕ B
  | true => B ⊕ C

private instance (g : Bool) : Fintype (port A B C g) := by
  cases g <;> unfold port <;> infer_instance

private def wire : (g : Bool) → port A B C g → (A ⊕ C) ⊕ B
  | false, .inl a => .inl (.inl a)
  | false, .inr b => .inr b
  | true, .inl b => .inr b
  | true, .inr c => .inl (.inr c)

private def modules (s : Stage F A B) (t : Stage F B C) :
    (g : Bool) → BitNetwork F (Fintype.card (port A B C g))
  | false => s.network
  | true => t.network

/-- Contract the entire intermediate array over shared hidden bits. -/
def compose (s : Stage F A B) (t : Stage F B C) : Stage F A C where
  network := TypedWiring.glue (modules s t) wire
  run x := (s.run x).bind t.run
  checked x z := by
    rw [TypedWiring.glue_value]
    have factor (y : B → Bool) :
        (∏ g : Bool, TypedWiring.value (modules s t g)
          (fun k => Sum.elim (Sum.elim x z) y (wire g k))) =
          (if s.run x = some y then 1 else 0) * (if t.run y = some z then 1 else 0) := by
      have left : (fun k => Sum.elim (Sum.elim x z) y (wire false k)) = Sum.elim x y := by
        funext k; cases k <;> rfl
      have right : (fun k => Sum.elim (Sum.elim x z) y (wire true k)) = Sum.elim y z := by
        funext k; cases k <;> rfl
      simp only [Fintype.prod_bool, left, right, modules, mul_comm]
      exact congrArg₂ (· * ·) (s.checked x y) (t.checked y z)
    simp_rw [factor]
    cases h : s.run x with
    | none => simp
    | some y =>
      rw [Finset.sum_eq_single y]
      · simp
      · intro k _ ne
        simp [Ne.symm ne]
      · simp

@[simp] theorem compose_cells (s : Stage F A B) (t : Stage F B C) :
    (compose s t).network.cells = s.network.cells + t.network.cells := by
  simp [compose, modules, Nat.add_comm]

@[simp] theorem compose_run (s : Stage F A B) (t : Stage F B C) (x : A → Bool) :
    (compose s t).run x = (s.run x).bind t.run := rfl

private def reject : Stage F A B where
  network := TypedWiring.localTable (fun _ => 0)
  run _ := none
  checked := by intro input output; simp [TypedWiring.localTable_value]

variable (P : ℕ → Type u) [∀ i, Fintype (P i)]
  (step : ∀ i, Stage F (P i) (P (i+1)))

/-- Compose the first `k+1` transformations. -/
def chain : (k : ℕ) → Stage F (P 0) (P (k+1))
  | 0 => step 0
  | k+1 => (chain k).compose (step (k+1))

/-- Stage-wise legality provides a successful output for the entire packing
chain. A uniform upper bound on the active count is one such invariant. -/
theorem chain_complete (k : ℕ) (legal : ∀ i, (P i → Bool) → Prop)
    (complete : ∀ i ≤ k, ∀ b, legal i b → ∃ c, (step i).run b = some c ∧ legal (i+1) c)
    (a : P 0 → Bool) (ha : legal 0 a) :
    ∃ z, (chain P step k).run a = some z ∧ legal (k+1) z := by
  induction k with
  | zero => exact complete 0 le_rfl a ha
  | succ k ih =>
    obtain ⟨b,hb,hl⟩ := ih (fun i hi => complete i (Nat.le_succ_of_le hi))
    obtain ⟨z,hz,hz'⟩ := complete (k+1) le_rfl b hl
    exact ⟨z, by simp [chain, hb, hz], hz'⟩

/-- A successful chain preserves every common readout preserved by its
individual stages, including the multiset of occupied payloads. -/
theorem chain_preserves {T : Type*} (k : ℕ) (readout : ∀ i, (P i → Bool) → T)
    (preserve : ∀ i ≤ k, ∀ b c, (step i).run b = some c → readout (i+1) c = readout i b)
    (a : P 0 → Bool) (z : P (k+1) → Bool) (ok : (chain P step k).run a = some z) :
    readout (k+1) z = readout 0 a := by
  induction k with
  | zero => exact preserve 0 le_rfl a z ok
  | succ k ih =>
    rw [chain, compose_run] at ok
    cases he : (chain P step k).run a with
    | none => simp [he] at ok
    | some b =>
      have last : (step (k+1)).run b = some z := by simpa [he] using ok
      exact (preserve (k+1) le_rfl b z last).trans
        (ih (fun i hi => preserve i (Nat.le_succ_of_le hi)) b he)

private theorem chain_last (k : ℕ) (a : P 0 → Bool) (z : P (k+1) → Bool)
    (ok : (chain P step k).run a = some z) :
    ∃ b, (step k).run b = some z := by
  cases k with
  | zero => exact ⟨a,ok⟩
  | succ k =>
    rw [chain,compose_run] at ok
    cases he : (chain P step k).run a with
    | none => simp [he] at ok
    | some b => exact ⟨b,by simpa [he] using ok⟩

/-- The terminal bank is still credited at the per-slot rate. This invariant
gives a bound by the initial capacity independent of the number of stages. -/
theorem chain_cells_budget (k : ℕ) (cap : ℕ → ℕ) (charge : ℕ)
    (cost : ∀ i ≤ k, (step i).network.cells ≤ cap (i+1) * charge)
    (shrink : ∀ i ≤ k, 2 * cap (i+1) ≤ cap i) :
    (chain P step k).network.cells + cap (k+1) * charge ≤ cap 0 * charge := by
  induction k with
  | zero =>
    have hs := Nat.mul_le_mul_right charge (shrink 0 le_rfl)
    have hc := cost 0 le_rfl
    rw [Nat.mul_assoc] at hs
    simp only [Nat.zero_add] at hs hc
    change (step 0).network.cells + cap 1 * charge ≤ cap 0 * charge
    omega
  | succ k ih =>
    have prev := ih (fun i hi => cost i (Nat.le_succ_of_le hi))
      (fun i hi => shrink i (Nat.le_succ_of_le hi))
    have hs := Nat.mul_le_mul_right charge (shrink (k+1) le_rfl)
    have hc := cost (k+1) le_rfl
    rw [Nat.mul_assoc] at hs
    rw [chain,compose_cells]
    omega

/-- Concrete dyadic capacities ending at `last`. In particular, substituting
`charge = c * (u+n)` bounds the full compaction cost at that per-slot rate. -/
theorem chain_cells_dyadic (k last charge : ℕ)
    (cost : ∀ i ≤ k, (step i).network.cells ≤ 2^(k-i) * last * charge) :
    (chain P step k).network.cells + last * charge ≤ 2^(k+1) * last * charge := by
  let cap := fun i : ℕ => 2^(k+1-i) * last
  have h := chain_cells_budget P step k cap charge (fun i hi => by
    simpa [cap] using cost i hi) (fun i hi => by
      have hk : k+1-i = (k-i)+1 := by omega
      simp [cap,hk,pow_succ,Nat.mul_comm,Nat.mul_left_comm])
  simpa [cap] using h

/-- It suffices to realize the finitely many stage sizes occurring in the
actual schedule. The resulting checked stage is complete for the stated
legal inputs, and every successful run preserves the chosen readout. -/
theorem exists_finite_chain {T : Type*} (k last charge : ℕ)
    (legal : ∀ i, (P i → Bool) → Prop) (readout : ∀ i, (P i → Bool) → T)
    (canonical : ∀ i, (P i → Bool) → Prop)
    (stages : ∀ i ≤ k, ∃ s : Stage F (P i) (P (i+1)),
      s.network.cells ≤ 2^(k-i)*last*charge ∧
      (∀ a, legal i a → ∃ b, s.run a = some b ∧ legal (i+1) b) ∧
      ∀ a b, s.run a = some b → readout (i+1) b = readout i a ∧ canonical (i+1) b) :
    ∃ s : Stage F (P 0) (P (k+1)),
      s.network.cells + last*charge ≤ 2^(k+1)*last*charge ∧
      (∀ a, legal 0 a → ∃ b, s.run a = some b ∧ legal (k+1) b) ∧
      ∀ a b, s.run a = some b → readout (k+1) b = readout 0 a ∧ canonical (k+1) b := by
  let s (i : ℕ) : Stage F (P i) (P (i+1)) := if hi : i ≤ k then (stages i hi).choose else reject
  have ok (i) (hi : i ≤ k) : (s i).network.cells ≤ 2^(k-i)*last*charge ∧
      (∀ a, legal i a → ∃ b, (s i).run a = some b ∧ legal (i+1) b) ∧
      ∀ a b, (s i).run a = some b → readout (i+1) b = readout i a ∧ canonical (i+1) b := by
    simpa only [s,dite_eq_left hi] using (stages i hi).choose_spec
  refine ⟨chain P s k,chain_cells_dyadic P s k last charge (fun i hi => (ok i hi).1),
    chain_complete P s k legal (fun i hi => (ok i hi).2.1),?_⟩
  intro a z h
  obtain ⟨b,hb⟩ := chain_last P s k a z h
  exact ⟨chain_preserves P s k readout (fun i hi a b hs => ((ok i hi).2.2 a b hs).1) a z h,
    ((ok k le_rfl).2.2 b z hb).2⟩

end Stage

/-- Pad an integer input size to a dyadic multiple of the desired last bank.
The initial padded bank is smaller than twice the actual candidate count. -/
theorem exists_dyadic_padding {last candidates : ℕ} (hp : 0 < last) (hle : last ≤ candidates) :
    ∃ k : ℕ, candidates ≤ 2^k * last ∧ 2^k * last < 2*candidates := by
  have existsPower : ∃ k : ℕ, candidates ≤ 2^k * last :=
    ⟨Nat.log 2 candidates + 1, (Nat.lt_pow_succ_log_self (by decide) candidates).le.trans
      (Nat.le_mul_of_pos_right _ hp)⟩
  let k := Nat.find existsPower
  refine ⟨k, Nat.find_spec existsPower, ?_⟩
  cases hk : k with
  | zero => simp; omega
  | succ j =>
    have hj : j < Nat.find existsPower := by change j < k; omega
    have hsmall : 2^j * last < candidates := Nat.lt_of_not_ge (Nat.find_min existsPower hj)
    rw [pow_succ',Nat.mul_assoc]
    omega

/-- The spill estimate leaves half the slots free in the final bank, and
hence also at every earlier halving. -/
theorem spill_fits_last_bank {n N active : ℕ} (hn : 2 ≤ n) (hs : active ≤ N / n^5) :
    2*active ≤ N / n^4 := by
  have hpos : 0 < n^4 := Nat.pow_pos (by omega)
  apply (Nat.le_div_iff_mul_le hpos).2
  calc
    2*active*n^4 ≤ n*(N/n^5)*n^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul hn hs)
    _ = (N/n^5)*n^5 := by rw [pow_succ n 4]; ac_rfl
    _ ≤ N := Nat.div_mul_le_self _ _

end ThreeFlat.Routing.Spill

end
end OAI

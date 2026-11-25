import OAI.Computability.BorderVNP.CrossingSignedLookup

/-!
# Counting the occupied fermion modes in Boolean circuits

Each layer reads one occupancy bit. A one-hot counter either stays in place or shifts by a
fixed nonnegative weight. This computes the doubled energy used in the shift test and the
occupation parities used in the signs, with one circuit for all possible occupation masks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.MaskCounter

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open scoped BigOperators

/-- The occupancy bits for a Fock space matrix index. -/
def mask {L : ℕ} (A : Index L) (i : Fin L) : Bool := decide (i.val ∈ A.val)

/-- The natural-number total of the weights at the set occupancy bits. -/
def total {L : ℕ} (w : Fin L → ℕ) (x : Fin L → Bool) : ℕ := ∑ i, if x i then w i else 0

private abbrev Ports (L B : ℕ) := Fin L ⊕ Fin (B+1)

private def partialTotal {L : ℕ} (w : Fin L → ℕ) (x : Fin L → Bool) (t : ℕ) :=
  ∑ i ∈ Finset.range t, if h : i < L then if x ⟨i,h⟩ then w ⟨i,h⟩ else 0 else 0

private def initial {L B : ℕ} : Ports L B → Expr (Fin L)
  | .inl i => .input i
  | .inr j => .const (decide (0 = j.val))

private def layer {L B : ℕ} (w : Fin L → ℕ) (t : ℕ) : Ports L B → Expr (Ports L B)
  | .inl i => .input (.inl i)
  | .inr j =>
    if h : t < L then
      let a := w ⟨t,h⟩
      let prev := if a ≤ j.val then .input (.inr ⟨j.val-a, by omega⟩) else .const false
      Expr.mux (.input (.inl ⟨t,h⟩)) prev (.input (.inr j))
    else .input (.inr j)

private noncomputable def scan {L : ℕ} (B : ℕ) (w : Fin L → ℕ) (t : ℕ) : Frame (Fin L) (Ports L B) :=
  ((Frame.initial id).step initial).steps (layer w) t

private theorem scan_eval {L : ℕ} (B : ℕ) (w : Fin L → ℕ) (t : ℕ) (x : Fin L → Bool) :
    (∀ i, (scan B w t).eval x (.inl i) = x i) ∧
    ∀ j, (scan B w t).eval x (.inr j) = decide (partialTotal w x t = j.val) := by
  induction t with
  | zero =>
    constructor
    · intro i; simp [scan, initial, Expr.eval]
    · intro j; simp [scan, partialTotal, initial, Expr.eval]; rfl
  | succ t ih =>
    have hs : scan B w (t+1) = (scan B w t).step (layer w t) := rfl
    constructor
    · intro i
      simpa [hs, layer, Expr.eval] using ih.1 i
    · intro j
      rw [hs, Frame.step_eval]
      have hp : partialTotal w x (t+1) = partialTotal w x t +
        (if h : t < L then if x ⟨t,h⟩ then w ⟨t,h⟩ else 0 else 0) := Finset.sum_range_succ _ _
      rw [hp]
      by_cases ht : t < L
      · cases hx : x ⟨t,ht⟩ <;> simp [layer, ht, hx, Expr.eval, ih.1, ih.2]
        split_ifs with h <;> simp only [Expr.eval, ih.2] <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega
      · simp [layer, ht, Expr.eval, ih.2]

/-- One-hot weighted sum up to a specified output bound. -/
noncomputable def counters {L : ℕ} (B : ℕ) (w : Fin L → ℕ) : Frame (Fin L) (Fin (B+1)) :=
  (scan B w L).select Sum.inr

/-- Every output tests the claimed value of the weighted sum. -/
theorem counters_eval {L : ℕ} (B : ℕ) (w : Fin L → ℕ) (x : Fin L → Bool) (j : Fin (B+1)) :
    (counters B w).eval x j = decide (total w x = j.val) := by
  rw [counters, Frame.select_eval, (scan_eval B w L x).2]
  exact congrArg (fun v => decide (v = j.val)) (Finset.sum_fin_eq_sum_range (fun i => if x i then w i else 0)).symm

/-- Polynomial gate bound for a scan. -/
theorem counters_size {L : ℕ} (B : ℕ) (w : Fin L → ℕ) :
    (counters B w).size ≤ (L+B+1) + L*((L+B+1)*8) := by
  let first : Frame (Fin L) (Ports L B) := (Frame.initial id).step initial
  have hi : first.size ≤ L+B+1 := by
    have h := Frame.step_size_le (Frame.initial id) (initial (L := L) (B := B)) 1
      (by rintro (i|i) <;> rfl)
    simpa [first, Ports, Nat.add_assoc] using h
  have hs := Frame.steps_size_le first (layer w) L 8 (by
    intro t ht p
    cases p with
    | inl i => change 1 ≤ 8; decide
    | inr j =>
      by_cases hj : w ⟨t,ht⟩ ≤ j.val <;> simp [layer, ht, hj, Expr.mux, Expr.size])
  simp only [Ports, Fintype.card_sum, Fintype.card_fin, ← Nat.add_assoc] at hs
  exact hs.trans (Nat.add_le_add_right hi _)

/-- The weighted counter computes a sum over the actual occupied modes. -/
theorem total_index {L : ℕ} (w : ℕ → ℕ) (A : Index L) :
    total (fun i : Fin L => w i) (mask A) = ∑ i ∈ A.val, w i := by
  rw [total, Finset.sum_fin_eq_sum_range]
  have he : A.val = (Finset.range L).filter (· ∈ A.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨Finset.mem_range.mp ((Finset.mem_powerset.mp A.property) h), h⟩, And.right⟩
  conv_rhs => rw [he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi, mask]

/-- The one-hot doubled-energy circuit for a mask of `L` modes. -/
noncomputable def energy (L : ℕ) : Frame (Fin L) (Fin (L*(2*L+1)+1)) :=
  counters _ fun i => 2*i.val+1

/-- The natural-valued energy used by the integral field modes. -/
theorem energy_eval {L : ℕ} (A : Index L) (j : Fin (L*(2*L+1)+1)) :
    (energy L).eval (mask A) j = decide (doubledEnergy A.val = j.val) := by
  rw [energy, counters_eval, total_index (fun i => 2*i+1)]
  rfl

/-- Parity of the selected occupied modes, used for insertion and deletion signs. -/
noncomputable def parity {L : ℕ} (pick : Fin L → Bool) : Frame (Fin L) Unit :=
  (counters L (fun i => (pick i).toNat)).step (fun _ =>
    Expr.disjoin (Finset.univ.toList.map fun j : Fin (L+1) => if j.val % 2 = 1 then .input j else .const false))

/-- The selected population fits in the `L + 1` counter cells. -/
private theorem population_bound {L : ℕ} (pick x : Fin L → Bool) :
    total (fun i => (pick i).toNat) x ≤ L := by
  have h : ∀ i : Fin L, (if x i then (pick i).toNat else 0) ≤ 1 := fun i => by cases x i <;> cases pick i <;> decide
  calc
    _ ≤ ∑ _ : Fin L, 1 := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

/-- The parity circuit outputs the oddness of the selected population. -/
theorem parity_eval {L : ℕ} (pick x : Fin L → Bool) :
    (parity pick).eval x () = decide (total (fun i => (pick i).toNat) x % 2 = 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [parity, Frame.step_eval, Expr.eval_disjoin_true, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨j,rfl⟩, hj⟩
    split_ifs at hj with h
    · rw [Expr.eval, counters_eval, decide_eq_true_eq] at hj
      rw [hj, h]
    · contradiction
  · intro h
    let j : Fin (L+1) := ⟨_, Nat.lt_succ_of_le (population_bound pick x)⟩
    refine ⟨_, ⟨j,rfl⟩, ?_⟩
    rw [ite_eq_left (show j.val % 2 = 1 from h), Expr.eval, counters_eval]
    simp [j]

/-- Oddness of an arbitrary predicate restricted to the actual source state. -/
theorem parity_eval_index {L : ℕ} (pick : ℕ → Bool) (A : Index L) :
    (parity (fun i : Fin L => pick i)).eval (mask A) () =
      decide ((A.val.filter (fun i => pick i)).card % 2 = 1) := by
  rw [parity_eval, total_index (fun i => (pick i).toNat), Finset.card_filter]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  cases pick i <;> rfl

/-- Polynomial gate bound for all parity tests. -/
theorem parity_size {L : ℕ} (pick : Fin L → Bool) :
    (parity pick).size ≤ (L+L+1) + L*((L+L+1)*8) + (L+1)*2+1 := by
  have hs := Frame.step_size_le (counters L (fun i => (pick i).toNat)) (ρ := Unit)
    (fun _ => Expr.disjoin (Finset.univ.toList.map fun j : Fin (L+1) => if j.val % 2 = 1 then .input j else .const false))
    ((L+1)*2+1) (by
      intro _
      apply (Expr.size_disjoin_le _ 1 ?_).trans
      · simp
      · intro e he
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
        split_ifs <;> rfl)
  simp only [Fintype.card_unit, one_mul] at hs
  exact hs.trans (by have := counters_size L (fun i => (pick i).toNat); omega)

end Crossing.Signed.MaskCounter

end BorderVNP
end Computability
end OAI

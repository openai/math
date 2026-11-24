import OAI.Computability.VPVNP.CutSchedule

/-!
# Accumulating the nominated production and gadget exponents

At each live first-half cut, the program checks the primed exterior bits
and the new cumulative exponents against the preceding cut. Section 14.1
requires that a fixed sequence of pair paths determine exactly one sequence
of cut strings, with zero initial exponents and zero padding. Here `inc`
combines both kinds of label counters in the order used by the evaluator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExponentTrace

open CutSchedule

/-- Fixed-width RAM word used to store a cumulative label exponent. -/
abbrev Word := BurstRAM.Word

variable {Label : Type*} {p : ℕ}

private def extended (inc : Fin p → Label → ℕ) (i : ℕ) (a : Label) : ℕ :=
  if h : i < p then inc ⟨i, h⟩ a else 0

/-- Sum of the per-pair increments before a given cut. -/
def partialSum (inc : Fin p → Label → ℕ) (j : Fin (p + 1)) (a : Label) : ℕ :=
  ∑ i ∈ Finset.range j.val, extended inc i a

@[simp] theorem prefix_zero (inc : Fin p → Label → ℕ) (a : Label) : partialSum inc 0 a = 0 := by
  simp [partialSum]

theorem prefix_step (inc : Fin p → Label → ℕ) (j : Fin p) (a : Label) :
    partialSum inc j.succ a = partialSum inc j.castSucc a + inc j a := by
  simp [partialSum, Finset.sum_range_succ, extended, j.isLt]

theorem prefix_last (inc : Fin p → Label → ℕ) (a : Label) :
    partialSum inc (Fin.last p) a = ∑ i, inc i a := by
  rw [partialSum, Fin.val_last, ← Fin.sum_univ_eq_sum_range]
  simp [extended]

/-- A complete sequence of first-half cuts has one binary word for every
nonempty cut numbered `i+1` with `i < 2^h`. -/
abbrev LiveBits (h Δ : ℕ) := (i : Fin (2 ^ h)) → Bits (width (h + 1) Δ (i.val + 1))

/-- Primed exterior cuts, including the two empty endpoint strings. -/
abbrev Exterior (h Δ : ℕ) :=
  (j : Fin (2 ^ h + 1)) → Bits (width (h + 1) Δ (2 * j.val))

variable {h Δ t Z : ℕ} (hfit : 1 + t * Z ≤ Δ)

private def fields (i : Fin (2 ^ h)) :=
  firstHalfLayout h Δ (i.val + 1) t Z (Nat.succ_pos _) i.isLt hfit

/-- Decode the running counters; before the first group all counters are zero. -/
def counters (live : LiveBits h Δ) : Fin (2 ^ h + 1) → Fin t → Word Z :=
  Fin.cons (fun _ => 0) (fun i => (fields hfit i (live i)).2.2.1)

/-- The local checks performed by each live pair group. The equality of
natural numbers enforces rejection on overflow. -/
def Valid (ξ : Exterior h Δ) (inc : Fin (2 ^ h) → Fin t → ℕ) (live : LiveBits h Δ) : Prop :=
  (∀ i, fields hfit i (live i) =
    (true, ξ i.succ, counters hfit live i.succ, fun _ => false)) ∧
  ∀ i a, (counters hfit live i.succ a).val = (counters hfit live i.castSucc a).val + inc i a

theorem counters_eq_prefix (ξ : Exterior h Δ) (inc : Fin (2 ^ h) → Fin t → ℕ) (live : LiveBits h Δ)
    (hv : Valid hfit ξ inc live) (j : Fin (2 ^ h + 1)) (a : Fin t) :
    (counters hfit live j a).val = partialSum inc j a := by
  induction j using Fin.induction with
  | zero => simp [counters]
  | succ i ih => rw [hv.2, ih, prefix_step]

/-- For any fixed exterior choices and local pair paths whose prefix sums fit,
the local checks admit exactly one binary first-half cut assignment. -/
theorem existsUnique_live (ξ : Exterior h Δ) (inc : Fin (2 ^ h) → Fin t → ℕ)
    (hbound : ∀ (i : Fin (2 ^ h)) a, partialSum inc i.succ a < 2 ^ Z) : ∃! live, Valid hfit ξ inc live := by
  let data (i : Fin (2 ^ h)) (a : Fin t) : Word Z := ⟨partialSum inc i.succ a, hbound i a⟩
  let live (i : Fin (2 ^ h)) := (fields hfit i).symm (true, ξ i.succ, data i, fun _ => false)
  have hf (i : Fin (2 ^ h)) : fields hfit i (live i) = (true, ξ i.succ, data i, fun _ => false) :=
    (fields hfit i).apply_symm_apply _
  have hcount (j : Fin (2 ^ h + 1)) (a : Fin t) : (counters hfit live j a).val = partialSum inc j a := by
    refine Fin.cases (by simp [counters]) (fun i => ?_) j
    simp [counters, hf, data]
  have hv : Valid hfit ξ inc live := by
    refine ⟨fun i => ?_, fun i a => ?_⟩
    · simp [counters, hf]
    · rw [hcount, hcount, prefix_step]
  refine ⟨live, hv, fun other ho => funext fun i => (fields hfit i).injective ?_⟩
  rw [ho.1, hf]
  congr 3
  funext a
  exact Fin.ext (counters_eq_prefix hfit ξ inc other ho i.succ a)

/-- Instantiation with the paper's `Z = 2H` exponent width, where `H=h+1`.
Every pair contributes less than `2^(2r)` to each label, even if later
cancellation gives zero after evaluating the term's gadget labels. -/
theorem firstHalf_no_overflow (h r : ℕ) (hr : 2 * r < h + 1)
    (inc : Fin (2 ^ h) → Label → ℕ) (hinc : ∀ i a, inc i a < 2 ^ (2 * r))
    (j : Fin (2 ^ h + 1)) (a : Label) : partialSum inc j a < 2 ^ (2 * (h + 1)) := by
  have hj : j.val ≤ 2 ^ h := Nat.lt_succ_iff.mp j.isLt
  apply accumulated_lt _ r _ (fun i => extended inc i a) (hj.trans (by rw [pow_succ]; omega)) hr
  intro i hi
  simp [extended, Nat.lt_of_lt_of_le hi hj, hinc]

/-- At the middle cut the exponent vector passed to the evaluator is the
sum of the increments for every primed pair. -/
theorem middle_counters (ξ : Exterior h Δ) (inc : Fin (2 ^ h) → Fin t → ℕ) (live : LiveBits h Δ)
    (hv : Valid hfit ξ inc live) (a : Fin t) :
    (counters hfit live (Fin.last (2 ^ h)) a).val = ∑ i, inc i a :=
  (counters_eq_prefix hfit ξ inc live hv _ a).trans (prefix_last inc a)

end ExponentTrace

end VPVNP
end Computability
end OAI

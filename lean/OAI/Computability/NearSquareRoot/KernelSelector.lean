import OAI.Computability.NearSquareRoot.InterchangeScan
import OAI.Computability.NearSquareRoot.ShortWordStack
import Mathlib.Data.ZMod.Basic

/-!
# Reading the column-dependent table selectors of a binary kernel

A template fixes its slots and the finite group of possible signatures. Each
slot tape holds its bits in column order. One synchronous read adds the
signature of the current column to the finite control. The final state
contains the sum, and every tape has its original contents and head position.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelSelector

open IntegerMultiplication
open InterchangeScan (Phase)

variable {I G : Type} [AddCommMonoid G]

/-- Scan until the right blank, then return past the leftmost bit to its
preceding blank. Only the forward scan updates the signature. -/
def rule (ref : I) (column : (I → Bool) → G) : TM.Rule (Option Bool) (Phase × G) I
  | (.forward, s), r =>
    if (r ref).isSome then
      some ((.forward, s + column (fun i => (r i).getD false)), fun i => (r i, .right))
    else some ((.rewind, s), fun i => (r i, .left))
  | (.rewind, s), r =>
    if (r ref).isSome then some ((.rewind, s), fun i => (r i, .left))
    else some ((.halt, s), fun i => (r i, .right))
  | (.halt, _), _ => none

/-- Position the heads at the first cell of an aligned tuple of bit slots. -/
def loaded {n : ℕ} (q : Phase × G) (x : Fin n → I → Bool) :
    TM.Config (Option Bool) (Phase × G) I :=
  ⟨q, fun i => TM.Tape.loaded none (List.ofFn fun j : Fin n => some (x j i))⟩

private def cell {n : ℕ} (x : Fin n → I → Bool) (z : ℤ) (i : I) : Option Bool :=
  if h : 0 ≤ z ∧ z.toNat < n then some (x ⟨z.toNat, h.2⟩ i) else none

private def snapshot {n : ℕ} (x : Fin n → I → Bool) (q : Phase × G) (p : ℤ) :
    TM.Config (Option Bool) (Phase × G) I :=
  ⟨q, fun i => ⟨p, fun k => cell x (p + k) i⟩⟩

omit [AddCommMonoid G] in
private theorem snapshot_zero {n : ℕ} (x : Fin n → I → Bool) (q : Phase × G) :
    snapshot x q 0 = loaded q x := by
  apply congrArg (TM.Config.mk q)
  funext i
  apply congrArg (TM.Tape.mk 0)
  funext z
  cases z with
  | ofNat z =>
    by_cases h : z < n <;> simp [cell, h]
  | negSucc z => simp [cell]

private theorem step_at {n : ℕ} (x : Fin n → I → Bool) (ref : I) (φ : (I → Bool) → G)
    (q q' : Phase × G) (p : ℤ) (d : TM.Move)
    (op : rule ref φ q (cell x p) = some (q', fun i => (cell x p i, d))) :
    TM.advance (rule ref φ) (snapshot x q p) = some (snapshot x q' (p+d.shift)) := by
  simp only [TM.advance, snapshot, add_zero, op, Option.map_some, Option.some.injEq,
    TM.Config.mk.injEq, true_and]
  funext i
  unfold TM.Tape.apply
  apply congrArg (TM.Tape.mk _)
  funext z
  change (if z + d.shift = 0 then cell x p i else cell x (p+(z+d.shift)) i) = cell x (p+d.shift+z) i
  split_ifs with hz
  · have e : p + d.shift + z = p := by omega
    rw [e]
  · rw [show p + (z + d.shift) = p + d.shift + z by omega]

private def partialSum {n : ℕ} (x : Fin n → I → Bool) (φ : (I → Bool) → G) (k : ℕ) : G :=
  ∑ j ∈ Finset.range k, if h : j < n then φ (x ⟨j,h⟩) else 0

private theorem partialSum_end {n : ℕ} (x : Fin n → I → Bool) (φ : (I → Bool) → G) :
    partialSum x φ n = ∑ j, φ (x j) := by
  exact (Finset.sum_fin_eq_sum_range (fun j => φ (x j))).symm

private theorem forward {n : ℕ} (x : Fin n → I → Bool) (ref : I) (φ : (I → Bool) → G)
    (k : ℕ) (hk : k ≤ n) :
    Trace (TM.advance (rule ref φ)) (snapshot x (.forward, 0) 0) k
      (snapshot x (.forward, partialSum x φ k) k) := by
  induction k with
  | zero =>
    simpa [partialSum] using (Trace.nil (step := TM.advance (rule ref φ)) (snapshot x (.forward, 0) 0))
  | succ k ih =>
    have h : k < n := hk
    refine (ih (by omega)).trans (.single ?_)
    have op := step_at x ref φ (.forward, partialSum x φ k) (.forward, partialSum x φ (k+1))
      k .right (by simp [rule, cell, h, partialSum, Finset.sum_range_succ])
    simpa [TM.Move.shift] using op

private theorem rewind {n : ℕ} (x : Fin n → I → Bool) (ref : I) (φ : (I → Bool) → G)
    (s : G) (k : ℕ) (hk : k ≤ n) :
    Trace (TM.advance (rule ref φ)) (snapshot x (.rewind, s) ((k:ℤ)-1)) (k+1)
      (snapshot x (.halt, s) 0) := by
  induction k with
  | zero =>
    apply Trace.single
    simpa [TM.Move.shift] using step_at x ref φ (.rewind, s) (.halt, s) (-1) .right
      (by simp [rule, cell])
  | succ k ih =>
    have h : k < n := hk
    have op := step_at x ref φ (.rewind, s) (.rewind, s) k .left (by simp [rule, cell, h])
    have one : Trace (TM.advance (rule ref φ)) (snapshot x (.rewind, s) k) 1
        (snapshot x (.rewind, s) ((k:ℤ)-1)) := .single (by simpa [TM.Move.shift, sub_eq_add_neg] using op)
    simpa [Nat.add_comm 1 (k+1)] using one.trans (ih (by omega))

/-- The returned control value is the sum of the prescribed column functions.
The full transition count includes the two end tests and every head rewind.
For a finite signature type and finite slot type this is one fixed finite
machine for all column counts. -/
theorem scan [Fintype I] (ref : I) (φ : (I → Bool) → G) {n : ℕ}
    (x : Fin n → I → Bool) :
    let start := loaded (.forward, (0 : G)) x
    let stop := loaded (.halt, ∑ j, φ (x j)) x
    Trace (TM.advance (rule ref φ)) start (2*n+2) stop ∧
    TM.advance (rule ref φ) stop = none ∧
    VisitsAtMost (rule ref φ) start (2*n+2) (Fintype.card I * (4*n+5)) := by
  let s := ∑ j, φ (x j)
  have forw := forward x ref φ n le_rfl
  rw [partialSum_end] at forw
  have turn := step_at x ref φ (.forward, s) (.rewind, s) n .left (by simp [rule, cell])
  have one : Trace (TM.advance (rule ref φ)) (snapshot x (.forward, s) n) 1
      (snapshot x (.rewind, s) ((n:ℤ)-1)) := .single (by simpa [TM.Move.shift, sub_eq_add_neg] using turn)
  have run := (forw.trans one).trans (rewind x ref φ s n le_rfl)
  rw [snapshot_zero, snapshot_zero, show n+1+(n+1) = 2*n+2 by omega] at run
  refine ⟨run, rfl, ?_⟩
  have fence := visitsAtMost_of_common_fence (m := rule ref φ)
    (init := loaded (.forward, (0 : G)) x) (steps := 2*n+2)
    (-(2*(n:ℤ)+2)) (2*n+2) (by
      intro t ht c hc i
      have h := head_excursion hc i
      simp only [loaded, TM.Tape.loaded, zero_sub, zero_add] at h
      omega)
  convert fence using 2
  omega

/-- Distinguished pair and auxiliary pairs in the binary Fourier query.
The selector is an element of `(ZMod 2)^m`; its components index the
spectral repair table. Spectator coordinates outside these slots never enter. -/
def queryColumn {m d : ℕ} (b : (Fin m ⊕ Fin d) × Bool → Bool) (j : Fin m) : ZMod 2 :=
  let pair (i : Fin m ⊕ Fin d) := (b (i,false)).toNat * (b (i,true)).toNat
  (pair (.inl j) : ZMod 2) + ∑ a : Fin d, (pair (.inr a) : ZMod 2)

/-- Simultaneously compute all binary quadratic query exponents on the
actual slot tapes, at the same transition count as a single query. -/
theorem scan_query {m d n : ℕ} (j₀ : Fin m)
    (x : Fin n → (Fin m ⊕ Fin d) × Bool → Bool) :
    let start := loaded (.forward, (0 : Fin m → ZMod 2)) x
    let stop := loaded (.halt, ∑ c, queryColumn (x c)) x
    let r := rule (Sum.inl j₀, false) (@queryColumn m d)
    Trace (TM.advance r) start (2*n+2) stop ∧
    TM.advance r stop = none ∧
    VisitsAtMost r start (2*n+2) ((2*(m+d))*(4*n+5)) := by
  simpa [Fintype.card_prod, Fintype.card_sum, mul_comm (m+d)] using
    scan (Sum.inl j₀, false) (@queryColumn m d) x

end KernelSelector

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.VPVNP.RAMTapeSortOffsetsCode
import OAI.Computability.VPVNP.StructuredStackLoop

/-!
# Visiting the physical rows of a sorting layer

A single finite routine visits the offsets in increasing order. The caller
can use the fixed-width binary row for the direction and partner tests and
the unary row to gather its record. The callback's other tape streams pass
from one visit to the next.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortOffsets

open BurstRAM UnaryWord TapeWord

variable {K : Type}

/-- Only the row width is occupied between successive traversals. -/
def idle (data : Stacks K) (h : ℕ) : Stacks (K ⊕ Port) :=
  Sum.elim data (store (ones h) [] [] [] [])

private def row (data : Stacks K) (h i : ℕ) (flag : List Bool) : Stacks (K ⊕ Port) :=
  Sum.elim data (store (ones h) (wordBits (Fin.ofNat (2^h) i)) (ones i) [] flag)

/-- The callback's ports at a physical row. The temporary and loop-flag stacks are empty. -/
def visit (data : Stacks K) {h : ℕ} (i : Fin (2^h)) : Stacks (K ⊕ Port) :=
  Sum.elim data (store (ones h) (wordBits i) (ones i.val) [] [])

private def part (q : Phase) : FiniteRoutine (K ⊕ Port) :=
  FiniteRoutine.ofStackCode code Sum.inr q (· == .done)

private def loop (body : FiniteRoutine (K ⊕ Port)) : FiniteRoutine (K ⊕ Port) :=
  FiniteRoutine.ofRoutine (Routine.popLoop (.inr Port.again) id Routine.ret
    (body.followedBy (part (.add true))).body)

/-- Fixed control independent of the input width, row count, and record size. -/
def routine (body : FiniteRoutine (K ⊕ Port)) : FiniteRoutine (K ⊕ Port) :=
  ((part .init).followedBy (loop body)).followedBy (part .clearIndex)

variable [DecidableEq K]

private theorem part_run {q : Phase} (hq : q ≠ .done) {s t : Stacks Port} {m : ℕ}
    (run : StackRuns code m q s .done t) (data : Stacks K) :
    (part q).Runs m (Sum.elim data s) (Sum.elim data t) := by
  apply FiniteRoutine.runs_ofStackCode_framed Sum.inr_injective (normal := (· == .done))
    (by simpa using hq) rfl (fun u h => by simp only [beq_iff_eq] at h; subst u; rfl) run
  · intro; rfl
  · intro; rfl
  · intro p hp; cases p with
    | inl k => rfl
    | inr k => exact (hp k rfl).elim

private theorem pop_flag (data : Stacks K) (h i : ℕ) (b : Bool) :
    Function.update (row data h i [b]) (.inr Port.again) [] = row data h i [] := by
  funext p; cases p with
  | inl k => simp [row]
  | inr p => cases p <;> simp [row, store]

private theorem ofNat_val {h i : ℕ} (hi : i < 2^h) :
    (Fin.ofNat (2^h) i).val = i := Nat.mod_eq_of_lt hi

omit [DecidableEq K] in
private theorem visit_eq_row (data : Stacks K) {h i : ℕ} (hi : i < 2^h) :
    visit data ⟨i,hi⟩ = row data h i [] := by
  simp only [visit, row, show Fin.ofNat (2^h) i = ⟨i,hi⟩ from Fin.ext (ofNat_val hi)]

private theorem advance {h i : ℕ} (hi : i < 2^h) (data : Stacks K) :
    (part (.add true)).Runs (4*h+4) (row data h i [])
      (row data h (i+1) [decide (i+1 < 2^h)]) := by
  let x := wordBits (Fin.ofNat (2^h) i)
  have hx : x.length = h := length_wordBits _
  have hv : value x = i := (value_wordBits _).trans (ofNat_val hi)
  have hl : (incScan true x).1.length = h := (incScan_length ..).trans hx
  have ha := incScan_value true x
  rw [hx, hv, Bool.toNat_true] at ha
  have hsmall := value_lt (incScan true x).1
  rw [hl] at hsmall
  have ho : (!(incScan true x).2) = decide (i+1 < 2^h) := by
    cases hh : (incScan true x).2 <;> simp [hh] at ha ⊢ <;> omega
  have hout : (incScan true x).1 = wordBits (Fin.ofNat (2^h) (i+1)) := by
    apply eq_of_length_value (hl.trans (length_wordBits _).symm)
    rw [value_wordBits]
    change value (incScan true x).1 = (i+1) % (2^h)
    cases hh : (incScan true x).2
    · simp only [hh, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at ha
      rw [← ha, Nat.mod_eq_of_lt hsmall]
    · simp only [hh, Bool.toNat_true, Nat.mul_one] at ha
      have he : i+1 = 2^h := by omega
      rw [he, Nat.mod_self]
      omega
  have hr := part_run (by decide : Phase.add true ≠ .done) (advance_run (ones h) x (ones i)) data
  simpa only [hx, hout, ho, row, ones, List.replicate_succ] using hr

private theorem loop_run (body : FiniteRoutine (K ⊕ Port)) (data : ℕ → Stacks K) (h T : ℕ)
    (bodyRun : ∀ i : Fin (2^h), ∃ t ≤ T,
      body.Runs t (visit (data i.val) i) (visit (data (i.val+1)) i))
    (m i : ℕ) (hs : m+i = 2^h) :
    ∃ t ≤ m*(T+4*h+5)+2, (loop body).Runs t
      (row (data i) h i [decide (i < 2^h)]) (row (data (2^h)) h (2^h) []) := by
  induction m generalizing i with
  | zero =>
    have he : i = 2^h := by omega
    subst i
    simp only [Nat.lt_irrefl, decide_false, Nat.zero_mul, Nat.zero_add]
    refine ⟨2, le_rfl, ?_⟩
    apply Routine.Runs.popLoop_false_stop (.inr Port.again) id Routine.ret
      (body.followedBy (part (.add true))).body (s := row (data (2^h)) h (2^h) [false])
      (n := 1) rfl rfl
    rw [pop_flag]
    exact Routine.runs_ret _
  | succ m ih =>
    have hi : i < 2^h := by omega
    have hre : decide (i < 2^h) = true := decide_eq_true hi
    obtain ⟨t, ht, hb⟩ := bodyRun ⟨i,hi⟩
    simp only [visit_eq_row] at hb
    have ha := advance hi (data (i+1))
    have hr := hb.followedBy ha
    obtain ⟨s, hs', hr'⟩ := ih (i+1) (by omega)
    rw [hre]
    refine ⟨1+(t+(4*h+4))+s, ?_, ?_⟩
    · rw [Nat.succ_mul m]; omega
    · let hiBody := (body.followedBy (part (.add true))).body
      change (Routine.popLoop (.inr Port.again) id Routine.ret hiBody).Runs _ _ _ at hr' ⊢
      exact Routine.Runs.popLoop_true_continue (.inr Port.again) id Routine.ret hiBody
        (s := row (data i) h i [true]) (tail := []) (n := t+(4*h+4)) (m := s)
        (mid := row (data (i+1)) h (i+1) [decide (i+1 < 2^h)]) rfl rfl
        (by rw [pop_flag]; exact hr) hr'

/-- A traversal makes one callback for each physical row, in increasing order.
The additive charge per row is linear in its binary width and includes the
cleanup of the unary offsets after the last callback. -/
theorem runs (body : FiniteRoutine (K ⊕ Port)) (data : ℕ → Stacks K) (h T : ℕ)
    (bodyRun : ∀ i : Fin (2^h), ∃ t ≤ T,
      body.Runs t (visit (data i.val) i) (visit (data (i.val+1)) i)) :
    ∃ t ≤ 6*h+7 + 2^h*(T+4*h+6), (routine body).Runs t (idle (data 0) h) (idle (data (2^h)) h) := by
  have hinit : (part .init).Runs (5*h+3) (idle (data 0) h) (row (data 0) h 0 [true]) :=
    part_run (by decide : Phase.init ≠ .done) (initialize_run h) (data 0)
  obtain ⟨t, ht, hloop⟩ := loop_run body data h T bodyRun (2^h) 0 (by omega)
  rw [decide_eq_true (Nat.two_pow_pos _)] at hloop
  let x := wordBits (Fin.ofNat (2^h) (2^h))
  have hclear := part_run (by decide : Phase.clearIndex ≠ .done)
    (clear_run (ones h) x (ones (2^h))) (data (2^h))
  simp only [x, ones, length_wordBits, List.length_replicate] at hclear
  refine ⟨_, ?_, (hinit.followedBy hloop).followedBy hclear⟩
  rw [show T+4*h+6 = (T+4*h+5)+1 by omega, Nat.mul_succ]
  omega

end RAMTape.SortOffsets

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.LiveExponentRAM
import OAI.Computability.VPVNP.PrimedScheduleRAM

/-!
# Executing a row of the first-half exponent check

Each digit runs in a fresh private workspace. The only shared cell changed
by an entire row is that label's increment word. Its final value on success
is zero. The input and output bit buffers may be read at any disjoint
addresses computed by the stage.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveExponent

open BurstRAM BurstRAM.PrivateRAM
open scoped Classical

variable {w : ℕ}

/-- Convert a natural exponent-sweep cursor to its persistent machine word. -/
abbrev atPos (p : ℕ) : Word w := Fin.ofNat _ p

private theorem atPos_val {p : ℕ} (h : p < 2^w) : (atPos (w := w) p).val = p :=
  Nat.mod_eq_of_lt h

private theorem atPos_succ (p : ℕ) : atPos (w := w) (p+1) = atPos p + 1 := by
  apply Fin.ext
  exact Nat.add_mod p 1 (2^w)

/-- The read-only and writable cells used by a nonempty suffix of one row.
The final digit test is taken exactly at the end of the row. -/
structure RowCells (pub : Fin 5 → Word w) (addr : Word w) (p : ℕ)
    (ds : List (Bool × Bool)) (m : Memory w) : Prop where
  fits : p + ds.length ≤ (pub 4).val
  cells : ∀ i (hi : i < ds.length),
    let s := atPos (w := w) (p+i)
    carryAddress pub s = addr ∧ incomingAddress pub s ≠ addr ∧ outgoingAddress pub s ≠ addr ∧
      (m (incomingAddress pub s).val).val = ds[i].1.toNat ∧
      (m (outgoingAddress pub s).val).val = ds[i].2.toNat ∧
      ((p+i) % (pub 3).val + 1 = (pub 3).val ↔ i+1 = ds.length)

private theorem RowCells.tail {pub : Fin 5 → Word w} {addr : Word w} {p : ℕ}
    {d : Bool × Bool} {ds : List (Bool × Bool)} {m : Memory w}
    (h : RowCells pub addr p (d::ds) m) (v : Word w) :
    RowCells pub addr (p+1) ds (writeMemory m addr v) := by
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.fits
  · intro i hi
    obtain ⟨ha, hb, hc, hx, hy, he⟩ := h.cells (i+1) (by simpa using hi)
    have ep : p+1+i = p+(i+1) := by omega
    rw [ep]
    refine ⟨ha,hb,hc,?_,?_,?_⟩
    · rw [writeMemory, ite_eq_right (fun e => hb (Fin.ext e))]
      exact hx
    · rw [writeMemory, ite_eq_right (fun e => hc (Fin.ext e))]
      exact hy
    · simpa using he

/-- Expected digit reports, even if a check would stop the actual run.
They determine the only possible complete transcript. -/
def rowReports (pub : Fin 5 → Word w) : ℕ → ℕ → Memory w → List (Report w)
  | 0, _, _ => []
  | n+1, p, m =>
    let r := digitReport pub (atPos p) m
    r :: rowReports pub n (p+1) (after m r.events)

private theorem bool_le (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

private theorem carry_head {pub : Fin 5 → Word w} {addr : Word w} {p : ℕ}
    {d : Bool × Bool} {ds : List (Bool × Bool)} {m : Memory w}
    (h : RowCells pub addr p (d :: ds) m) (hw : 2 ≤ w) (hc : (m addr.val).val + 1 < 2^w) :
    let r := digitReport pub (atPos p) m
    let next := after m r.events
    (next addr.val).val = total (m addr.val).val d.1 / 2 ∧
      RowCells pub addr (p+1) ds next ∧ (next addr.val).val+1 < 2^w := by
  dsimp only
  obtain ⟨ha, _, _, hx, _, _⟩ := h.cells 0 (by simp)
  simp only [Nat.add_zero, List.getElem_cons_zero] at ha hx
  rw [digitReport_after, ha]
  have hb := bool_le d.1
  have hfit : (m (carryAddress pub (atPos p)).val).val +
      (m (incomingAddress pub (atPos p)).val).val < 2^w := by rw [ha, hx]; omega
  have hv := carryWord_val pub (atPos p) m hw hfit
  rw [ha, hx] at hv
  refine ⟨by simpa [writeMemory,total] using hv, h.tail _, ?_⟩
  rw [writeMemory, ite_eq_left rfl, hv]
  omega

/-- Execute the digit calls of one row with any continuation. An incorrect
output bit, overflow, or any extra binary choice rejects the call sequence. -/
theorem run_row {pub : Fin 5 → Word w} {addr : Word w} {p : ℕ} {ds : List (Bool × Bool)}
    {m : Memory w} (hw : 2 ≤ w) (hz : 0 < (pub 3).val) (h : RowCells pub addr p ds m)
    (hc : (m addr.val).val + 1 < 2^w) (hne : ds ≠ [])
    (bits : List (List Bool)) (hlen : bits.length = ds.length) (tail : List (List Bool)) (f : ℕ) :
    let P := (digitTemplate.instantiate w pub).program
    runSegment P (f+31) (some (atPos p)) m (bits ++ tail) =
      if Checks (m addr.val).val (ds.map Prod.fst) (ds.map Prod.snd) ∧ bits = List.replicate ds.length [] then
        (runSegment P (f+31) (some (atPos (p+ds.length))) (writeMemory m addr 0) tail).map
          (rowReports pub ds.length p m ++ ·)
      else none := by
  classical
  dsimp only
  induction ds generalizing p m bits with
  | nil => contradiction
  | cons d ds ih =>
    cases bits with
    | nil => simp at hlen
    | cons b bits =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      let s := atPos (w := w) p
      let r := digitReport pub s m
      let m' := after m r.events
      obtain ⟨ha, _, _, hx, hy, he⟩ := h.cells 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero, List.length_cons] at ha hx hy he
      change carryAddress pub s = addr at ha
      change (m (incomingAddress pub s).val).val = d.1.toNat at hx
      change (m (outgoingAddress pub s).val).val = d.2.toNat at hy
      have hp : p < (pub 4).val := by have := h.fits; simp only [List.length_cons] at this; omega
      have hsp : s.val = p := atPos_val (hp.trans (pub 4).isLt)
      have hs : s < pub 4 := by simpa only [Fin.lt_def, hsp] using hp
      have hd := bool_le d.1
      have hfit : (m (carryAddress pub s).val).val + (m (incomingAddress pub s).val).val < 2^w := by
        rw [ha, hx]; omega
      have htest : DigitTest pub s m ↔
          d.2.toNat = total (m addr.val).val d.1 % 2 ∧ (ds = [] → total (m addr.val).val d.1 / 2 = 0) := by
        have he' : p % (pub 3).val + 1 = (pub 3).val ↔ ds = [] := he.trans (by simp)
        rw [DigitTest, ha, hx, hy, hsp, he', total]
        exact and_iff_right (by omega)
      have hmem := carry_head h hw hc
      change (m' addr.val).val = _ ∧ RowCells _ _ _ _ m' ∧ _ at hmem
      have hret : r.result = some (atPos (w := w) (p+1)) := congrArg some (atPos_succ p).symm
      rw [List.cons_append, runSegment, execute_digit_iff pub (atPos p) m hw hz hs hfit]
      change (match (if DigitTest pub s m ∧ b = [] then some r else none) with
        | none => none
        | some rep => (runSegment (digitTemplate.instantiate w pub).program (f+31)
          rep.result (after m rep.events) (bits ++ tail)).map (rep :: ·)) = _
      simp only [List.map_cons, Checks, List.length_cons, List.replicate_succ, List.cons.injEq]
      by_cases hb : b = []
      · by_cases hdigit : d.2.toNat = total (m addr.val).val d.1 % 2
        · cases ds with
          | nil =>
            have hb0 : bits = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
            subst bits
            by_cases hc0 : total (m addr.val).val d.1 / 2 = 0
            · have ht := htest.mpr ⟨hdigit, fun _ => hc0⟩
              have hm0 : m' = writeMemory m addr 0 := by
                change after m (digitReport pub s m).events = _
                rw [digitReport_after, ha]
                congr 1
                apply Fin.ext
                have eqv := hmem.1.trans hc0
                change (after m (digitReport pub s m).events addr.val).val = 0 at eqv
                rw [digitReport_after, ha, writeMemory, ite_eq_left rfl] at eqv
                exact eqv
              simp only [ht, hdigit, hc0, hb, true_and, and_true, ite_true, Checks, List.map_nil,
                List.nil_append]
              rw [hret, show after m r.events = _ from hm0]
              rfl
            · have hn : ¬DigitTest pub s m := fun ht => hc0 ((htest.mp ht).2 rfl)
              simp [hn, hc0, Checks]
          | cons e es =>
            have ht := htest.mpr ⟨hdigit, by simp⟩
            have hh := ih hmem.2.1 hmem.2.2 (by simp) bits hlen
            have hm0 : writeMemory m' addr 0 = writeMemory m addr 0 := by
              change writeMemory (after m (digitReport pub s m).events) addr 0 = _
              rw [digitReport_after, ha]
              funext i
              by_cases hi : i = addr.val <;> simp [writeMemory, hi]
            simp only [ht, hb, hdigit, true_and, ite_true]
            rw [hret, show after m r.events = m' from rfl, hh, hm0, hmem.1]
            have ep : p+((e::es).length+1) = p+1+(e::es).length := by omega
            rw [ep]
            split <;> simp [rowReports, Option.map_map, Function.comp_def, r, s, m']
        · have hn : ¬DigitTest pub s m := fun ht => hdigit (htest.mp ht).1
          simp [hn, hdigit]
      · simp [hb]

end LiveExponent

end VPVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.CubeISAOwnedPackets
import OAI.Computability.BorderVNP.CubeISAOwnedSingletons
import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.RoutingISADeterministic

/-! # Native validity tests for packet and singleton row counters

The fixed dimension is unrolled in the instruction table. Packet trials check
that the two symbols in each remaining digit increase. Singleton trials first
compare the grouping symbols and then the remaining endpoint digits. Neither
scan allocates or touches shared memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM Cube.Physical.Owned

/-- Every pair digit in the remaining packet label has increasing symbols. -/
abbrev strictDigits (n d x : ℕ) : Prop :=
  ∀ j : Fin n, let v := x / (d*d)^j.val % (d*d)
               v / d < v % d

/-- The two remaining endpoint labels share a symbol. -/
abbrev commonDigits (n d x y : ℕ) : Prop :=
  ∃ j : Fin n, x / d^j.val % d = y / d^j.val % d

/-- The packet filter reads exactly the other-coordinate fields of the owned
mixed-radix counter. -/
theorem strictDigits_iff_trial {n d blocks : ℕ} (t : Fin (packetTrials n d blocks)) :
    strictDigits n d (t.val / blocks / 2) ↔ packetTrialValid t := by
  apply forall_congr' fun j => ?_
  change _ ↔ ((packetDigits n d blocks t).1.1 j).1.val < ((packetDigits n d blocks t).1.1 j).2.val
  rw [((packetDigits_values t).2.2 j).1, ((packetDigits_values t).2.2 j).2]

/-- The singleton test combines equality at the grouping coordinate with
agreement among the candidate's remaining source and destination digits. -/
theorem commonDigits_iff_trial {n d : ℕ} (i : Fin (n+1)) (a b : Fin d)
    (t : Fin (singlePairTrials n d)) :
    (a.val = b.val ∨ commonDigits n d (t.val / d^n) (t.val % d^n)) ↔
      singleTrialValid i a b t := by
  rw [singleTrialValid_iff, Fin.ext_iff]
  apply or_congr_right
  apply exists_congr fun j => ?_
  rw [Fin.ext_iff, (singleOtherLabels_values t j).1, (singleOtherLabels_values t j).2]

private theorem strict_succ (n d x : ℕ) :
    strictDigits (n+1) d x ↔ x % (d*d) / d < x % (d*d) % d ∧ strictDigits n d (x / (d*d)) := by
  unfold strictDigits
  rw [Fin.forall_fin_succ]
  simp only [Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]

private theorem common_succ (n d x y : ℕ) :
    commonDigits (n+1) d x y ↔ x%d = y%d ∨ commonDigits n d (x/d) (y/d) := by
  unfold commonDigits
  rw [Fin.exists_fin_succ]
  simp only [Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]

private def packetStep : Code := .block [
  .binary .mod 41 29 11, .binary .div 29 29 11, .binary .div 42 41 10, .binary .mod 43 41 10]

/-- Set register 40 to one iff every remaining packet symbol pair increases. -/
def packetFilter : ℕ → Code
  | 0 => .copy 40 1
  | n+1 => .seq packetStep (.ifLt 42 43 (packetFilter n) (.copy 40 0))

private def singleStep : Code := .block [
  .binary .mod 41 29 10, .binary .mod 42 30 10, .binary .div 29 29 10, .binary .div 30 30 10]

private def singleTail : ℕ → Code
  | 0 => .copy 40 0
  | n+1 => .seq singleStep (.ifEq 41 42 (.copy 40 1) (singleTail n))

/-- Set register 40 to one iff the endpoint labels share a coordinate. -/
def singleFilter (n : ℕ) : Code := .ifEq 14 15 (.copy 40 1) (singleTail n)

/-- The complete packet test has a linear opcode count. -/
theorem packetFilter_slots (n : ℕ) : (packetFilter n).slots = 6*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => change 4 + (1 + (packetFilter n).slots + 1) = _; omega

private theorem singleTail_slots (n : ℕ) : (singleTail n).slots = 6*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => change 4 + (1 + 1 + (singleTail n).slots) = _; omega

/-- The complete singleton test has a linear opcode count. -/
theorem singleFilter_slots (n : ℕ) : (singleFilter n).slots = 6*n+3 := by
  change 1+1+(singleTail n).slots = _
  rw [singleTail_slots]
  omega

/-- The packet filter preserves all low registers, including the packet base,
orientation, and global index returned by address preparation. -/
theorem packetFilter_protects (n : ℕ) {k : ℕ} (hk : k ≤ 29) : (packetFilter n).protects k = true := by
  induction n <;> simp [packetFilter, packetStep, Code.block, Code.protects, *] <;> omega

private theorem singleTail_protects (n : ℕ) {k : ℕ} (hk : k ≤ 29) : (singleTail n).protects k = true := by
  induction n <;> simp [singleTail, singleStep, Code.block, Code.protects, *] <;> omega

/-- Both prepared endpoint addresses survive the singleton test. -/
theorem singleFilter_protects (n : ℕ) {k : ℕ} (hk : k ≤ 29) : (singleFilter n).protects k = true := by
  simp [singleFilter, Code.protects, singleTail_protects n hk]
  omega

/-- The packet test has one deterministic control path on each register bank. -/
theorem packetFilter_deterministic (n : ℕ) : (packetFilter n).deterministic = true := by
  induction n <;> simp [packetFilter, packetStep, Code.block, Code.deterministic, *]

private theorem singleTail_deterministic (n : ℕ) : (singleTail n).deterministic = true := by
  induction n <;> simp [singleTail, singleStep, Code.block, Code.deterministic, *]

/-- The singleton test has one deterministic control path on each register bank. -/
theorem singleFilter_deterministic (n : ℕ) : (singleFilter n).deterministic = true := by
  simp [singleFilter, Code.deterministic, singleTail_deterministic]

private theorem packet_correct {w : ℕ} (env : Arg → ℕ) (n : ℕ) (z : NatState) {d x : ℕ}
    (h0 : z.reg 0 = 0) (h1 : z.reg 1 = 1) (h10 : z.reg 10 = d) (h11 : z.reg 11 = d*d)
    (hx : z.reg 29 = x) (hd : 0 < d) :
    (packetFilter n).fixedSafe w env z ∧
      ((packetFilter n).fixedEval env z).reg 40 = (if strictDigits n d x then 1 else 0) ∧
      ((packetFilter n).fixedEval env z).mem = z.mem := by
  induction n generalizing x z with
  | zero => simp [packetFilter, Code.fixedSafe, Code.safeReadOnly, Code.fixedEval, Code.evalNat, h1]
  | succ n ih =>
    let t := packetStep.fixedEval env z
    have keep (j : Reg) (hj : j.val < 29) : t.reg j = z.reg j :=
      packetStep.fixedEval_protected env z (by decide) j hj
    have safe : packetStep.fixedSafe w env z := by
      simp (config := {decide := true}) [packetStep, Code.block, Code.fixedSafe, Code.safeReadOnly,
        Code.fixedEval, Code.evalNat, addressOpFits, h10,h11, hd, Nat.mul_pos hd hd]
    have fields : t.reg 29 = x/(d*d) ∧ t.reg 42 = x%(d*d)/d ∧ t.reg 43 = x%(d*d)%d := by
      simp (config := {decide := true}) [t,packetStep,Code.block,Code.fixedEval,Code.evalNat,addressOp,hx,h10,h11]
    have tail := ih t ((keep 0 (by decide)).trans h0) ((keep 1 (by decide)).trans h1)
      ((keep 10 (by decide)).trans h10) ((keep 11 (by decide)).trans h11) fields.1
    change (packetStep.fixedSafe w env z ∧
        (if t.reg 42 < t.reg 43 then (packetFilter n).fixedSafe w env t else True)) ∧
      (if t.reg 42 < t.reg 43 then (packetFilter n).fixedEval env t else
        (Code.copy 40 0).fixedEval env t).reg 40 = _ ∧
      (if t.reg 42 < t.reg 43 then (packetFilter n).fixedEval env t else
        (Code.copy 40 0).fixedEval env t).mem = _
    have hm : t.mem = z.mem := rfl
    rw [fields.2.1, fields.2.2]
    by_cases h : x%(d*d)/d < x%(d*d)%d
    · simpa only [strict_succ, h, ite_true, true_and] using And.intro (And.intro safe tail.1)
        (And.intro tail.2.1 (tail.2.2.trans hm))
    · simp only [strict_succ, h, ite_false, false_and, safe, and_true, Code.fixedEval,
        Code.evalNat, Function.update_self, (keep 0 (by decide)).trans h0, hm]

private theorem single_correct {w : ℕ} (env : Arg → ℕ) (n : ℕ) (z : NatState) {d x y : ℕ}
    (h0 : z.reg 0 = 0) (h1 : z.reg 1 = 1) (h10 : z.reg 10 = d)
    (hx : z.reg 29 = x) (hy : z.reg 30 = y) (hd : 0 < d) :
    (singleTail n).fixedSafe w env z ∧
      ((singleTail n).fixedEval env z).reg 40 = (if commonDigits n d x y then 1 else 0) ∧
      ((singleTail n).fixedEval env z).mem = z.mem := by
  induction n generalizing x y z with
  | zero => simp [singleTail, Code.fixedSafe, Code.safeReadOnly, Code.fixedEval, Code.evalNat, h0]
  | succ n ih =>
    let t := singleStep.fixedEval env z
    have keep (j : Reg) (hj : j.val < 29) : t.reg j = z.reg j :=
      singleStep.fixedEval_protected env z (by decide) j hj
    have safe : singleStep.fixedSafe w env z := by
      simp (config := {decide := true}) [singleStep, Code.block, Code.fixedSafe, Code.safeReadOnly,
        Code.fixedEval, Code.evalNat, addressOpFits, h10, hd]
    have fields : t.reg 29 = x/d ∧ t.reg 30 = y/d ∧ t.reg 41 = x%d ∧ t.reg 42 = y%d := by
      simp (config := {decide := true}) [t,singleStep,Code.block,Code.fixedEval,Code.evalNat,addressOp,hx,hy,h10]
    have tail := ih t ((keep 0 (by decide)).trans h0) ((keep 1 (by decide)).trans h1)
      ((keep 10 (by decide)).trans h10) fields.1 fields.2.1
    change (singleStep.fixedSafe w env z ∧
        (if t.reg 41 = t.reg 42 then True else (singleTail n).fixedSafe w env t)) ∧
      (if t.reg 41 = t.reg 42 then (Code.copy 40 1).fixedEval env t else
        (singleTail n).fixedEval env t).reg 40 = _ ∧
      (if t.reg 41 = t.reg 42 then (Code.copy 40 1).fixedEval env t else
        (singleTail n).fixedEval env t).mem = _
    have hm : t.mem = z.mem := rfl
    rw [fields.2.2.1, fields.2.2.2]
    by_cases h : x%d = y%d
    · simp [h, safe, common_succ, Code.fixedEval, Code.evalNat, (keep 1 (by decide)).trans h1, hm]
    · simpa [h, common_succ, hm] using And.intro (And.intro safe tail.1)
        (And.intro tail.2.1 (tail.2.2.trans hm))

/-- Run the native packet filter at word width `w`. The divisor hypotheses
are the only arithmetic guards. All memory and all registers below 29 survive. -/
theorem packetFilter_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (n : ℕ) {d x : ℕ}
    (r0 : readings s 0 = 0) (r1 : readings s 1 = 1) (r10 : readings s 10 = d)
    (r11 : readings s 11 = d*d) (r29 : readings s 29 = x) (hd : 0 < d) :
    BoundedRun pub macros (packetFilter n) s m (6*n+1) (fun z =>
      z.reg 40 = (if strictDigits n d x then 1 else 0) ∧
      (∀ j : Reg, j.val < 29 → z.reg j = readings s j) ∧ z.mem = readings m) := by
  let st := NatState.ofWords s m
  have hc := packet_correct (w := w) (readings pub) n st r0 r1 r10 r11 r29 hd
  apply ((packetFilter n).runFixed pub macros s m hc.1).mono (packetFilter_slots n).le
  rintro z rfl
  exact ⟨hc.2.1, (packetFilter n).fixedEval_protected _ st (packetFilter_protects n le_rfl), hc.2.2⟩

/-- Run the native singleton filter on the fixed ordered row and the two
remaining labels. The full prepared endpoints and memory survive. -/
theorem singleFilter_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (n : ℕ) {d a b x y : ℕ}
    (r0 : readings s 0 = 0) (r1 : readings s 1 = 1) (r10 : readings s 10 = d)
    (r14 : readings s 14 = a) (r15 : readings s 15 = b)
    (r29 : readings s 29 = x) (r30 : readings s 30 = y) (hd : 0 < d) :
    BoundedRun pub macros (singleFilter n) s m (6*n+3) (fun z =>
      z.reg 40 = (if a = b ∨ commonDigits n d x y then 1 else 0) ∧
      (∀ j : Reg, j.val < 29 → z.reg j = readings s j) ∧ z.mem = readings m) := by
  let st := NatState.ofWords s m
  have hc := single_correct (w := w) (readings pub) n st r0 r1 r10 r29 r30 hd
  have rg14 : st.reg 14 = a := r14
  have rg15 : st.reg 15 = b := r15
  have safe : (singleFilter n).fixedSafe w (readings pub) st := by
    by_cases h : a = b <;> simp [singleFilter,Code.fixedSafe,Code.safeReadOnly,rg14,rg15,h,hc.1]
  apply ((singleFilter n).runFixed pub macros s m safe).mono (singleFilter_slots n).le
  rintro z rfl
  refine ⟨?_,(singleFilter n).fixedEval_protected _ st (singleFilter_protects n le_rfl),?_⟩
  · have rg1 : st.reg 1 = 1 := r1
    change (if st.reg 14 = st.reg 15 then (Code.copy 40 1).fixedEval _ st else
      (singleTail n).fixedEval _ st).reg 40 = _
    by_cases h : a = b <;> simp [rg14,rg15,h,hc.2.1, Code.fixedEval, Code.evalNat,rg1]
  · change (if st.reg 14 = st.reg 15 then (Code.copy 40 1).fixedEval _ st else
      (singleTail n).fixedEval _ st).mem = _
    rw [rg14,rg15]
    split
    · rfl
    · exact hc.2.2

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI

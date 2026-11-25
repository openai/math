import OAI.Computability.BorderVNP.RoutingISACheckLoop
import OAI.Computability.BorderVNP.RoutingISAAddressFit
import OAI.Computability.BorderVNP.RoutingISAHeader
import OAI.Computability.BorderVNP.RoutingISAChecked
import OAI.Computability.BorderVNP.RoutingISALoops

/-! # Native comparison of the two legs at a relay -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- One iteration of the actual compiled relay comparison. -/
def relayBody : Code := .block [
  .copy 32 21, .copy 33 22, .copy 34 23, .copy 35 16, legAddress, .load 17 48,
  .copy 32 23, .copy 33 22, .copy 34 21, .copy 35 16, legAddress, .load 14 48,
  requireEq 17 14, requireLt 17 2, .binary .add 16 16 1]

/-- At this physical quotient, both addressed copies of the transmission are
Boolean and agree. -/
def RelayWordAgrees (pub : Arg → ℕ) (mem : ℕ → ℕ) (u v y q : ℕ) : Prop :=
  let x := mem (routedAddress pub mem u v y q)
  x = mem (routedAddress pub mem y v u q) ∧ x < 2

private theorem legLow (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) (i : Reg) (hi : i.val < 30) :
    legAddress.evalNat pub mem s i = s i := legAddress.evalNat_protected _ _ _ (by decide) i hi

private theorem eval_requireEq (x y : Reg) (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    (requireEq x y).evalNat pub mem s = s := by simp [requireEq, Code.evalNat]
private theorem eval_requireLt (x y : Reg) (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    (requireLt x y).evalNat pub mem s = s := by simp [requireLt, Code.evalNat]

/-- An iteration increments the quotient and preserves every other low register
except for the two actual loaded words. -/
theorem relayBody_evalNat (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    relayBody.evalNat pub mem s 16 = s 16 + s 1 ∧
    ∀ i : Reg, i.val < 30 → i ≠ 14 → i ≠ 16 → i ≠ 17 → relayBody.evalNat pub mem s i = s i := by
  constructor
  · simp (config := {decide := true}) [relayBody, Code.block, eval_requireEq, eval_requireLt,
      Code.evalNat, legLow, addressOp]
  · intro i hi h14 h16 h17
    have hn (j : Reg) (hj : 30 ≤ j.val) : i ≠ j := fun he => by subst i; omega
    simp (config := {decide := true}) [relayBody, Code.block, eval_requireEq, eval_requireLt,
      Code.evalNat, hi, legLow, h14, h16, h17, hn 32 (by decide), hn 33 (by decide),
      hn 34 (by decide), hn 35 (by decide)]

private theorem relaxLeg : legAddress.relaxReject = legAddress := rfl

private theorem safe_requireEq {w : ℕ} (x y : Reg) (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    (requireEq x y).safeReadOnly w pub mem s ↔ s x = s y := by simp [requireEq, Code.safeReadOnly]
private theorem safe_requireLt {w : ℕ} (x y : Reg) (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    (requireLt x y).safeReadOnly w pub mem s ↔ s x < s y := by simp [requireLt, Code.safeReadOnly]

private def relayReg (s : Reg → ℕ) (u v y q : ℕ) : Reg → ℕ :=
  Function.update (Function.update (Function.update (Function.update s 32 u) 33 v) 34 y) 35 q

private theorem legFit {w : ℕ} {pub : Arg → ℕ} {mem : ℕ → ℕ} (s : Reg → ℕ)
    {u v y q : ℕ} (room : LegRoom w pub mem u v y q) :
    legAddress.safeReadOnly w pub mem (relayReg s u v y q) := by
  apply legAddress_safe
  simpa (config := {decide := true}) [relayReg] using room

private theorem relayBody_safeIff {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (a : LegRoom w pub mem (s 21) (s 22) (s 23) (s 16))
    (b : LegRoom w pub mem (s 23) (s 22) (s 21) (s 16))
    (two : s 2 = 2) (inc : s 16 + s 1 < 2^w) :
    relayBody.safeReadOnly w pub mem s ↔ RelayWordAgrees pub mem (s 21) (s 22) (s 23) (s 16) := by
  simp (config := {decide := true}) [relayBody, Code.block, eval_requireEq, eval_requireLt, safe_requireEq,
    safe_requireLt, Code.evalNat, Code.safeReadOnly, addressOpFits, legLow, legAddress_evalNat, inc, two,
    RelayWordAgrees]
  exact ⟨fun h => h.2.2, fun h => ⟨legFit _ a,legFit _ b,h⟩⟩

private theorem relayBody_room {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (a : LegRoom w pub mem (s 21) (s 22) (s 23) (s 16))
    (b : LegRoom w pub mem (s 23) (s 22) (s 21) (s 16))
    (inc : s 16 + s 1 < 2^w) :
    relayBody.relaxReject.safeReadOnly w pub mem s := by
  have reqEq (t : Reg → ℕ) : (requireEq 17 14).relaxReject.safeReadOnly w pub mem t := by
    simp [requireEq, Code.relaxReject, Code.safeReadOnly]
  have reqLt (t : Reg → ℕ) : (requireLt 17 2).relaxReject.safeReadOnly w pub mem t := by
    simp [requireLt, Code.relaxReject, Code.safeReadOnly]
  simp (config := {decide := true}) [relayBody, Code.block, Code.relaxReject, relaxLeg,
    Code.evalNat_relaxReject, eval_requireEq, eval_requireLt, reqEq, reqLt,
    Code.evalNat, Code.safeReadOnly, addressOpFits, legLow, inc]
  exact ⟨legFit _ a,legFit _ b⟩

/-- The copy-check loop leaves its source table, low registers other than the
quotient and two loaded words, and the entire physical memory intact. -/
structure RelayScanState (bank : Reg → ℕ) (mem : ℕ → ℕ) (q : ℕ) (z : NatState) : Prop where
  /-- The two sides have been compared through every quotient smaller than the cursor. -/
  cursor : z.reg 16 = q
  /-- The shared memory has not been modified. -/
  memory : z.mem = mem
  /-- Registers used by the enclosing pair-table enumeration are preserved. -/
  keep (i : Reg) : i.val < 30 → i ≠ 14 → i ≠ 16 → i ≠ 17 → z.reg i = bank i

/-- Exact comparison and Booleanity test of every occupied position for this
endpoint pair and relay. The cost is constant per quotient, including both
nontrivial physical address calculations and the two loads. -/
theorem compareRelayPositions_test {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (zero : (s 0).val = 0) (one : (s 1).val = 1)
    (two : (s 2).val = 2)
    (room : ∀ q < (s 28).val,
      LegRoom w (readings pub) (readings m) (s 21).val (s 22).val (s 23).val q ∧
      LegRoom w (readings pub) (readings m) (s 23).val (s 22).val (s 21).val q) :
    TestRun pub macros compareRelayPositions s m ((s 28).val * (relayBody.slots + 1) + 2)
      (∀ q < (s 28).val, RelayWordAgrees (readings pub) (readings m) (s 21).val (s 22).val (s 23).val q)
      (RelayScanState (readings s) (readings m) (s 28).val) := by
  let I := RelayScanState (readings s) (readings m)
  let good q := RelayWordAgrees (readings pub) (readings m) (s 21).val (s 22).val (s 23).val q
  have keep {i : ℕ} {z : NatState} (hz : I i z) (r : Reg) (h : r.val < 30) (h' : r ≠ 14)
      (h'' : r ≠ 16) (h''' : r ≠ 17) : z.reg r = (s r).val := hz.keep r h h' h'' h'''
  have regs : ∀ i z, I i z → z.reg 16 = i ∧ z.reg 28 = (s 28).val :=
    fun i z hz => ⟨hz.cursor,keep hz 28 (by decide) (by decide) (by decide) (by decide)⟩
  have step : ∀ i < (s 28).val, ∀ t mt, I i (.ofWords t mt) →
      TestRun pub macros relayBody t mt relayBody.slots (good i) (I (i+1)) := by
    intro i hi t mt h
    have mem : readings mt = readings m := h.memory
    have r16 : readings t 16 = i := h.cursor
    have r21 := keep h 21 (by decide) (by decide) (by decide) (by decide)
    have r22 := keep h 22 (by decide) (by decide) (by decide) (by decide)
    have r23 := keep h 23 (by decide) (by decide) (by decide) (by decide)
    change readings t 21 = (s 21).val at r21
    change readings t 22 = (s 22).val at r22
    change readings t 23 = (s 23).val at r23
    have r1 : readings t 1 = 1 := (keep h 1 (by decide) (by decide) (by decide) (by decide)).trans one
    have r2 : readings t 2 = 2 := (keep h 2 (by decide) (by decide) (by decide) (by decide)).trans two
    have inc : readings t 16 + readings t 1 < 2^w := by rw [r16,r1]; have := (s 28).isLt; omega
    have both := room i hi
    rw [← mem, ← r21, ← r22, ← r23, ← r16] at both
    have test : relayBody.safeReadOnly w (readings pub) (readings mt) (readings t) ↔ good i := by
      simpa only [good,mem,r16,r21,r22,r23] using relayBody_safeIff _ _ _ both.1 both.2 r2 inc
    have exec (hgood : good i) : BoundedRun pub macros relayBody t mt relayBody.slots (I (i+1)) := by
      obtain ⟨es,z,r,cap,vals⟩ := relayBody.runReadOnly pub macros mt t (test.mpr hgood)
      have ⟨cur,kept⟩ := relayBody_evalNat (readings pub) (readings mt) (readings t)
      refine ⟨_,z,mt,r,cap,⟨(congrFun vals 16).trans (cur.trans (by rw [r16,r1])),mem,?_⟩⟩
      intro k hlo h₁ h₂ h₃
      exact (congrFun vals k).trans ((kept k hlo h₁ h₂ h₃).trans (h.keep k hlo h₁ h₂ h₃))
    refine ⟨exec,?_⟩
    intro es z mz r
    have ok := test.mp (r.checked (by decide) (relayBody_room _ _ _ both.1 both.2 inc))
    exact ⟨ok,((exec ok).asTest (by decide)).sound r |>.2⟩
  let t := Function.update s (16 : Reg) (s 0)
  have copy : Runs pub macros (.copy 16 0) s m [tick w] t m := .localStep m rfl rfl
  have init : I 0 (.ofWords t m) := by
    refine ⟨by simpa [t, NatState.ofWords, readings] using zero,rfl,?_⟩
    intro i _ _ h _
    simp [t, NatState.ofWords, readings, h]
  have first : BoundedRun pub macros (.copy 16 0) s m 1 (I 0) := ⟨_,_,_,copy,le_rfl,init⟩
  have next t' mt (h : I 0 (.ofWords t' mt)) :=
    test_counted_loop 16 28 relayBody (s 28).val (fun _ => relayBody.slots) good I regs step
      0 (Nat.zero_le _) t' mt h
  apply ((first.asTest rfl).seq next).mono
  · simp [Finset.sum_const, Nat.add_comm]
    omega
  · simp [good]
  · exact fun _ h => h

end RoutingISA

end BorderVNP
end Computability
end OAI

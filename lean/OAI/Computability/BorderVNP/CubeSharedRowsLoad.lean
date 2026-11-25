import OAI.Computability.BorderVNP.CubeSharedRows

/-! # Native field calculation for the shared record of two distinct groups -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SharedRows

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The rank of a real pair fits in the reserved triangular suffix. -/
theorem Layout.index_lt {l : Layout} {s t : ℕ} (hs : s < t) (ht : t < l.groups) :
    l.rowIndex s t < l.dataCount+l.groups.choose 2 := by
  have h := Nat.choose_le_choose 2 ht
  rw [choose_succ_two] at h
  dsimp [rowIndex]
  omega

private theorem square_key {s t d : ℕ} (hs : s < d) (ht : t < d) : s*d+t < d^2 := calc
  _ < (s+1)*d := by rw [Nat.add_mul,one_mul]; omega
  _ ≤ _ := (Nat.mul_le_mul_right _ hs).trans_eq (pow_two _).symm

/-- The fixed instruction block for reading the two owners and the declared width,
and forming the addresses of their two views. The inner symbol is in register 14. -/
def loadFields : Code := .block [
  .binary .mul 16 2 15,.binary .add 16 11 16,
  .binary .add 17 6 14,.load 17 17,.binary .add 18 6 13,.load 18 18,
  .binary .mul 22 14 3,.binary .add 22 22 13,.binary .mul 23 13 3,.binary .add 23 23 14,
  .binary .mul 24 22 4,.binary .add 24 7 24,.binary .add 24 24 5,.load 19 24,.binary .add 19 8 19,
  .binary .mul 20 10 22,.binary .add 20 9 20,.binary .mul 21 10 23,.binary .add 21 9 21]

/-- The buffered row fields, with the original loop indices intact. -/
structure Buffered (l : Layout) (before : ℕ → ℕ) (s t : ℕ) (z : NatState) : Prop where
  /-- Immutable configuration registers. -/
  ready : l.Ready z
  /-- Outer and inner loop counters and output cursor. -/
  counters : z.reg 13 = t ∧ z.reg 14 = s ∧ z.reg 15 = l.rowIndex s t
  /-- Absolute start of this seven-word output. -/
  record : z.reg 16 = l.address (l.rowIndex s t)
  /-- Actual first and second owner, list width and both destination addresses. -/
  fields : z.reg 17 = before (l.owners+s) ∧ z.reg 18 = before (l.owners+t) ∧
    z.reg 19 = l.selectors+l.crossWidth before s t ∧ z.reg 20 = l.view s t ∧ z.reg 21 = l.view t s

set_option maxHeartbeats 2000000 in
/-- Correct natural contents and address safety of the physical group-row read.
The fresh descriptor is computed from the real declaration and owner arrays. -/
theorem run_loadFields {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {s t : ℕ} (hs : s < t) (ht : t < l.groups)
    (bank : Bank w) (m : Memory w) (ready : l.Ready (.ofWords bank m))
    (ct : (bank 13).val = t) (cs : (bank 14).val = s) (ci : (bank 15).val = l.rowIndex s t)
    (image : l.Image before (l.rowIndex s t) (readings m)) :
    BoundedRun pub macros loadFields bank m loadFields.slots (fun z =>
      Buffered l before s t z ∧ z.mem = readings m) := by
  let z := NatState.ofWords bank m
  have r2 : z.reg 2 = 7 := ready 2 (by decide)
  have r3 : z.reg 3 = l.groups := ready 3 (by decide)
  have r4 : z.reg 4 = l.axes := ready 4 (by decide)
  have r5 : z.reg 5 = l.axis := ready 5 (by decide)
  have r6 : z.reg 6 = l.owners := ready 6 (by decide)
  have r7 : z.reg 7 = l.lengths := ready 7 (by decide)
  have r8 : z.reg 8 = l.selectors := ready 8 (by decide)
  have r9 : z.reg 9 = l.banks := ready 9 (by decide)
  have r10 : z.reg 10 = l.stride := ready 10 (by decide)
  have r11 : z.reg 11 = l.records := ready 11 (by decide)
  have r13 : z.reg 13 = t := ct
  have r14 : z.reg 14 = s := cs
  have r15 : z.reg 15 = l.rowIndex s t := ci
  have hrow := l.index_lt hs ht
  have hout := fit.recordsFit
  change l.records+7*(l.dataCount+l.groups.choose 2) ≤ 2^w at hout
  have ext (a : ℕ) (ha : a ∈ [l.owners+s,l.owners+t,l.lengths+(s*l.groups+t)*l.axes+l.axis,l.frame+13]) :
      z.mem a = before a := by
    apply image.outside
    have ho := fit.separate t ht s hs a ha
    dsimp [Layout.address] at *
    omega
  have ro := ext (l.owners+s) (by simp)
  have rt := ext (l.owners+t) (by simp)
  have rd : z.mem (l.lengths+(s*l.groups+t)*l.axes+l.axis) = l.crossWidth before s t := ext _ (by simp)
  have ks := square_key (hs.trans ht) ht
  have kt := square_key ht (hs.trans ht)
  have kl (k : ℕ) (hk : k < l.groups^2) : l.lengths+k*l.axes+l.axis < 2^w := by
    have h := Nat.mul_le_mul_right l.axes hk
    rw [Nat.succ_mul] at h
    have := fit.lengthsFit
    have := fit.axisFit
    omega
  have kb (k : ℕ) (hk : k < l.groups^2) : l.banks+l.stride*k < 2^w := by
    have h := Nat.mul_le_mul_left l.stride hk
    rw [Nat.mul_succ] at h
    by_cases hz : l.stride = 0
    · have hb : l.banks < 2^w := r9 ▸ (bank 9).isLt
      simpa [hz] using hb
    · have := fit.viewsFit; omega
  have kvs := kb _ ks
  have kvt := kb _ kt
  have kvl := kl _ ks
  have hstride : l.stride < 2^w := r10 ▸ (bank 10).isLt
  have hlen := (fit.widthFit t ht s hs).trans_lt hstride
  have hsafe : loadFields.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [loadFields,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r13,r14,r15,
      rd,hlen]
    have := fit.square
    have := fit.ownersFit
    omega
  apply (loadFields.runFixed pub macros bank m hsafe).mono le_rfl
  rintro result rfl
  change Buffered l before s t (loadFields.fixedEval (readings pub) z) ∧ (loadFields.fixedEval (readings pub) z).mem = z.mem
  refine ⟨⟨ready.fixed (c := loadFields) (by decide) _,?_,?_,?_⟩,?_⟩
  all_goals simp (config := {decide := true}) [loadFields,Code.block,Code.fixedEval,Code.evalNat,
    addressOp,Layout.address,Layout.view,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r13,r14,r15,rd,ro,rt]

end Cube.SharedRows

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.CubeGroupWeightImage

/-! # Native reads of a declared shared row or receiving-cell demand -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open RoutingISA VPVNP.BurstRAM

/-- Look up a strict pair in its sorted declaration row and add the fixed selector prefix. -/
def sharedWidth : Code := .block [
  .ifLt 21 22 (.block [.binary .mul 23 21 3,.binary .add 23 23 22])
    (.block [.binary .mul 23 22 3,.binary .add 23 23 21]),
  .binary .mul 23 23 4,.binary .add 23 6 23,.binary .add 23 23 5,
  .load 26 23,.binary .add 26 26 7]

/-- Read the target group into register 21 and the unscaled increment into 26. -/
def Phase.readRow : Phase → Code
  | .init => .nop
  | .shared => .block [.binary .div 21 20 3,.binary .mod 22 20 3,
      .ifEq 21 22 (.copy 26 0) sharedWidth]
  | .data => .block [.binary .add 22 10 20,.load 21 22,.binary .div 21 21 12,
      .binary .mod 21 21 3,.binary .add 22 11 20,.load 26 22]

private theorem pairKey_lt {d s t : ℕ} (hs : s < d) (ht : t < d) :
    s*d+t < d*d := calc
  _ < s*d+d := Nat.add_lt_add_left ht _
  _ = (s+1)*d := (Nat.succ_mul _ _).symm
  _ ≤ d*d := Nat.mul_le_mul_right _ hs

private theorem sharedWidth_run {l : Layout} {orig : ℕ → ℕ} {w : ℕ} (pub : Arg → ℕ)
    (z : NatState) (ready : l.Ready z) (fit : l.Fits w orig) {s t : ℕ} (hs : s < l.groups)
    (ht : t < l.groups) (h21 : z.reg 21 = s) (h22 : z.reg 22 = t)
    (he : z.mem (l.rowAddr s t) = orig (l.rowAddr s t))
    (hwidth : orig (l.rowAddr s t)+l.selectors < 2^w) :
    sharedWidth.fixedSafe w pub z ∧
      (sharedWidth.fixedEval pub z).reg 26 = orig (l.rowAddr s t)+l.selectors ∧
      (sharedWidth.fixedEval pub z).reg 21 = s ∧ (sharedWidth.fixedEval pub z).mem = z.mem := by
  have h3 : z.reg 3 = l.groups := ready 3 (by decide)
  have h4 : z.reg 4 = l.axes := ready 4 (by decide)
  have h5 : z.reg 5 = l.axis := ready 5 (by decide)
  have h6 : z.reg 6 = l.rows := ready 6 (by decide)
  have h7 : z.reg 7 = l.selectors := ready 7 (by decide)
  have ha := fit.rows s hs t ht
  have sq := fit.square
  by_cases hst : s < t
  · have key := pairKey_lt hs ht
    simp only [Layout.rowAddr,min_eq_left hst.le,max_eq_right hst.le] at he hwidth ha ⊢
    simp (config := {decide := true}) [sharedWidth, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.evalNat,Code.safeReadOnly,addressOp,addressOpFits,h3,h4,h5,h6,h7,h21,h22,hst,he,hwidth]
    omega
  · have key := pairKey_lt ht hs
    have hts := le_of_not_gt hst
    simp only [Layout.rowAddr,min_eq_right hts,max_eq_left hts] at he hwidth ha ⊢
    simp (config := {decide := true}) [sharedWidth, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.evalNat,Code.safeReadOnly,addressOp,addressOpFits,h3,h4,h5,h6,h7,h21,h22,hst,he,hwidth]
    omega

/-- With the actual memory image, every word operation in the physical read fits
and the target and charge coincide with the semantic histogram update. -/
theorem Phase.readRow_sound (p : Phase) (hp : p ≠ .init) {w : ℕ} (pub : Arg → ℕ)
    (l : Layout) (orig : ℕ → ℕ) (z : NatState) (i : ℕ) (hi : i < p.count l)
    (fit : l.Fits w orig) (ready : l.Ready z) (im : Image p l orig z.mem i) (hc : z.reg 20 = i) :
    p.readRow.fixedSafe w pub z ∧
      (p.readRow.fixedEval pub z).reg 21 = p.target l orig i ∧
      1000000*(p.readRow.fixedEval pub z).reg 26 = p.delta l orig i ∧
      (p.readRow.fixedEval pub z).mem = z.mem := by
  have r3 : z.reg 3 = l.groups := ready 3 (by decide)
  have hd := fit.positive
  cases p with
  | init => contradiction
  | data =>
    have r10 : z.reg 10 = l.labels := ready 10 (by decide)
    have r11 : z.reg 11 = l.demands := ready 11 (by decide)
    have r12 : z.reg 12 = l.place := ready 12 (by decide)
    have hplace : 0 < l.place := pow_pos hd _
    have hl := im.outside _ (fit.labelSep i hi)
    have hw := im.outside _ (fit.dataSep i hi)
    simp (config := {decide := true}) [Phase.readRow,Phase.target,Phase.delta,Layout.symbol,
      Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,
      r3,r10,r11,r12,hc,hd,hplace,hl,hw,fit.labels i hi,fit.demands i hi]
  | shared =>
    let s := i/l.groups
    let t := i%l.groups
    have hs : s < l.groups := (Nat.div_lt_iff_lt_mul hd).2 hi
    have ht : t < l.groups := Nat.mod_lt _ hd
    let before := Code.block [.binary .div 21 20 3,.binary .mod 22 20 3]
    let mid := before.fixedEval pub z
    have mid21 : mid.reg 21 = s := by
      simp (config := {decide := true}) [mid,before,Code.block,Code.fixedEval,Code.evalNat,
        addressOp,hc,r3,s]
    have mid22 : mid.reg 22 = t := by
      simp (config := {decide := true}) [mid,before,Code.block,Code.fixedEval,Code.evalNat,
        addressOp,hc,r3,t]
    have midready : l.Ready mid := fun a ha =>
      (before.fixedEval_protected _ _ (by decide) a ha).trans (ready a ha)
    have beforeSafe : before.fixedSafe w pub z := by
      simp (config := {decide := true}) [before,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.evalNat,Code.safeReadOnly,addressOpFits,r3,hd]
    have he := im.outside _ (fit.rowSep s hs t ht)
    have hm : mid.mem = z.mem := rfl
    by_cases hs' : s = t
    · have r0 : mid.reg 0 = 0 := midready 0 (by decide)
      change (_ ∧ _ ∧ (Code.ifEq 21 22 (.copy 26 0) sharedWidth).fixedSafe w pub mid) ∧
        ((Code.ifEq 21 22 (.copy 26 0) sharedWidth).fixedEval pub mid).reg 21 = s ∧
        1000000*((Code.ifEq 21 22 (.copy 26 0) sharedWidth).fixedEval pub mid).reg 26 = _ ∧
        ((Code.ifEq 21 22 (.copy 26 0) sharedWidth).fixedEval pub mid).mem = _
      exact ⟨⟨beforeSafe.1,beforeSafe.2,by simp [Code.fixedSafe,Code.safeReadOnly,mid21,mid22,hs']⟩,
        by simp (config := {decide := true}) [Code.fixedEval,Code.evalNat,mid21,mid22,hs'],
        by simp [Code.fixedEval,Code.evalNat,mid21,mid22,hs',r0,Phase.delta,Layout.rowCharge,
          show i/l.groups = i%l.groups from hs'],
        by simp [Code.fixedEval,mid21,mid22,hs',hm]⟩
    · have hwidth : orig (l.rowAddr s t)+l.selectors < 2^w := by
        have inc := im.incrementFits fit (by decide) hi
        change _ + 1000000*(if s = s ∧ s ≠ t then orig (l.rowAddr s t)+l.selectors else 0) < _ at inc
        rw [ite_eq_left ⟨rfl,hs'⟩] at inc
        omega
      obtain ⟨safe,width,target,mem⟩ := sharedWidth_run pub mid midready fit hs ht mid21 mid22
        (hm ▸ he) hwidth
      change (_ ∧ _ ∧ (Code.ifEq 21 22 (.copy 26 0) sharedWidth).fixedSafe w pub mid) ∧
        ((Code.ifEq 21 22 (.copy 26 0) sharedWidth).fixedEval pub mid).reg 21 = s ∧
        1000000*((Code.ifEq 21 22 (.copy 26 0) sharedWidth).fixedEval pub mid).reg 26 = _ ∧
        ((Code.ifEq 21 22 (.copy 26 0) sharedWidth).fixedEval pub mid).mem = _
      refine ⟨⟨beforeSafe.1,beforeSafe.2,?_⟩,?_,?_,?_⟩ <;>
        simp only [Code.fixedSafe,Code.fixedEval,mid21,mid22,ite_eq_right hs']
      · exact safe
      · exact target
      · change 1000000*(sharedWidth.fixedEval pub mid).reg 26 =
          1000000*(if s = s ∧ s ≠ t then orig (l.rowAddr s t)+l.selectors else 0)
        rw [width,ite_eq_left ⟨rfl,hs'⟩]
      · exact mem.trans hm

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI

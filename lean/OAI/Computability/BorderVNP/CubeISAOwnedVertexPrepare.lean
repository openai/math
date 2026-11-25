import OAI.Computability.BorderVNP.CubeISAOwnedVertexWriter

/-! # Computing the grouping bit and loop scales at a packet

The endpoint symbols and the orientation are supplied by the physical packet
decoder. A team compares its own grouping symbol to the upper endpoint, flips
the first coordinate on reversed packets, and builds both powers of two by
a scan of the fixed number of cube coordinates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedVertex

open Cube Cube.Physical Cube.Physical.VertexIndex VPVNP.BurstRAM

/-- Group owner in 39, proposed grouping coordinate in 40, cube dimension
minus one in 48. The upper group and orientation come from packet registers
15 and 25. This initialization leaves the selector and packet base in place. -/
def shapeSetup : Code := .block [
  .constant 50 0, .constant 51 1, .constant 52 2, .copy 44 51, .copy 46 51,
  .ifEq 39 15 (.copy 45 51) (.copy 45 50),
  .ifEq 40 50 (.ifEq 25 51 (.binary .sub 45 51 45) .nop) .nop]

/-- Double the full half-cube count at each coordinate and the grouping place
only while below the declared grouping coordinate. -/
def shapeBody : Code := .block [
  .binary .mul 46 52 46, .ifLt 50 40 (.binary .mul 44 52 44) .nop, .binary .add 50 50 51]

/-- Prepare the inserted-bit arithmetic from the group and packet words. -/
def prepareShape : Code := .seq shapeSetup (.whileLt 50 48 shapeBody)

variable {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)

/-- The actual native computation of the owner bit, half-cube count, and
grouping place, with a fixed number of instructions per coordinate. -/
theorem prepareShape_run {n d blocks : ℕ} (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (s : Bank w) (m : Memory w)
    (upper : (s 15).val = (p.1.1 i).val.2.val) (ori : (s 25).val = p.1.2.toNat)
    (group : (s 39).val = (groupSymbol p i high).val) (coord : (s 40).val = i.val)
    (dim : (s 48).val = n) (capacity : 2^n < 2^w) (two : 2 < 2^w) :
    BoundedRun pub macros prepareShape s m (shapeSetup.slots+n*(shapeBody.slots+1)+1) fun z =>
      z.reg 44 = 2^i.val ∧ z.reg 45 = (ownerBit i p.1.2 high).toNat ∧ z.reg 46 = 2^n ∧
      z.mem = readings m ∧ (∀ r : Reg, r.val < 44 → z.reg r = (s r).val) ∧ z.reg 47 = (s 47).val := by
  let inv (k : ℕ) (z : NatState) := z.reg 50 = k ∧ z.reg 48 = n ∧ z.reg 51 = 1 ∧ z.reg 52 = 2 ∧
    z.reg 44 = 2^(min k i.val) ∧ z.reg 45 = (ownerBit i p.1.2 high).toNat ∧ z.reg 46 = 2^k ∧
    z.mem = readings m ∧ (∀ r : Reg, r.val < 44 → z.reg r = (s r).val) ∧ z.reg 47 = (s 47).val
  have cond : ((s 39).val = (s 15).val) ↔ high = true := by
    rw [upper, group]
    cases high with
    | false => exact iff_of_false (Nat.ne_of_lt (p.1.1 i).property) (by decide)
    | true => simp [groupSymbol]
  have hi : i.val = 0 ↔ i = 0 := Fin.val_eq_zero_iff
  have init : BoundedRun pub macros shapeSetup s m shapeSetup.slots (inv 0) := by
    let st := NatState.ofWords s m
    have hw : w ≠ 0 := by rintro rfl; norm_num at two
    have safe : shapeSetup.fixedSafe w (readings pub) st := by
      cases high <;> cases hh : p.1.2 <;> by_cases h : i.val = 0 <;>
        simp (config := {decide := true}) [shapeSetup, Code.block, Code.fixedSafe, Code.fixedEval,
          Code.evalNat, Code.safeReadOnly, addressOpFits, st, NatState.ofWords, readings, cond, coord, ori, hh, h, hw, two]
    apply (shapeSetup.runFixed pub macros s m safe).mono le_rfl
    intro z he
    subst z
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun r hr => shapeSetup.fixedEval_protected _ _ (by decide) r hr, ?_⟩ <;>
      cases high <;> cases hh : p.1.2 <;> by_cases h : i.val = 0 <;>
      simp (config := {decide := true}) [shapeSetup, Code.block, Code.fixedEval, Code.evalNat, addressOp,
        dim, ownerBit, ← hi, hh, h, NatState.ofWords, readings, cond, coord, ori]
  have step (k : ℕ) (hk : k < n) (u : Bank w) (mm : Memory w) (hp : inv k (.ofWords u mm)) :
      BoundedRun pub macros shapeBody u mm shapeBody.slots (inv (k+1)) := by
    let st := NatState.ofWords u mm
    rcases hp with ⟨h50,h48,h51,h52,h44,h45,h46,hmem,hrest,h47⟩
    have h40 := (hrest 40 (by decide)).trans coord
    have fit : 2^(k+1) < 2^w := (Nat.pow_le_pow_right (by decide) hk).trans_lt capacity
    have inc : k+1 < 2^w := (show k+1 ≤ n from hk).trans_lt (Nat.lt_two_pow_self.trans capacity)
    have fd : 2 * 2^(min k i.val) < 2^w := by
      rw [← pow_succ']; exact (Nat.pow_le_pow_right (by decide) (by omega : min k i.val+1 ≤ k+1)).trans_lt fit
    rw [pow_succ'] at fit
    have safe : shapeBody.fixedSafe w (readings pub) st := by
      by_cases hl : k < i.val <;>
        simp (config := {decide := true}) [shapeBody, Code.block, Code.fixedSafe, Code.fixedEval,
          Code.evalNat, Code.safeReadOnly, addressOp, addressOpFits, st, h50,h51,h52,h40,h44,h46,hl,fit,fd,inc]
    apply (shapeBody.runFixed pub macros u mm safe).mono le_rfl
    intro z he
    subst z
    have hnext : 2^min (k+1) i.val = if k < i.val then 2*2^min k i.val else 2^min k i.val := by
      by_cases hl : k < i.val
      · simp [hl, Nat.min_eq_left hl.le, pow_succ']
      · simp [hl, Nat.min_eq_right (by omega : i.val ≤ k+1), Nat.min_eq_right (by omega : i.val ≤ k)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun r hr => (shapeBody.fixedEval_protected _ st (by decide) r hr).trans (hrest r hr), ?_⟩ <;>
      by_cases hl : k < i.val <;>
      simp (config := {decide := true}) [shapeBody, Code.block, Code.fixedEval, Code.evalNat,
        addressOp, h50,h48,h51,h52,h40,h44,h45,h46,hmem,h47,hnext,hl,pow_succ']; omega
  exact (init.seq fun u mm hu => run_counted_loop pub macros 50 48 shapeBody n shapeBody.slots inv
    (fun _ _ hp => ⟨hp.1,hp.2.1⟩) step 0 (Nat.zero_le _) u mm hu).mono (by simp; omega)
    fun _ hp => by
      rcases hp with ⟨_,_,_,_,h44,h45,h46,mem,rest,h47⟩
      exact ⟨(by simpa [Nat.min_eq_right (by omega : i.val ≤ n)] using h44), h45,h46,mem,rest,h47⟩

end RoutingISA.OwnedVertex

end BorderVNP
end Computability
end OAI

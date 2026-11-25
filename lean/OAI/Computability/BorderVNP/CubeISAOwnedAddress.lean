import OAI.Computability.BorderVNP.CubeISAOwnedPacketRank
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Native address preparation on one local packet trial

The unmodified low registers carry the alphabet, grouping-coordinate power,
block count, two ordered symbols, bank stride, base, and local cursor. The
fragment returns the packet base in register 24, its orientation in 25,
its stable index in 26 and its other-coordinate digit string in 29.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM Cube.Physical.Owned

/-- Prepare the packet index and bank address from the current owned-row cursor. -/
def preparePacket : Code := .block [
  .binary .mod 28 18 13, .binary .div 29 18 13,
  .binary .mod 25 29 2, .binary .div 29 29 2,
  .binary .mul 30 14 10, .binary .add 30 30 15,
  .binary .mod 31 29 12, .binary .div 32 29 12,
  .binary .mul 32 11 32, .binary .add 32 30 32, .binary .mul 32 12 32,
  .binary .add 26 31 32, .binary .mul 26 26 2, .binary .add 26 26 25,
  .binary .mul 26 26 13, .binary .add 26 26 28, .binary .mul 24 26 16,
  .binary .add 24 17 24]

private theorem partsFit {w d place blocks lo hi t stride base : ℕ}
    (hp : 0 < place) (hb : 0 < blocks) (hs : 0 < stride)
    (bound : base + trialPacketIndex d place blocks lo hi t * stride < 2^w) :
    let x := t / blocks / 2
    let v := lo*d+hi
    let y := d*d*(x/place)
    let z := place*(v+y)
    let a := x%place+z
    let o := a*2+t/blocks%2
    let k := o*blocks+t%blocks
    lo*d < 2^w ∧ v < 2^w ∧ y < 2^w ∧ v+y < 2^w ∧ z < 2^w ∧
      a < 2^w ∧ a*2 < 2^w ∧ o < 2^w ∧ o*blocks < 2^w ∧ k < 2^w ∧ k*stride < 2^w := by
  dsimp only
  unfold trialPacketIndex insertDigit at bound
  have left (x y : ℕ) (hy : 0 < y) : x ≤ x*y := Nat.le_mul_of_pos_right _ hy
  have right (x y : ℕ) (hy : 0 < y) : x ≤ y*x := Nat.le_mul_of_pos_left _ hy
  generalize hx : t / blocks / 2 = x at *
  generalize hq : d*d*(x/place) = y at *
  generalize ho : t/blocks%2 = o at *
  generalize hr : t%blocks = r at *
  have h₁ := left (((x%place+place*(lo*d+hi+y))*2+o)*blocks+r) stride hs
  have h₂ := left ((x%place+place*(lo*d+hi+y))*2+o) blocks hb
  have h₃ := right (lo*d+hi+y) place hp
  omega

/-- The eighteen native operations return the global packet address and retain
the registers below 24 and the entire memory. The single allocation bound covers
all products and sums in the calculation. -/
theorem preparePacket_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) {d place blocks lo hi trial stride base : ℕ}
    (r2 : readings s 2 = 2) (r10 : readings s 10 = d) (r11 : readings s 11 = d*d)
    (r12 : readings s 12 = place) (r13 : readings s 13 = blocks)
    (r14 : readings s 14 = lo) (r15 : readings s 15 = hi)
    (r16 : readings s 16 = stride) (r17 : readings s 17 = base) (r18 : readings s 18 = trial)
    (hp : 0 < place) (hb : 0 < blocks) (hs : 0 < stride)
    (bound : base + trialPacketIndex d place blocks lo hi trial * stride < 2^w) :
    BoundedRun pub macros preparePacket s m 18 (fun z =>
      let k := trialPacketIndex d place blocks lo hi trial
      z.reg 24 = base+k*stride ∧ z.reg 25 = trial/blocks%2 ∧ z.reg 26 = k ∧
      z.reg 29 = trial/blocks/2 ∧ (∀ j : Reg, j.val < 24 → z.reg j = readings s j) ∧
      z.mem = readings m) := by
  let st := NatState.ofWords s m
  have fit := partsFit hp hb hs bound
  dsimp only at fit
  have safe : preparePacket.fixedSafe w (readings pub) st := by
    simp (config := {decide := true}) [preparePacket, Code.block, Code.fixedSafe, Code.safeReadOnly,
      Code.fixedEval, Code.evalNat, addressOp, addressOpFits, st, NatState.ofWords,
      r2,r10,r11,r12,r13,r14,r15,r16,r17,r18, hp, hb]
    unfold trialPacketIndex insertDigit at bound
    tauto
  apply (preparePacket.runFixed pub macros s m safe).mono (by decide)
  intro z hz
  subst z
  refine ⟨?_,?_,?_,?_,fun j hj => preparePacket.fixedEval_protected _ st (by decide) j hj, rfl⟩ <;>
    simp (config := {decide := true}) [preparePacket, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, NatState.ofWords, r2,r10,r11,r12,r13,r14,r15,r16,r17,r18,
      trialPacketIndex, insertDigit]

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI

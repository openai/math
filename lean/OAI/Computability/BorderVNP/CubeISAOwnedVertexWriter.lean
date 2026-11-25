import OAI.Computability.BorderVNP.CubeISAOwnedVertexModel
import OAI.Computability.BorderVNP.DiagonalTallyPacketBank
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Writing the local packet-vertex reference directory

Each incident group processes its own half of the packet vertices. The native
loop writes three words per vertex: the packet bit-bank base, the selected term
ordinal, and the canonical physical vertex ordinal. It visits each local rank
once and writes exactly three words without touching the packet bit bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedVertex

open Cube Cube.Physical Cube.Physical.VertexIndex VPVNP.BurstRAM

/-- Initialize the local rank and the three small arithmetic constants. -/
def setup : Code := .block [.constant 53 0, .constant 54 1, .constant 55 2, .constant 56 3]

/-- Emit one owned vertex triple. Input registers 24, 43, 44, 45, 46, 47
hold the packet base, selector, binary place, fixed bit, local count, and
directory base. The running local rank is register 53. -/
def body : Code := .block [
  .binary .div 50 53 44, .binary .mul 50 55 50, .binary .add 50 50 45,
  .binary .mul 50 44 50, .binary .mod 51 53 44, .binary .add 50 50 51,
  .binary .mul 51 56 53, .binary .add 51 47 51, .store 51 24, .binary .add 51 51 54,
  .store 51 43, .binary .add 51 51 54, .store 51 50, .binary .add 53 53 54]

/-- Complete sparse directory pass for one packet incident at one local grouping symbol. -/
def pass : Code := .seq setup (.whileLt 53 46 body)

/-- Resulting shared memory after a prefix of the local ranks. -/
def image (base packet selector scale bit : ℕ) (before : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => before
  | k+1 => Function.update (Function.update (Function.update
      (image base packet selector scale bit before k) (base+3*k) packet) (base+3*k+1) selector)
      (base+3*k+2) (insertBit scale bit k)

/-- Every triple in a written prefix contains precisely its declared packet base,
selector ordinal, and the inserted physical vertex index. -/
theorem image_at {k j : ℕ} (hj : j < k) (base packet selector scale bit : ℕ) (before : ℕ → ℕ) :
    let m := image base packet selector scale bit before k
    m (base+3*j) = packet ∧ m (base+3*j+1) = selector ∧ m (base+3*j+2) = insertBit scale bit j := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : j = k
    · subst j
      simp [image, Function.update_of_ne]
    · have hj' : j < k := by omega
      simpa only [image, Function.update_of_ne (show base+3*j ≠ base+3*k+2 by omega),
        Function.update_of_ne (show base+3*j ≠ base+3*k+1 by omega),
        Function.update_of_ne (show base+3*j ≠ base+3*k by omega),
        Function.update_of_ne (show base+3*j+1 ≠ base+3*k+2 by omega),
        Function.update_of_ne (show base+3*j+1 ≠ base+3*k+1 by omega),
        Function.update_of_ne (show base+3*j+1 ≠ base+3*k by omega),
        Function.update_of_ne (show base+3*j+2 ≠ base+3*k+2 by omega),
        Function.update_of_ne (show base+3*j+2 ≠ base+3*k+1 by omega),
        Function.update_of_ne (show base+3*j+2 ≠ base+3*k by omega)] using ih hj'

/-- Words outside the output triple array retain their initial contents. -/
theorem image_outside (base packet selector scale bit : ℕ) (before : ℕ → ℕ) (k x : ℕ)
    (hx : x < base ∨ base+3*k ≤ x) : image base packet selector scale bit before k x = before x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [image, Function.update_of_ne (show x ≠ base+3*k+2 by omega),
      Function.update_of_ne (show x ≠ base+3*k+1 by omega),
      Function.update_of_ne (show x ≠ base+3*k by omega)] using ih (by omega)

variable {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)

/-- The native word loop computes the precise memory image in linear local
vertex time. The loop counter bound is half the cube, independent of how many
packets other groups own. -/
theorem pass_run {n : ℕ} (i : Fin (n+1)) (bit : Bool) (s : Bank w) (m : Memory w)
    (scale : (s 44).val = 2^i.val) (digit : (s 45).val = bit.toNat)
    (count : (s 46).val = 2^n) (capacity : (s 47).val + 3*2^n ≤ 2^w)
    (indices : 2^(n+1) ≤ 2^w) (small : 3 < 2^w) :
    BoundedRun pub macros pass s m (15*2^n+5) fun z =>
      z.mem = image (s 47).val (s 24).val (s 43).val (2^i.val) bit.toNat (readings m) (2^n) ∧
      ∀ r : Reg, r.val < 50 → z.reg r = (s r).val := by
  let pre (k : ℕ) (z : NatState) := (∀ r : Reg, r.val < 50 → z.reg r = (s r).val) ∧
    z.reg 53 = k ∧ z.reg 54 = 1 ∧ z.reg 55 = 2 ∧ z.reg 56 = 3 ∧
    z.mem = image (s 47).val (s 24).val (s 43).val (2^i.val) bit.toNat (readings m) k
  have regs (k : ℕ) (z : NatState) (hz : pre k z) : z.reg 53 = k ∧ z.reg 46 = 2^n :=
    ⟨hz.2.1, (hz.1 46 (by decide)).trans count⟩
  have step (k : ℕ) (hk : k < 2^n) (u : Bank w) (mm : Memory w) (hp : pre k (.ofWords u mm)) :
      BoundedRun pub macros body u mm 14 (pre (k+1)) := by
    let st := NatState.ofWords u mm
    rcases hp with ⟨hr,r53,r54,r55,r56,mem⟩
    have r24 := hr 24 (by decide); have r43 := hr 43 (by decide); have r47 := hr 47 (by decide)
    have r44 := (hr 44 (by decide)).trans scale; have r45 := (hr 45 (by decide)).trans digit
    have hscale : 0 < 2^i.val := pow_pos (by decide) _
    have hindex := (VertexIndex.insert_lt i bit ⟨k,hk⟩).trans_le indices
    change 2^i.val*(2*(k/2^i.val)+bit.toNat)+k%2^i.val < 2^w at hindex
    have hmul : 2*(k/2^i.val)+bit.toNat ≤ 2^i.val*(2*(k/2^i.val)+bit.toNat) :=
      Nat.le_mul_of_pos_left _ hscale
    have safe : body.fixedSafe w (readings pub) st := by
      simp (config := {decide := true}) [body, Code.block, Code.fixedSafe, Code.fixedEval,
        Code.evalNat, Code.safeReadOnly, addressOpFits, addressOp, st,
        r44,r45,r47,r53,r54,r55,r56, hscale]
      omega
    apply (body.runFixed pub macros u mm safe).mono (by decide)
    intro z he
    subst z
    refine ⟨fun r h => (body.fixedEval_protected _ st (by decide) r h).trans (hr r h), ?_⟩
    simp (config := {decide := true}) [body, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, r24,r43,r44,r45,r47,r53,r54,r55,r56, mem, image, insertBit]
  have hs : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    change 0 < 2^w ∧ 1 < 2^w ∧ 2 < 2^w ∧ 3 < 2^w
    omega
  have init := (setup.runFixed pub macros s m hs).mono (show setup.slots ≤ 4 by decide) (Q := pre 0) (by
    intro z hz
    subst z
    refine ⟨fun r hr => setup.fixedEval_protected _ _ (by decide) r hr, ?_⟩
    simp (config := {decide := true}) [setup, Code.block, Code.fixedEval, Code.evalNat, image, NatState.ofWords])
  exact (init.seq fun u mm hu => run_counted_loop pub macros 53 46 body (2^n) 14 pre regs step 0
    (Nat.zero_le _) u mm hu).mono (by simp; omega) fun _ hz => ⟨hz.2.2.2.2.2,hz.1⟩

/-- The triple ordinal is exactly the ordinal used by the selected local-table
reader for the owned vertex. -/
theorem image_vertex {n d blocks : ℕ} (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (j : Fin (2^n)) (base packet selector : ℕ) (before : ℕ → ℕ) :
    image base packet selector (2^i.val) (ownerBit i p.1.2 high).toNat before (2^n) (base+3*j.val+2) =
      (Tally.vertexOrder (n+1) (owned p i high j).val).val :=
  (image_at j.isLt base packet selector _ _ before).2.2.trans (number_owned p i high j).symm

end RoutingISA.OwnedVertex

end BorderVNP
end Computability
end OAI

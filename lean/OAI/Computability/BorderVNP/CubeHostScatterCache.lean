import OAI.Computability.BorderVNP.CubeHostScatterRows
import OAI.Computability.BorderVNP.CubeHostScatterCoupling

/-! # Resolving physical label, ordinal, metadata and endpoint pointers on an owned live row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Native cache fill after the owner check. Registers 15 through 22 are the exact
per-cable ABI for the inner bit copy. -/
def cache (side : Bool) : Code := .block [
  .constant 21 (if side then 1 else 0),
  .binary .add 36 6 31,.load 36 36,.binary .add 37 6 32,.load 37 37,
  .binary .mul 16 36 7,.binary .add 16 16 37,.binary .add 37 8 13,.load 17 37,
  .binary .mul 37 3 16,.binary .add 37 11 37,.load 18 37,.binary .add 37 37 1,.load 19 37,
  .binary .add 37 37 1,.load 20 37,.binary .add 34 34 1,.load 22 34,
  .binary .mul 37 2 13,.binary .add 37 10 37,.binary .add 37 37 21,.load 37 37,.binary .add 22 22 37]

set_option maxHeartbeats 2000000 in
/-- Execute all address calculations and reads of the native scatter ABI on the actual input rows. -/
theorem run_cache {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {i : ℕ} (hi : i < l.count) (side : Bool)
    (s : Bank w) (m : Memory w) (h : Owner l before i side (.ofWords s m))
    (frozen : l.Frozen before (readings m)) (owned : l.Owned before i side) :
    BoundedRun pub macros (cache side) s m (cache side).slots (fun z => l.Ready z ∧ z.reg 13 = i ∧
      (l.cached before i side).Ready z ∧ z.mem = readings m) := by
  let z := NatState.ofWords s m
  have r0 : z.reg 0 = 0 := h.ready 0 (by decide)
  have r1 : z.reg 1 = 1 := h.ready 1 (by decide)
  have r2 : z.reg 2 = 2 := h.ready 2 (by decide)
  have r3 : z.reg 3 = 3 := h.ready 3 (by decide)
  have r6 : z.reg 6 = l.labels := h.ready 6 (by decide)
  have r7 : z.reg 7 = l.alphabet := h.ready 7 (by decide)
  have r8 : z.reg 8 = l.ordinals := h.ready 8 (by decide)
  have r10 : z.reg 10 = l.relative := h.ready 10 (by decide)
  have r11 : z.reg 11 = l.pairs := h.ready 11 (by decide)
  have r12 : z.reg 12 = l.singles := h.ready 12 (by decide)
  have r13 : z.reg 13 = i := h.index
  have r15 : z.reg 15 = l.width before i := h.fields.1
  have r24 : z.reg 24 = l.packets := h.ready 24 (by decide)
  have r25 : z.reg 25 = l.blocks := h.ready 25 (by decide)
  have r26 : z.reg 26 = l.bc := h.ready 26 (by decide)
  have r27 : z.reg 27 = l.bankWidth := h.ready 27 (by decide)
  have r28 : z.reg 28 = l.selectorWidth := h.ready 28 (by decide)
  have r31 : z.reg 31 = l.cell before i false := h.fields.2.1
  have r32 : z.reg 32 = l.cell before i true := h.fields.2.2
  have r34 : z.reg 34 = l.cells+2*l.cell before i side := h.pointer
  have rd (a : ℕ) (ha : a ∈ l.rowReads before i side) : z.mem a = before a := frozen.read hi side a ha
  have ha := fit.rowFit i hi side owned
  let a := l.pairs + 3*l.key before i
  let s0 := l.labels+l.cell before i false
  let s1 := l.labels+l.cell before i true
  let e0 := l.cells+2*l.cell before i side+1
  let e1 := l.relative+2*i+side.toNat
  have rs0 := rd s0 (by simp [Layout.rowReads,s0])
  have rs1 := rd s1 (by simp [Layout.rowReads,s1])
  have rord := rd (l.ordinals+i) (by simp [Layout.rowReads])
  have ra := rd a (by simp [Layout.rowReads,a])
  have rb := rd (a+1) (by simp [Layout.rowReads,a])
  have rc := rd (a+1+1) (by simp [Layout.rowReads,a,Nat.add_assoc])
  have re0 := rd e0 (by simp [Layout.rowReads,e0])
  have re1 := rd e1 (by simp [Layout.rowReads,e1])
  have ka : before s0*l.alphabet+before s1 = l.key before i := rfl
  have a0 := ha s0 (by simp [Layout.rowReads,s0])
  have a1 := ha s1 (by simp [Layout.rowReads,s1])
  have ao := ha (l.ordinals+i) (by simp [Layout.rowReads])
  have ab := ha (a+2) (by simp [Layout.rowReads,a])
  have ae0 := ha e0 (by simp [Layout.rowReads,e0])
  have ae1 := ha e1 (by simp [Layout.rowReads,e1])
  have adest : before e0 + before e1 < 2^w := by
    have hh := fit.destFit i hi side owned
    change before e0 + before e1 + _ ≤ 2^w at hh
    have hpos := owned.1
    omega
  have sf : (if side then (1 : Word 8) else 0).val = side.toNat := by cases side <;> rfl
  have spos : side.toNat < 2^w := (Bool.toNat_le side).trans_lt (by have := (s 3).isLt; change (s 3).val = 3 at r3; omega)
  dsimp only [s0,s1,a,e0,e1] at rs0 rs1 re0 re1 ka ra rb rc adest
  have safe : (cache side).fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [cache,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,addressOpFits,addressOp,r1,r2,r3,r6,r7,r8,r10,r11,r13,r31,r32,r34,sf,spos,
      rs0,rs1,ka,re0,re1,adest]
    dsimp only [s0,s1,a,e0,e1] at *
    omega
  have run := keep_directory ((cache side).runFixed pub macros s m safe) (by cases side <;> decide) h.ready h.index
  apply run.mono le_rfl
  rintro _ ⟨hr,hi',rfl⟩
  refine ⟨hr,hi',?_,?_⟩
  · change BitFields.Ready (l.cached before i side) ((cache side).fixedEval (readings pub) z)
    simp (config := {decide := true}) [cache,Code.block,Code.fixedEval,Code.evalNat,addressOp,BitFields.Ready,
      BitFields.read,Layout.cached,Layout.dest,r0,r1,r2,r3,r6,r7,r8,r10,r11,r12,r13,r15,r24,r25,r26,r27,r28,
      r31,r32,r34,sf,rs0,rs1,ka,rord,ra,rb,rc,re0,re1]
  · simp [cache,Code.block,Code.fixedEval,NatState.ofWords]

end Cube.HostScatter

end BorderVNP
end Computability
end OAI

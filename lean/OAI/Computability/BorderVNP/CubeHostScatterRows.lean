import OAI.Computability.BorderVNP.CubeHostScatterLayout

/-! # Native row and owner tests before entering the per-bit host scatter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The public registers and the outer index survive the read-only address stages. -/
def KeepsDirectory (c : Code) : Prop := ∀ j : Reg,
  (j.val ≤ 13 ∨ 24 ≤ j.val ∧ j.val ≤ 29) → c.keeps j = true

instance (c : Code) : Decidable (KeepsDirectory c) := inferInstanceAs (Decidable (∀ j : Reg, (j.val ≤ 13 ∨ 24 ≤ j.val ∧ j.val ≤ 29) → c.keeps j = true))

/-- Extend a bounded run with the configuration and index retained by its actual instruction sequence. -/
theorem keep_directory {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {l : Layout} {i cost : ℕ} {P : NatState → Prop} {s : Bank w} {m : Memory w}
    (run : BoundedRun pub macros c s m cost P) (hk : KeepsDirectory c)
    (ready : l.Ready (.ofWords s m)) (idx : (s 13).val = i) :
    BoundedRun pub macros c s m cost (fun z => l.Ready z ∧ z.reg 13 = i ∧ P z) := by
  obtain ⟨es,t,mt,hr,hc,hpost⟩ := run
  refine ⟨es,t,mt,hr,hc,?_,?_,hpost⟩
  · intro j hj
    have keep := hr.keepsReg (hk j (by omega))
    exact (congrArg Fin.val keep).trans (ready j hj)
  · exact (congrArg Fin.val (hr.keepsReg (hk 13 (by decide)))).trans idx

/-- Load both cells and the width from the actual three-word record. -/
def readRow : Code := .block [
  .binary .mul 30 3 13,.binary .add 30 4 30,.load 31 30,
  .binary .add 30 30 1,.load 32 30,.binary .add 30 30 1,.load 15 30]

/-- Actual input columns resident before a team decides whether it owns this endpoint. -/
structure Header (l : Layout) (before : ℕ → ℕ) (i : ℕ) (z : NatState) : Prop where
  /-- Stable configuration and row index. -/
  ready : l.Ready z
  /-- Current physical cable row. -/
  index : z.reg 13 = i
  /-- Actual width and both old cell numbers. -/
  fields : z.reg 15 = l.width before i ∧ z.reg 31 = l.cell before i false ∧ z.reg 32 = l.cell before i true

/-- Every address in this row's physical input list still contains its original word. -/
theorem Layout.Frozen.read {l : Layout} {before mem : ℕ → ℕ} (f : l.Frozen before mem) {i : ℕ}
    (hi : i < l.count) (side : Bool) (x : ℕ) (hx : x ∈ l.rowReads before i side) :
    mem x = before x := f x ⟨i,hi,side,Or.inl hx⟩

/-- The actual native descriptor read returns the untouched source, destination and width words. -/
theorem run_readRow {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {i : ℕ} (hi : i < l.count)
    (s : Bank w) (m : Memory w) (ready : l.Ready (.ofWords s m)) (idx : (s 13).val = i)
    (frozen : l.Frozen before (readings m)) :
    BoundedRun pub macros readRow s m readRow.slots (fun z => Header l before i z ∧ z.mem = readings m) := by
  let z := NatState.ofWords s m
  have r1 : z.reg 1 = 1 := ready 1 (by decide)
  have r3 : z.reg 3 = 3 := ready 3 (by decide)
  have r4 : z.reg 4 = l.cables := ready 4 (by decide)
  have r13 : z.reg 13 = i := idx
  have rsrc : z.mem (l.cables+3*i) = l.cell before i false := frozen.read hi false _ (by simp [Layout.rowReads])
  have rdst : z.mem (l.cables+3*i+1) = l.cell before i true := frozen.read hi false _ (by simp [Layout.rowReads])
  have rwid : z.mem (l.cables+3*i+1+1) = l.width before i := frozen.read hi false (l.cables+3*i+2) (by simp [Layout.rowReads])
  have safe : readRow.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [readRow,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,addressOpFits,addressOp,r1,r3,r4,r13]
    have := fit.directory
    omega
  have base := keep_directory (readRow.runFixed pub macros s m safe) (by decide) ready idx
  apply base.mono le_rfl
  rintro _ ⟨hready,hi',rfl⟩
  change Header l before i (readRow.fixedEval (readings pub) z) ∧ (readRow.fixedEval (readings pub) z).mem = z.mem
  refine ⟨⟨hready,hi',?_⟩,?_⟩ <;>
    simp (config := {decide := true}) [readRow,Code.block,Code.fixedEval,Code.evalNat,addressOp,
      r1,r3,r4,r13,rsrc,rdst,rwid]

/-- The real cell-owner lookup uses the first word of the two-word per-cell directory. -/
def readOwner (side : Bool) : Code := .block [
  .copy 33 (if side then 32 else 31), .binary .mul 34 2 33,.binary .add 34 9 34,.load 35 34]

/-- Resident header and owner address, before the conditional branch. -/
structure Owner (l : Layout) (before : ℕ → ℕ) (i : ℕ) (side : Bool) (z : NatState) extends Header l before i z where
  /-- Pointer to this cell's two-word owner and bit-bank entry. -/
  pointer : z.reg 34 = l.cells+2*l.cell before i side
  /-- Actual team read from the pointed cell. -/
  owner : z.reg 35 = l.owner before i side

/-- Executing the live row's owner lookup does not visit any of its bits. -/
theorem run_readOwner {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {i : ℕ} (hi : i < l.count) (side : Bool)
    (s : Bank w) (m : Memory w) (head : Header l before i (.ofWords s m)) (frozen : l.Frozen before (readings m))
    (nonzero : l.width before i ≠ 0) (cross : l.cell before i false ≠ l.cell before i true) :
    BoundedRun pub macros (readOwner side) s m (readOwner side).slots (fun z => Owner l before i side z ∧ z.mem = readings m) := by
  let z := NatState.ofWords s m
  have r2 : z.reg 2 = 2 := head.ready 2 (by decide)
  have r9 : z.reg 9 = l.cells := head.ready 9 (by decide)
  have r15 : z.reg 15 = l.width before i := head.fields.1
  have r31 : z.reg 31 = l.cell before i false := head.fields.2.1
  have r32 : z.reg 32 = l.cell before i true := head.fields.2.2
  have ptr := fit.ownerFit i hi side nonzero cross
  have rmem : z.mem (l.cells+2*l.cell before i side) = l.owner before i side := frozen.read hi side _ (by simp [Layout.rowReads])
  have safe : (readOwner side).fixedSafe w (readings pub) z := by
    cases side <;> simp (config := {decide := true}) [readOwner,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,addressOpFits,addressOp,r2,r9,r31,r32] <;> omega
  have base := keep_directory ((readOwner side).runFixed pub macros s m safe) (by cases side <;> decide) head.ready head.index
  apply base.mono le_rfl
  rintro _ ⟨hready,hidx,rfl⟩
  change Owner l before i side ((readOwner side).fixedEval (readings pub) z) ∧ ((readOwner side).fixedEval (readings pub) z).mem = z.mem
  refine ⟨⟨⟨hready,hidx,?_⟩,?_,?_⟩,?_⟩
  all_goals cases side <;> simp (config := {decide := true}) [readOwner,Code.block,Code.fixedEval,Code.evalNat,
    addressOp,r2,r9,r15,r31,r32,rmem]

end Cube.HostScatter

end BorderVNP
end Computability
end OAI

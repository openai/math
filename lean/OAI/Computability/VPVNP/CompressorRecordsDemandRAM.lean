import OAI.Computability.VPVNP.CompressorRecordsBundleWords
import OAI.Computability.VPVNP.CompressorSlotOwnerAgreement

/-!
# Materializing the selected roles of each old shrinking arc

The scan cursor uses the old physical outgoing-port order. The output record address
uses the old arc's absolute ID in the surviving-slot directory, which moves the tag
and port ahead of the mask and keeps the residual lane least significant. Read both
thickness bits, follow the thin C endpoint for A and B, and read the opposite
endpoint's chosen owner for D. All arcs have a CD indicator, including thick–thick
arcs that occupy unused addresses of the genuine slot range.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DemandRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open ShrinkRAM (div mod select)
open scoped Fin.CommRing

variable {w : ℕ}

/-- Straight-line instruction lists for the demand worker, which uses 24 registers and 11
public operands. -/
abbrev Ops := List (Op 24 11)

/-- Degree, residual/tag/mask radices, an unused offset, the actual outgoing,
thickness, owner, assigned and target columns, and the absolute arc-record base. -/
def visit : Ops :=
  [.stateWord 0,.publicWord 1 0,.publicWord 2 1,.publicWord 3 2,.publicWord 4 3,
    .constant 23 1,.binary .div 5 0 1,.binary .mod 6 0 1,
    .publicWord 13 5,.binary .add 13 13 0,.read 7 13,.binary .div 7 7 1,
    .publicWord 13 6,.binary .add 14 13 5,.read 8 14,.binary .add 14 13 7,.read 9 14,
    .binary .sub 10 7 5,.binary .mul 10 8 10,.binary .add 11 5 10,.binary .sub 12 7 10,
    .publicWord 13 8,.binary .add 13 13 11,.read 15 13,.binary .div 15 15 1,
    .publicWord 13 9,.binary .add 13 13 11,.read 16 13,
    .publicWord 13 7,.binary .add 13 13 12,.read 17 13,
    .binary .mul 18 8 9,.binary .sub 18 23 18,
    .binary .mod 19 5 2,.binary .div 5 5 2,.binary .mod 20 5 3,.binary .div 5 5 3,
    .binary .mod 21 5 1,.binary .div 5 5 1,.binary .mod 22 5 4,.binary .div 5 5 4,
    .binary .mul 5 5 3,.binary .add 5 5 20,.binary .mul 5 5 1,.binary .add 5 5 6,
    .binary .mul 5 5 4,.binary .add 5 5 22,.binary .mul 5 5 1,.binary .add 5 5 21,
    .binary .mul 5 5 2,.binary .add 5 5 19,.constant 22 2,.binary .add 22 22 22,.binary .mul 5 22 5,
    .publicWord 13 10,.binary .add 13 13 5,.write 13 15,
    .binary .add 13 13 23,.write 13 16,.binary .add 13 13 23,.write 13 17,
    .binary .add 13 13 23,.write 13 18,.binary .add 0 0 23]

/-- Address of an old arc's four-word demand record, obtained by permuting the scan index into
absolute arc order and adding the output table base. -/
def address (p : Fin 11 → Word w) (i : Word w) : Word w :=
  let f := BundleRAM.decode p i
  let hi := (((f.base*p 2+f.tag)*p 0+f.slot)*p 3+f.mask)*p 0+f.label
  let lane := mod (BundleRAM.sourceSite p i) (p 1)
  p 10 + 4*(hi*p 1+lane)

/-- Order the physical source and target according to the source's thickness bit, putting the C
endpoint first on a CD arc. -/
def endpoints (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : Word w × Word w :=
  let src := BundleRAM.sourceSite p i
  let dst := BundleRAM.targetSite p m i
  let thick := m (p 6+src).val
  let delta := thick*(dst-src)
  (src+delta,dst-delta)

/-- The demand record of an old arc, storing its packed A, B and D site numbers and the CD
indicator. -/
structure Roles (α : Type) where
  /-- Packed source site of the bundle assigned to the thin C endpoint on a CD arc. -/
  A : α
  /-- Packed target site of the bundle assigned to the thin C endpoint on a CD arc. -/
  B : α
  /-- Packed site selected by the placement for the opposite, D endpoint on a CD arc. -/
  D : α
  /-- The CD indicator, set to one unless both endpoints of the old arc are thick. -/
  cd : α

/-- Read the placement data at the two endpoints to compute A, B and D, and use their thickness
bits to compute the CD flag. -/
def roles (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : Roles (Word w) :=
  let s := BundleRAM.sourceSite p i
  let t := BundleRAM.targetSite p m i
  let z := endpoints p m i
  ⟨div (m (p 8+z.1).val) (p 0),m (p 9+z.1).val,m (p 7+z.2).val,1-m (p 6+s).val * m (p 6+t).val⟩

/-- Trace of one demand visit, reading the old target, endpoint thicknesses and selected
placement data before writing the four demand fields. -/
def events (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let s := BundleRAM.sourceSite p i
  let t := BundleRAM.targetSite p m i
  let z := endpoints p m i
  let v := roles p m i
  let a := address p i
  List.replicate 10 .tick ++ [.read (p 5+i) (m (p 5+i).val),.tick,.tick,.tick,
    .read (p 6+s) (m (p 6+s).val),.tick,.read (p 6+t) (m (p 6+t).val)] ++
    List.replicate 6 .tick ++ [.read (p 8+z.1) (m (p 8+z.1).val),.tick,.tick,.tick,
    .read (p 9+z.1) v.B,.tick,.tick,.read (p 7+z.2) v.D] ++ List.replicate 25 .tick ++
    [.write a v.A,.tick,.write (a+1) v.B,.tick,.write (a+1+1) v.D,.tick,
     .write (a+1+1+1) v.cd,.tick]

/-- Write the computed A, B, D and CD words to the four consecutive cells of the old arc's
demand record. -/
def store (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : Memory w :=
  let a := address p i
  let v := roles p m i
  writeMemory (writeMemory (writeMemory (writeMemory m a v.A) (a+1) v.B)
    (a+1+1) v.D) (a+1+1+1) v.cd

theorem visit_after (p : Fin 11 → Word w) (m : Memory w) (i : Word w) :
    after m (events p m i) = store p m i := rfl

theorem visit_work (p : Fin 11 → Word w) (m : Memory w) (i : Word w) :
    (events p m i).length = 64 ∧ countProbes (events p m i) = 10 := ⟨rfl,rfl⟩

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 8192 in
private theorem visit_trace (p : Fin 11 → Word w) (m : Memory w) (i : Word w) (rs : Regs w 24) :
    ∃ rs', trace p i visit rs m = some (events p m i, rs', store p m i) ∧ rs' 0 = i+1 := by
  simp (config := {decide := true}) [visit, trace, Op.effect, Function.update, BinaryOp.eval,
    events, roles, address, endpoints, BundleRAM.decode, BundleRAM.sourceSite, BundleRAM.targetSite,
    div, mod, store]
  repeat' apply And.intro
  all_goals first | rfl | (norm_num1; rfl)

theorem visit_native (p : Fin 11 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 65 (M.program.start i) m [] = some ⟨events p m i,some (i+1)⟩ := by
  obtain ⟨rs, ht, hr⟩ := visit_trace p m i (fun _ => 0)
  let M := (template visit 0).instantiate w p
  change execute M.program (1+visit.length) ⟨M.entry,i,fun _=>0,fun _=>0⟩ m [] = _
  rw [execute_template,run_eq_trace,ht]; simp [hr]

end CompressorRecords.DemandRAM

end VPVNP
end Computability
end OAI

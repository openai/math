import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentResetSpanDispatch
import OAI.Hierarchy.DescentPaidResidentCensus

namespace OAI
/-! # Control bits and retained words in empty reset operand cells -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentResetAttachments
open DescentDenseHostOrder Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentPackedZip
open DescentActorRaster DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage.Prepare
open scoped Classical Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
variable {H : ℕ} (fits : Fintype.card B.next.V≤H)
open DescentPaidResidentCount

theorem actualBit_unoccupied (host : Fin H) (group : Fin (S.groupCount (i+1))) (block : DescentColonies.Block k)
    (missing : ¬ ∃u, occupies B.next.placement (Equiv.refl _)
      (B.next.vertex.trans (Fin.castLEEmb fits)) host group block u) :
    actualBit B fits host group block=0 :=by
  unfold actualBit
  exact ite_eq_right missing

theorem actualBit_outside (host : Fin H) (group : Fin (S.groupCount (i+1))) (block : DescentColonies.Block k)
    (padding : Fintype.card B.next.V≤host.val) : actualBit B fits host group block=0 :=by
  apply actualBit_unoccupied
  rintro ⟨site,h,_⟩
  have same:=congrArg Fin.val h
  exact (Nat.not_lt_of_ge padding) (same ▸ (B.next.vertex ((B.next.placement.pos site).2)).isLt)

theorem actualBit_no_site (host : Fin H) (group : Fin (S.groupCount (i+1))) (block : DescentColonies.Block k)
    (inside : host.val<Fintype.card B.next.V)
    (missing : ¬∃u,occupies B.next.placement (Equiv.refl _) B.next.vertex ⟨host.val,inside⟩ group block u) :
    actualBit B fits host group block=0 :=by
  apply actualBit_unoccupied
  rintro ⟨site,h,g,x⟩
  have same : (B.next.vertex (B.next.placement.pos site).2).val = host.val :=
    congrArg (fun j : Fin H => j.val) h
  exact missing ⟨site,Fin.ext same,g,x⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentDenseHostOrder DescentResetOperandSetup DescentResetPublicOperandBook
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "C" => a.successor.setup
local notation "r" => a.successor.middle.rootDepth
local notation "cfg" => publicOperands z roots menu.payload
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
variable (Y : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
    Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
variable (j : Fin a.successor.setup.retained.outputs) (block : Fin a.successor.setup.placement.blocks)
variable (host : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
local notation "table" => DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  menu.keep name Y j block
local notation "ret" => (((table) host g).val : Cell (C).fieldBits)
variable (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (index : Fin (publicOperands z roots menu.payload).mouths) (f : Fin 7)
local notation "pub" => (cfg).column z.board (C).fieldBits (some f) index x
local notation "reg" => (cfg).reg x
local notation "loc" => (finProdFinEquiv.symm index : Fin (cfg).args × Fin (cfg).nodes)
local notation "prv" => ((cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
  (loc).2.val (loc).1.val f.succ (reg) : Cell (C).fieldBits)
variable (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → ((publicOperands z roots menu.payload).reg x 1).val=0)
variable (physical : ∀hv : host.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
    ((publicOperands z roots menu.payload).reg x 3).val=(a.successor.setup.placement.shape (name ⟨host.val,hv⟩)).val)

/-- If the real actor mask is clear, both hardware-produced fields vanish. A retained
word can survive only through the actual selected earlier table. -/
theorem inactive_span (disabled : ((cfg).oldConfig.header ((cfg).basic x) 0).val=0) :
    menu.spanValue name Y j block host g x index f blank physical=ret :=by
  have pv : (cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
      (loc).2.val (loc).1.val f.succ (reg)=0:=by
    simp [DescentRotorOperandQueryROM.Shape.flatReg,blank disabled]
  have publicEmpty : (cfg).mixed z.board (loc).2.val (loc).1.val x=none:=by
    simp [DescentResetPublicOperandBook.Config.mixed,disabled]
  have pb : pub=0:=by simp only [DescentResetPublicOperandBook.Config.column,publicEmpty]
  apply Fin.ext
  simp only [spanValue,pv,Nat.cast_zero,pb,Fin.val_zero,Nat.add_zero]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI

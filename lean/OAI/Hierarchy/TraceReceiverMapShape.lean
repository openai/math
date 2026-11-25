import OAI.Hierarchy.TraceReceiverTaskShape
import OAI.Hierarchy.TraceReceiverMapProgram
import OAI.ThreeFlat.RAM.TickTerminalRoot

namespace OAI
/-! # Native hardware of the per-root saved-map loop -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure TickTerminalRoot

private def seedBinds := (TraceReceiverMapSave.seedWord 1 0 0 0).binds
private def copyBinds := (TraceReceiverMapSave.expression 1 0 0).binds

private theorem seed_binds (W head tasks ordinal : ℕ) :
    (TraceReceiverMapSave.seedWord W head tasks ordinal).binds=seedBinds := by
  simp [seedBinds,TraceReceiverMapSave.seedWord,Term.select,Term.binary,Term.load,Term.literal,Term.binds]

private theorem copy_binds (W source head : ℕ) :
    (TraceReceiverMapSave.expression W source head).binds=copyBinds := by
  simp [copyBinds,TraceReceiverMapSave.expression,Term.binary,Term.load,Term.literal,Term.binds]

def mapHardware := rootLabels+rootRegisters+rootSlots+((11+0+4*seedBinds)+(18+4*copyBinds))

private theorem counted_additions (s c old full : ℕ) (h : 10+old=full) :
    10+(s+(old+c))=full+(s+c) := by omega

theorem map_size (W : ℕ) (A : Arena) (tasks header : ℕ) :
    size (maps W A tasks header)=mapHardware := by
  obtain ⟨hl,hr,hs⟩:=many_shape W A
  have old : size (many W A)=rootLabels+rootRegisters+rootSlots := by
    unfold size
    rw [hl,hr,hs]
  rw [many,size_counted] at old
  rw [maps,size_counted,size_seq,TraceReceiverMapSave.one,size_seq,
    TraceReceiverMapSave.procedure,size_scan,TraceReceiverMapSave.seed,size_writing,
    seed_binds,copy_binds]
  exact counted_additions _ _ _ _ old

end Hierarchy.TraceReceiverTasks

end OAI

import OAI.ThreeFlat.Diagonal.TraceJournalRows
import OAI.Hierarchy.TraceReceiverArchive

namespace OAI
/-! # Native scanner inputs from the rows of a selected physical archive -/
namespace ThreeFlat.Diagonal.NavigationPass.TraceRecovery
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage PhysicalStage.Run NavigationDirectory HistoryContraction CompressorPacking Native
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

open Hierarchy.TraceReceiverArchive

/-- The exact three geometry obligations of the numerical lane scanner, plus
identification of its last row with the terminal factor's physical ordinal. -/
theorem scanner_inputs {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (path : r.ArchivePath h C O) (data : LayerData O.layer)
    (K dp dir H M : ℕ) (steps : List Stage) (c : Cursor) (mem : ℕ→ℕ) (initial : Layer→Prop)
    (num : r.FinalNumbered h C O path)
    (rows : stagePost K steps c O.layer (·<dp) mem H M initial (r.archiveList h C O path data)
      (r.finalArchive h C O path).1)
    (physical : ∀ pre op post, steps=pre++op::post →
      mem (dir+(64*pre.length+44))=(allocate K (finish K pre c) op).words 44) :
    let bases := ownerBases r h C O path
    bases.length=steps.length ∧
    (∀ t : Fin bases.length, mem (dir+44+64*t.val)=bases[t.val]) ∧
    (∀ (t : Fin bases.length) (v : A.Site),
      bases[t.val]+((bases.take t.val).foldl (fun j b=>mem (b+j)) (O.ord v).val)<dp) ∧
    (∀ v : A.Site, bases.foldl (fun j b=>mem (b+j)) (O.ord v).val=(r.terminalOrderEquiv h (r.plan.destination h v)).val) := by
  intro bases
  obtain ⟨chart,last,stored⟩:=rows
  have length := ownerBases_length r h C O path data K steps c chart
  refine ⟨length,?_,?_,?_⟩
  · intro t
    have ht : t.val<steps.length := by simpa only [←length] using t.isLt
    let pre:=steps.take t.val
    let op:=steps[t.val]
    let post:=steps.drop (t.val+1)
    have split : steps=pre++op::post := by
      dsimp [pre,op,post]
      rw [List.getElem_cons_drop ht,List.take_append_drop]
    have n : pre.length=t.val := by simp [pre,Nat.min_eq_left ht.le]
    have field := owner_base r h C O path data K pre op post c (split ▸ chart)
    have actual := physical pre op post split
    rw [n] at field actual
    rw [List.getElem?_eq_getElem t.isLt] at field
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using actual.trans (Option.some.inj field).symm
  · intro t v
    exact prefix_extent r h C O path data mem (·<dp) (fun q hq=>(stored q hq).parents)
      (fun q hq=>(stored q hq).ownerCells) v t.val t.isLt
  · intro v
    rw [←follow_eq_foldl]
    exact follow_terminalOrder r h C O path data mem (fun q hq=>(stored q hq).parents) num v


end
end ThreeFlat.Diagonal.NavigationPass.TraceRecovery

end OAI

import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge

namespace OAI
/-! # Reading the selected run's chronological parent from its published word -/
namespace Hierarchy.HistorySelectedChildren
open ThreeFlat RAM Diagonal
open Diagonal.HistoryContraction Diagonal.PhysicalStage RAM.NavigationNodeRows Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

/-- Instantiate the chronological parent read from the resident eight-word
node pass. This consumes exactly the rows exported by the node publisher. -/
theorem archive_parentAt {d l W : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (bank : Banks) (out : Memory W)
    (stored : r.ArchiveRowsStored bank (fun a=>(out a).val) h C O p) (zero : O.layer.first=0)
    (final roots : ℕ) (first : final=(r.finalArchive h C O p).1.first)
    (count : roots=(r.finalArchive h C O p).1.count) :
    let chron:=r.archiveDirectory h C O p bank (fun a=>(out a).val) stored zero final roots first count
    ∀j : Fin (final+roots),j.val<chron.firstFinal →
      out (bank.nodes+8*j.val+1)=((chron.parent j).val:Word W) := by
  intro chron j early
  have equality := r.archiveDirectory_parent h C O p bank (fun a=>(out a).val) stored zero
    final roots first count j early
  exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun a : ℕ=>(a:Word W)) equality.symm)

end
end Hierarchy.HistorySelectedChildren

end OAI

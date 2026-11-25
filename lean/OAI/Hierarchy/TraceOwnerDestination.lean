import OAI.Hierarchy.TraceParentScanner
import OAI.Hierarchy.TraceIntervalScanner
import OAI.Hierarchy.TraceReceiverArchive

namespace OAI
/-! # The destination array of a decoded physical trace -/
noncomputable section
namespace Hierarchy.TraceAdmission.Parents
open ThreeFlat Diagonal PhysicalStage RAM RAM.NavigationNodeRows
open Computability.VPVNP.BurstRAM TraceReceiverArchive
open scoped Fin.CommRing
variable {F : Type} [Field F] {W d l lanes : ℕ} {A : State d l}

theorem loaded_after_trace (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (layer : LayerData O.layer)
    (mem : Memory W) (source : ∀q∈r.archiveList h C O p layer,
      ParentReads q.parent q.owners (fun i=>(mem i).val))
    (initial : Fin lanes→A.Site) (seed : ∀ j,(O.ord (initial j)).val=j.val)
    (base : ℕ) :
    let bases := ownerBases r h C O p
    let L := r.finalArchive h C O p
    let dest := fun j => L.2 ((r.finalSite h).symm (r.plan.destination h (initial j)))
    let out := fillSegment base ((bases.length+1)*lanes)
      (file base lanes (walkPrefix (fun i=>(mem i).val) bases)) mem
    TraceIntervalScanner.Loaded (base+bases.length*lanes) dest out := by
  intro bases last dest out j
  have finish := follow_destination r h C O p layer (fun i=>(mem i).val) source (initial j)
  rw [follow_eq_foldl,seed] at finish
  rw [show out (base+bases.length*lanes+j.val) =
      (walkPrefix (fun i=>(mem i).val) bases bases.length j.val : Word W) from
      final_row base lanes bases.length _ mem j]
  exact congrArg (fun i : ℕ=>(i:Word W)) (by simpa [walkPrefix,List.take_length,bases,dest,last] using finish)

open NavigationPass NavigationDirectory

/-- The pointer table read by the native owner scanner is already present
in the published 64-word headers; the intermediate ordinals need no advice. -/
theorem mounted_arrays (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (data : LayerData O.layer)
    (K : ℕ) (ops : List Stage) (c : Cursor) (dir : ℕ) (m : Memory W)
    (rows : (r.archiveList h C O p data).map (fun q=>(⟨q.layer,q.parent⟩ : Layers))=
      nodeLayers K ops c O.layer)
    (mounted : ∀ i v,(tape K ops c)[i]?=some v→(m (dir+i)).val=v)
    (t : Fin (ownerBases r h C O p).length) :
    (m ((dir+44)+64*t.val)).val=(ownerBases r h C O p)[t.val] := by
  have ht : t.val<ops.length :=
    t.isLt.trans_eq (ownerBases_length r h C O p data K ops c rows)
  have split : ops.take t.val ++ ops[t.val] :: ops.drop (t.val+1)=ops := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have «prefix» : (ops.take t.val).length=t.val := by simp [List.length_take,ht.le]
  have point := mounted_owner_base r h C O p data K (ops.take t.val) ops[t.val]
    (ops.drop (t.val+1)) c dir (fun i=>(m i).val) (by simpa only [split] using rows)
    (by simpa only [split] using mounted)
  rw [«prefix»,List.getElem?_eq_getElem t.isLt] at point
  simpa only [show dir+44+64*t.val=dir+(64*t.val+44) by omega] using (Option.some.inj point).symm

/-- The first resource slot is read directly from the charged terminal archive.
Both indices here are the same physical ordinals returned by the owner scan. -/
theorem charged_source (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (mem : Memory W)
    (stored : r.ArchiveRowsStored b (fun a=>(mem a).val) h C O p) (start pay : A.Site→ℕ)
    (seed : O.Charged b (fun a=>(mem a).val) start pay) (v : (r.plan.finish h).Site) :
    let L := r.finalArchive h C O p
    (mem (b.charges+2*(L.1.first+(L.2 ((r.finalSite h).symm v)).val))).val =
      b.unitWork*r.chargeAt h C start v := by
  simpa only [archiveColumn, Fin.val_zero, Nat.add_zero] using
    (r.archive_charges h C O p b (fun a=>(mem a).val) stored start pay seed v).1


end Hierarchy.TraceAdmission.Parents

end
end OAI

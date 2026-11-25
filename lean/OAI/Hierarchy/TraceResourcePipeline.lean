import OAI.Hierarchy.TraceOwnerDestination
import OAI.Hierarchy.TraceResourceHandoff

namespace OAI
/-! # From archived parent vectors to a registered row in the public matrix -/
namespace Hierarchy.TraceAdmission.Resources
open Computability.VPVNP.BurstRAM ThreeFlat RAM PhysicalProcedure
open TraceIntervalScanner

/-- Join the actual parent scan, reverse linked-list scatter, two resource strips, and
the final copy to the numerical resource matrix. All program dimensions are public. -/
def registration (W parentCtrl resourceCtrl dp stages dst : ℕ) (p : Parameters ℕ) : Procedure W :=
  ((Parents.scan W parentCtrl).seq
    (procedure W (dp+stages*p.lanes) p.heads p.links p.lanes p.roots)).seq
    (handoff W resourceCtrl dst p)

private theorem retainHeader {W ctrl header dp : ℕ} {p : Parameters ℕ} {m o : Memory W}
    (H : Header ctrl header p m) (ch : ctrl<dp) (bh : header+16≤dp)
    (same : ∀ a<dp,o a=m a) : Header ctrl header p o := by
  refine ⟨by rw [same _ ch]; exact H.pointer,?_,?_,?_,?_,?_⟩
  · rw [same _ (by omega)];exact H.scratch
  · rw [same _ (by omega)];exact H.slength
  · rw [same _ (by omega)];exact H.resource
  · rw [same _ (by omega)];exact H.rlength
  · intro i;rw [same _ (by have:=i.isLt;omega)];exact H.params i

theorem registration_spec {W pc ph rc rh dp directory dst : ℕ} (p : Parameters ℕ)
    (bases : List ℕ) (dest : Fin p.lanes→Fin p.roots) (m : Memory W)
    (parentSpace : Parents.Layout W pc ph dp p.lanes bases.length directory)
    (listSpace : Layout W (dp+bases.length*p.lanes) p.heads p.links p.lanes p.roots)
    (resourceSpace : Room W rc rh p) (resourceHeader : Header rc rh p m)
    (controls : rc<dp) (headers : rh+16≤dp) (target : dst≤p.resources)
    (ctl : (m pc).val=ph) (start : (m ph).val=dp)
    (sz : (m (ph+1)).val=(bases.length+1)*p.lanes)
    (page : (m (ph+2)).val=directory) (n : (m (ph+3)).val=p.lanes)
    (array : ∀ t : Fin bases.length,(m (directory+64*t.val)).val=bases[t.val])
    (extent : ∀ t : Fin bases.length,∀ j<p.lanes,
      bases[t.val]+Parents.walkPrefix (fun a=>(m a).val) bases t.val j<dp)
    (source : let walk:=Parents.walkPrefix (fun a=>(m a).val) bases
      Loaded (dp+bases.length*p.lanes) dest
        (fillSegment dp ((bases.length+1)*p.lanes) (Parents.file dp p.lanes walk) m)) :
    let walk:=Parents.walkPrefix (fun a=>(m a).val) bases
    let first:=fillSegment dp ((bases.length+1)*p.lanes) (Parents.file dp p.lanes walk) m
    (registration W pc rc dp bases.length dst p).Spec (·=m)
      (fun _ out=>∃ linked,Output p.heads p.links dest first linked ∧ out=publicRows dst p linked)
      ((11+(bases.length+1)*p.lanes*(2*(Parents.row pc).work+4)+(9+4*p.roots+10*p.lanes))+
        (ticks rc p+(6+5*resourceLength p))) := by
  intro walk first
  have scan : (Parents.scan W pc).Spec (·=m) (fun _ out=>out=first)
      (11+(bases.length+1)*p.lanes*(2*(Parents.row pc).work+4)) :=
    Parents.scan_of_arrays bases parentSpace m ctl start sz page n array extent
  have initial : ((Parents.scan W pc).seq
      (procedure W (dp+bases.length*p.lanes) p.heads p.links p.lanes p.roots)).Spec (·=m)
      (fun _ out=>∃ mid,mid=first ∧ Output p.heads p.links dest mid out)
      (11+(bases.length+1)*p.lanes*(2*(Parents.row pc).work+4)+(9+4*p.roots+10*p.lanes)) :=
    scan.seq (procedure_spec listSpace dest) (by rintro _ out rfl; exact source)
  have firstEq : ∀ z<dp,first z=m z := fun z hz=>by
    dsimp only [first];simp [fillSegment,Nat.not_le_of_lt hz]
  have listHead : dp≤p.heads := by have:=listSpace.beforeHeads;omega
  have nextHead : dp≤p.links := by have:=listSpace.beforeLinks;omega
  let post (x out : Memory W) := out=publicRows dst p x
  have finish : (handoff W rc dst p).Spec (Output p.heads p.links dest first) post
      (ticks rc p+(6+5*resourceLength p)) := by
    intro a b c M loc reg pub exit installed given cfg mem entry oks
    have keep (z : ℕ) (hz : z<dp) : mem z=m z :=
      (oks.1 _ (.inl (hz.trans_le listHead)) (.inl (hz.trans_le nextHead))).trans (firstEq _ hz)
    exact handoff_spec p resourceSpace mem first (retainHeader resourceHeader controls headers keep)
      dest oks target M loc reg pub exit installed given cfg mem entry rfl
  intro P R K machine
  exact PhysicalProcedure.Procedure.Spec.mono
    (A := registration W pc rc dp bases.length dst p)
    (initial.seq finish (by rintro _ _ ⟨_,rfl,h⟩;exact h))
    (fun _ e=>e) (by
      rintro _ out ⟨mem,⟨_,rfl,lists⟩,h⟩
      exact ⟨mem,lists,h⟩) le_rfl machine

end Hierarchy.TraceAdmission.Resources

end OAI

import OAI.Hierarchy.TraceResourcePipeline
import OAI.ThreeFlat.Diagonal.TraceJournalScanner

namespace OAI
/-! # Native registration of each true terminal factor of a parsed history -/
namespace Hierarchy.TraceAdmission.Resources
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure Computability.VPVNP.BurstRAM
open TraceReceiverArchive
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {W d l : ℕ} {A : State d l}

/-- The public number of rows in the last issued layer equals the number
of tensor factors in every selected history. -/
theorem final_layer_count (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O) (last : Layer)
    (issued : (r.finalArchive h C O path).1=last) :
    Fintype.card (r.plan.finish h).Site=last.count := by
  let out:=r.finalArchive h C O path
  have chart := (r.finalSite h).symm.trans out.2
  exact (Fintype.card_congr chart).trans ((Fintype.card_fin _).trans (congrArg Layer.count issued))

theorem register_recovered (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O) (data : LayerData O.layer)
    (K dp dir H Q : ℕ) (steps : List Stage) (c : Cursor) (m : Memory W) (initial : Layer→Prop)
    (num : r.FinalNumbered h C O path)
    (stored : TraceRecovery.stagePost K steps c O.layer (·<dp) (fun a=>(m a).val) H Q initial
      (r.archiveList h C O path data) (r.finalArchive h C O path).1)
    (physical : ∀ pre op post,steps=pre++op::post →
      (m (dir+(64*pre.length+44))).val=(allocate K (finish K pre c) op).words 44)
    (p : Parameters ℕ) (pin : Fin p.lanes → A.Site) (seed : ∀ j,(O.ord (pin j)).val=j.val)
    (rootCount : Fintype.card (r.plan.finish h).Site=p.roots) (pc ph rc rh dst : ℕ)
    (parentSpace : Parents.Layout W pc ph dp p.lanes steps.length (dir+44))
    (listSpace : TraceIntervalScanner.Layout W (dp+steps.length*p.lanes) p.heads p.links p.lanes p.roots)
    (resourceSpace : Room W rc rh p) (resourceHeader : Header rc rh p m)
    (control : rc<dp) (headers : rh+16≤dp) (target : dst≤p.resources)
    (ctl : (m pc).val=ph) (start : (m ph).val=dp) (size : (m (ph+1)).val=(steps.length+1)*p.lanes)
    (page : (m (ph+2)).val=dir+44) (n : (m (ph+3)).val=p.lanes) :
    let dest := fun j=>Fin.cast rootCount (r.terminalOrderEquiv h (r.plan.destination h (pin j)))
    let bases:=ownerBases r h C O path
    let first:=fillSegment dp ((bases.length+1)*p.lanes)
      (Parents.file dp p.lanes (Parents.walkPrefix (fun a=>(m a).val) bases)) m
    (registration W pc rc dp steps.length dst p).Spec (·=m)
      (fun _ out=>∃ linked,TraceIntervalScanner.Loaded (dp+steps.length*p.lanes) dest first ∧
        TraceIntervalScanner.Output p.heads p.links dest first linked ∧ out=publicRows dst p linked)
      ((11+(steps.length+1)*p.lanes*(2*(Parents.row pc).work+4)+(9+4*p.roots+10*p.lanes))+
        (ticks rc p+ (6+5*resourceLength p))) := by
  intro dest bases first
  obtain ⟨length,arrays,extent,final⟩:=TraceRecovery.scanner_inputs r h C O path data
    K dp dir H Q steps c (fun a=>(m a).val) initial num stored physical
  change bases.length=steps.length at length
  rw [←length] at parentSpace listSpace size ⊢
  have load : TraceIntervalScanner.Loaded (dp+bases.length*p.lanes) dest first := by
    intro j
    rw [show first (dp+bases.length*p.lanes+j.val) =
        (Parents.walkPrefix (fun a => (m a).val) bases bases.length j.val : Word W) from
      Parents.final_row dp p.lanes bases.length _ m j]
    apply congrArg (fun a : ℕ=>(a:Word W))
    simpa only [Parents.walkPrefix,List.take_length,dest,Fin.val_cast,seed j] using final (pin j)
  intro _ _ _ machine
  exact PhysicalProcedure.Procedure.Spec.mono (A:=registration W pc rc dp bases.length dst p)
    (registration_spec p bases dest m parentSpace listSpace resourceSpace resourceHeader
      control headers target ctl start size page n arrays (by
        intro t j hj
        let ix : Fin p.lanes:=⟨j,hj⟩
        simpa only [Parents.walkPrefix,seed ix] using extent t (pin ix)) load)
    (fun _ h=>h) (by
      rintro _ out ⟨linked,stored,done⟩
      exact ⟨linked,load,stored,done⟩) le_rfl machine

/-- The three kinds of public resource slot refer to the same true terminal
chart, including the selected archive's physical work charge. -/
theorem registered_resource_rows (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O) (num : r.FinalNumbered h C O path)
    (p : Parameters ℕ) (bank : RAM.NavigationNodeRows.Banks)
    (charges : p.charges=bank.charges) (first : p.firstFinal=(r.finalArchive h C O path).1.first)
    (count : Fintype.card (r.plan.finish h).Site=p.roots) (pin : Fin p.lanes→A.Site)
    (salaries pairs : A.Site→ℕ) (before m linked out : Memory W) (ctrl header dp dst : ℕ)
    (resourceRoom : Room W ctrl header p)
    (stored : r.ArchiveRowsStored bank (fun a=>(before a).val) h C O path)
    (seed : O.Charged bank (fun a=>(before a).val) salaries pairs)
    (chargeRoom : p.charges+2*(p.firstFinal+p.roots)≤dp)
    (head : dp≤p.heads) (next : dp≤p.links)
    (kept : ∀ a, p.charges≤a → a<dp → m a=before a)
    (lists : TraceIntervalScanner.Output p.heads p.links
      (fun j=>Fin.cast count (r.terminalOrderEquiv h (r.plan.destination h (pin j)))) m linked)
    (last : out=publicRows dst p linked) (v : (r.plan.finish h).Site) :
    let idx:=Fin.cast count (r.terminalOrderEquiv h v)
    let dest:=fun j=>Fin.cast count (r.terminalOrderEquiv h (r.plan.destination h (pin j)))
    (out (dst+idx.val*(p.directions+2))).val=bank.unitWork*r.chargeAt h C salaries v ∧
    out (dst+idx.val*(p.directions+2)+1)=(inputCount dest idx p.cap p.pairSpan : Word W) ∧
      ∀ i : Fin p.directions,out (dst+idx.val*(p.directions+2)+(2+i.val))=
        (directionCount dest idx p.band p.pairSpan i.val : Word W) := by
  intro idx dest
  subst out
  have bound : p.charges+2*(p.firstFinal+idx.val)<dp := by have:=idx.isLt;omega
  have keep:= (lists.1 _ (.inl (bound.trans_le head)) (.inl (bound.trans_le next))).trans (kept _ (by omega) bound)
  have raw:=Parents.charged_source r h C O path bank before stored salaries pairs seed v
  have ord : idx.val=((r.finalArchive h C O path).2 ((r.finalSite h).symm v)).val := by
    change (r.terminalOrderEquiv h v).val=_
    rw [r.terminalOrderEquiv_val]
    exact (num _).symm
  refine ⟨?_,?_,?_⟩
  · have pub:=public_row (W:=W) dst p linked idx (⟨0,by omega⟩ : Fin (p.directions+2))
    have real:=completed_cell p resourceRoom linked m dest lists idx (⟨0,by omega⟩ : Fin (p.directions+2))
    simp only [Nat.add_zero] at pub real
    rw [pub,real,keep,charges,first,ord]
    exact raw
  · have pub:=public_row (W:=W) dst p linked idx (⟨1,by omega⟩ : Fin (p.directions+2))
    exact pub.trans (published_input p resourceRoom linked m dest lists idx)
  · intro i
    have pub:=public_row (W:=W) dst p linked idx (⟨2+i.val,by have:=i.isLt;omega⟩ : Fin (p.directions+2))
    exact pub.trans (published_direction p resourceRoom linked m dest lists idx i)

end Hierarchy.TraceAdmission.Resources

end OAI

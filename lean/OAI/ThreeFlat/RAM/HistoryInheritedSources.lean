import OAI.ThreeFlat.RAM.HistorySelectedFrame

namespace OAI
/-! # The old cached endpoint copied at each actual inherited stage position -/

namespace ThreeFlat.RAM.HistoryStageSetup

open Computability.VPVNP.BurstRAM PrivateRAM HistoryPartyBatchExec HistoryStageRoot HistoryStageBody
open HistoryStageBody.Physical NavigationNodeRows
open Diagonal.PhysicalStage Diagonal.HistoryContraction Diagonal.TickWorkspace
open scoped BigOperators Fin.CommRing Classical
noncomputable section

variable {W : ℕ} {F Pins E : Type} [Field F] {d l D lanes : ℕ} {A : State d l}
    {R : Move F A D lanes} {branch : Fin R.rules.count}
    (L : A.Words Pins) (step : R.WordStep Pins L branch)
    {old : A.ArchiveSites} {ch : (R.next branch).Site→ℕ} (row : R.ArchiveStep branch old ch)

/-- Decode the S44 child-list head and every valid child cache index. -/
theorem recorded_child_addresses (T : Input) (mem : Memory W) (b : Banks) {s : Layer} (data : LayerData s)
    (j : Fin s.count) (directory : DirectoryRow b s j mem) (source : data.Reads (numeric mem))
    (idx : T.id=s.first+j.val) (baseNodes : T.nodeBase=b.nodes)
    (countRoom : s.childCount<2^W) (listRoom : s.children+j.val*s.childCount<2^W) :
    childCount T (numeric mem)=s.childCount ∧ ∀ k : Fin s.childCount,
      childPtr T (numeric mem) k.val=T.resultBase+8*data.child j k := by
  have atNode : HistoryStageRoot.node T=b.nodes+8*(s.first+j.val):=by rw [HistoryStageRoot.node,idx,baseNodes]
  constructor
  · unfold childCount;rw [atNode];exact (congrArg Fin.val directory.childCount).trans (Fin.val_cast_of_lt countRoom)
  · intro k
    have head:=(congrArg Fin.val directory.childPtr).trans (Fin.val_cast_of_lt listRoom)
    unfold childPtr
    rw [atNode,show numeric mem (b.nodes+8*(s.first+j.val)+3)=_ from head]
    rw [show numeric mem (s.children+j.val*s.childCount+k.val)=_ from source.child j k]

set_option maxRecDepth 16000 in
theorem stage_endpoint_sources (order : step.ChildOrder row) (v : (R.next branch).Site)
    (u seedCount : ℕ) (archive : Archive) (family : Family) (mem : Memory W) (b : Banks)
    (directory : DirectoryRow b row.sites.layer (row.sites.ord v) mem)
    (source : row.data.Reads (numeric mem))
    (idx : (numInput (Physical.layout u archive family) family.childBound (numeric mem)).id=row.sites.id v)
    (baseNodes : b.nodes=base u 44)
    (countRoom : row.sites.layer.childCount<2^W)
    (listRoom : row.sites.layer.children+(row.sites.ord v).val*row.sites.layer.childCount<2^W)
    (arena : base u 12+(row.sites.id v+1)*(volume u)^2≤base u 13) (large : 162≤volume u)
    (N : Forest F L.ports.form) (origin : ∀ w,Fin (L.ext w)→E) (pointer : E→ℕ)
    (encode : ((Fin 3→Bool)→F)→ℕ)
    (childSize : ∀ k : Fin row.sites.layer.childCount,L.ext (row.row.children v k).val≤volume u)
    (child : ∀ k : Fin row.sites.layer.childCount,let n:=row.data.child (row.sites.ord v) k
      (NodeValue.ofSite (Run.nodeOfSite L N origin (row.row.children v k).val) pointer
        (streamAt u seedCount n) (endsAt u seedCount n)).Cached encode u n mem) :
    let layout:=Physical.layout u archive family
    let T:=numInput layout family.childBound (numeric mem)
    let val:=NodeValue.ofSite (Run.nodeOfSite step.words (step.nextForest N) (Run.pushedOrigin step origin) v)
      pointer T.stream T.ext
    ∀ j : Fin val.external,∃ k : Fin (childCount T (numeric mem)),∃ z : Fin (Endpoints.width T (numeric mem) k.val),
      val.ext+j.val=Endpoints.toAddr T (numeric mem) k.val+z.val ∧
      mem (Endpoints.srcAddr T (numeric mem) k.val+z.val)=(val.endpoint j:Word W) ∧
      External layout family.childBound (Endpoints.srcAddr T (numeric mem) k.val+z.val) := by
  let layout:=Physical.layout u archive family
  let T:=numInput layout family.childBound (numeric mem)
  let raw:=numeric mem
  let idc := row.data.child (row.sites.ord v)
  obtain ⟨degree,ids⟩:=recorded_child_addresses T mem b row.data (row.sites.ord v) directory source idx
    (show T.nodeBase=b.nodes from baseNodes.symm) countRoom listRoom
  have width (k : Fin row.sites.layer.childCount) :
      Endpoints.width T raw k.val=L.ext (row.row.children v k).val := by
    unfold Endpoints.width Endpoints.info;rw [ids k]
    exact congrArg Result.extCount (child k).header
  have address (k : Fin row.sites.layer.childCount) : Endpoints.srcAddr T raw k.val=endsAt u seedCount (idc k) := by
    unfold Endpoints.srcAddr Endpoints.info;rw [ids k];exact congrArg Result.ext (child k).header
  intro _ _ _ j
  let k:=step.originIndex row v j
  let entry:=step.origin v j
  have site : (row.row.children v k).val=entry.1.val := by
    apply old.ord.injective
    apply Fin.ext
    have e:=(row.row.childId v k).symm.trans (step.origin_childId row order v j)
    change old.layer.first+_ = old.layer.first+_ at e
    exact Nat.add_left_cancel e
  let z : Fin (L.ext (row.row.children v k).val) := entry.2.cast (congrArg L.ext site.symm)
  refine ⟨k.cast degree.symm,z.cast (width k).symm,?_,?_,?_⟩
  · change T.ext+j.val=(T.ext+HistoryStageRoot.prefix T raw k.val Result.extCount)+z.val
    have prev : HistoryStageRoot.prefix T raw k.val Result.extCount=
        ∑ t : Fin k.val,Move.WordStep.childWidth (L:=L) row v t.val := by
      unfold HistoryStageRoot.prefix
      rw [←Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro t _
      have live := t.isLt.trans k.isLt
      simpa only [Endpoints.width,Endpoints.info,Move.WordStep.childWidth,dite_eq_left live] using width (⟨t.val,live⟩:Fin row.sites.layer.childCount)
    rw [prev];have num:=step.origin_offset row order v j
    change j.val=(∑ t : Fin k.val,Move.WordStep.childWidth (L:=L) row v t.val)+z.val at num
    omega
  · change mem (Endpoints.srcAddr T raw k.val+z.val)=(pointer (origin entry.1.val entry.2):Word W)
    rw [address]
    have word := (child k).ends z
    change mem (endsAt u seedCount (idc k)+z.val)=(pointer (origin (row.row.children v k).val z):Word W) at word
    rw [word]
    have same {x y : A.Site} (e : x=y) (i : Fin (L.ext y)) :
        origin x (i.cast (congrArg L.ext e.symm))=origin y i := by cases e;rfl
    rw [show origin (row.row.children v k).val z=origin entry.1.val entry.2 from same site entry.2]
  · change External layout family.childBound (Endpoints.srcAddr T raw k.val+z.val)
    rw [address]
    have prior : idc k<row.sites.id v := by
      have iLt:=(old.ord (row.row.children v k).val).isLt
      have nextRow:=row.row.contiguous
      have pos:=row.row.childId v k
      change idc k=old.layer.first+_ at pos
      change idc k<row.sites.layer.first+_;omega
    have size:=Physical.address_limits (seedCount:=seedCount) (i:=idc k) (rows:=0) large (by simp) (childSize k)
    have rowEnd := Nat.mul_le_mul_right ((volume u)^2) (Nat.add_le_add_right prior.le 1)
    have low : endsAt u seedCount (idc k)+z.val<base u 13 :=
      (Nat.add_lt_add_left z.isLt _).trans_le
        (size.2.2.trans ((Nat.add_le_add_left rowEnd _).trans arena))
    left
    change endsAt u seedCount (idc k)+z.val<15*Diagonal.TickWorkspace.stride u+volume u+64+0
    change endsAt u seedCount (idc k)+z.val<14*Diagonal.TickWorkspace.stride u at low
    omega


end
end ThreeFlat.RAM.HistoryStageSetup

end OAI

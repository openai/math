import OAI.Hierarchy.ProbeChainPlacement
import OAI.Hierarchy.ProbePayloadStrip
import OAI.Hierarchy.ProbeSiteOrder

namespace OAI
/-! # Physical placement of every payload strip on its advised permutation route -/
namespace Hierarchy.ProbeStage
open AdaptiveProbe PayloadStrip
open scoped Classical
noncomputable section
set_option quotPrecheck false

abbrev PayloadColumns (h d : ℕ) := Fin (2^h) ⊕ (StageColumns h d ⊕ Fin (2^h))

private abbrev Key (R : Type*) (N : ℕ) := R ⊕ ((Fin N × (R × Bool)) ⊕ R)

private def columnKey {R : Type*} {N : ℕ} (p : R) (i : Columns N) : Key R N :=
  if i.val.val=0 then .inl p
  else if atStage : (i.val.val-1)/2<N then
    .inr (.inl (⟨(i.val.val-1)/2,atStage⟩,p,if i.val.val%2=1 then false else true))
  else .inr (.inr p)

private def keyOrdinal {R : Type*} (N : ℕ) : Key R N → R × ℕ
  | .inl p => (p,0)
  | .inr (.inl (t,p,false)) => (p,2*t.val+1)
  | .inr (.inl (t,p,true)) => (p,2*t.val+2)
  | .inr (.inr p) => (p,2*N+1)

private theorem ordinal_columnKey {R : Type*} {N : ℕ} (p : R) (i : Columns N) :
    keyOrdinal N (columnKey p i)=(p,i.val.val) := by
  have bound := i.val.isLt
  change i.val.val<2*N+1+1 at bound
  by_cases h : i.val.val=0
  · simp [columnKey,keyOrdinal,h]
  by_cases room : (i.val.val-1)/2<N
  · by_cases odd : i.val.val%2=1 <;> simp [columnKey,keyOrdinal,h,room,odd] <;> omega
  · simp [columnKey,keyOrdinal,h,room]; omega

private def keyEmbedding {R : Type*} (N : ℕ) : (R × Columns N) ↪ Key R N where
  toFun x := columnKey x.1 x.2
  inj' := by
    rintro ⟨p,i⟩ ⟨q,j⟩ eq
    have both := congrArg (keyOrdinal N) eq
    change keyOrdinal N (columnKey p i)=keyOrdinal N (columnKey q j) at both
    rw [ordinal_columnKey,ordinal_columnKey] at both
    exact Prod.ext (congrArg (fun z : R × ℕ=>z.1) both) (Subtype.ext (Fin.ext (congrArg (fun z : R × ℕ=>z.2) both)))

variable {h d : ℕ} (π : Equiv.Perm (Fin (2^h)))
local notation "N" => (permutationFabric h d).shapes.length
local notation "R" => Fin (2^h)

private def stagePort (t : StageAt h d) :
    (R × Bool) ↪ ((stageAt h d t).Group × (Fin (stageAt h d t).span ⊕ Fin (stageAt h d t).span)) := by
  let a:=advisedStage h d π t
  let port : R × Bool → Fin (stageAt h d t).span ⊕ Fin (stageAt h d t).span
    | (p,false) => .inl (a.input p)
    | (p,true) => .inr (a.output p)
  refine ⟨fun z => (a.group z.1,port z),?_⟩
  rintro ⟨p,x⟩ ⟨q,y⟩ same
  have grp := congrArg Prod.fst same
  have vals := congrArg Prod.snd same
  cases x <;> cases y
  · exact Prod.ext (a.input_inj (Prod.ext grp (Sum.inl.inj vals))) rfl
  · exact (Sum.inl_ne_inr vals).elim
  · exact (Sum.inr_ne_inl vals).elim
  · exact Prod.ext (a.output_inj (Prod.ext grp (Sum.inr.inj vals))) rfl

/-- The selected input and output addresses of all payload rows of one stage. -/
def occupiedStagePort (t : StageAt h d) :
    (R × Bool) ↪ ((stageAt h d t).Group × (Fin (stageAt h d t).span ⊕ Fin (stageAt h d t).span)) :=
  stagePort π t

@[simp] theorem occupiedStagePort_in (t : StageAt h d) (p : R) :
    occupiedStagePort π t (p,false)=((advisedStage h d π t).group p,.inl ((advisedStage h d π t).input p)) := rfl

@[simp] theorem occupiedStagePort_out (t : StageAt h d) (p : R) :
    occupiedStagePort π t (p,true)=((advisedStage h d π t).group p,.inr ((advisedStage h d π t).output p)) := rfl

private def stageSocket : (StageAt h d × (R × Bool)) ↪ StageColumns h d where
  toFun z := ⟨z.1,stagePort π z.1 z.2⟩
  inj' := by
    rintro ⟨t,x⟩ ⟨u,y⟩ eq
    obtain ⟨rfl,rest⟩ := Sigma.mk.inj_iff.mp eq
    exact Prod.ext rfl ((stagePort π _).injective (eq_of_heq rest))

/-- One injection for all rows, including both exterior banks. At each internal
stage the actual input and output maps of its advised permutation separate the rows. -/
def payloadPlaceAll : (R × Columns N) ↪ PayloadColumns h d :=
  (keyEmbedding N).trans ((Function.Embedding.refl R).sumMap
    ((stageSocket (d:=d) π).sumMap π.toEmbedding))

def payloadPlace (p : R) : Columns N ↪ PayloadColumns h d where
  toFun i := payloadPlaceAll π (p,i)
  inj' _ _ eq := congrArg Prod.snd ((payloadPlaceAll π).injective eq)

/-- The external strip endpoints are the input and the permuted output. -/
theorem payloadPlace_input (p : R) : payloadPlace (d:=d) π p (first N 0)=.inl p := rfl

theorem payloadPlace_output (p : R) : payloadPlace (d:=d) π p (last N (Fin.last N))=.inr (.inr (π p)) := by
  have key : columnKey p (last N (Fin.last N))=.inr (.inr p) := by
    change (if 2*N+1=0 then _ else if q : (2*N+1-1)/2<N then _ else _)=_
    simp []
  change ((Function.Embedding.refl R).sumMap ((stageSocket (d:=d) π).sumMap π.toEmbedding))
      (columnKey p (last N (Fin.last N)))=_
  rw [key];rfl

/-- Columns 2*t+1 and 2*t+2 are the input and output sockets of tile t. -/
theorem payloadPlace_stage_in (p : R) (t : StageAt h d) :
    payloadPlace π p (last N t.castSucc)=
      .inr (.inl ⟨t,(advisedStage h d π t).group p,.inl ((advisedStage h d π t).input p)⟩) := by
  have key : columnKey p (last N t.castSucc)=.inr (.inl (t,p,false)) := by
    have address : (last N t.castSucc).val.val=2*t.val+1 := rfl
    simp only [columnKey,address]
    have calc' : (2*t.val+1-1)/2=t.val := by omega
    simp [t.isLt,show (2*t.val+1)%2=1 by omega]
  change ((Function.Embedding.refl R).sumMap ((stageSocket (d:=d) π).sumMap π.toEmbedding))
      (columnKey p (last N t.castSucc))=_
  rw [key];rfl

theorem payloadPlace_stage_out (p : R) (t : StageAt h d) :
    payloadPlace π p (first N t.succ)=
      .inr (.inl ⟨t,(advisedStage h d π t).group p,.inr ((advisedStage h d π t).output p)⟩) := by
  have key : columnKey p (first N t.succ)=.inr (.inl (t,p,true)) := by
    have address : (first N t.succ).val.val=2*(t.val+1) := rfl
    simp only [columnKey,address]
    have calc' : (2*(t.val+1)-1)/2=t.val := by omega
    simp [show 2*(t.val+1)≠0 by omega,calc',t.isLt]
  change ((Function.Embedding.refl R).sumMap ((stageSocket (d:=d) π).sumMap π.toEmbedding))
      (columnKey p (first N t.succ))=_
  rw [key];rfl

/-- Count all physical stage sockets including padding, together with both exterior banks. -/
theorem payloadColumns_card_le (h d : ℕ) (hd : 1 ≤ d) :
    Fintype.card (PayloadColumns h d) ≤
      2*2^h+2*(permutationFabric h d).shapes.length*(4^(rounds d+1)*2^h) := by
  let cap:=4^(rounds d+1)*2^h
  have each (t : StageAt h d) :
      Fintype.card ((stageAt h d t).Group × (Fin (stageAt h d t).span ⊕ Fin (stageAt h d t).span)) ≤ 2*cap := by
    have shape := (template_dyadic (h:=h) hd (stageAt h d t) (List.get_mem ..)).2
    simpa only [Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,two_mul,Nat.mul_add,cap]
      using Nat.mul_le_mul_left 2 shape
  have inside : Fintype.card (StageColumns h d) ≤ (permutationFabric h d).shapes.length*(2*cap) := by
    unfold StageColumns
    rw [Fintype.card_sigma]
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (s:=Finset.univ) (fun t _=>each t)
  have normalized : (permutationFabric h d).shapes.length*(2*cap)=2*(permutationFabric h d).shapes.length*cap := by ring
  rw [normalized] at inside
  change Fintype.card (Fin (2^h) ⊕ (StageColumns h d ⊕ Fin (2^h))) ≤ 2*2^h+2*(permutationFabric h d).shapes.length*cap
  simp only [Fintype.card_sum,Fintype.card_fin]
  omega

theorem payloadSites_card_le (h d k : ℕ) (hd : 1 ≤ d) :
    Fintype.card (ColumnSite (PayloadColumns h d) k) ≤
      (2*2^h+2*(permutationFabric h d).shapes.length*(4^(rounds d+1)*2^h))*(2*k+1) := by
  have layers : Fintype.card (ColumnLayer k)=2*k+1 := by
    simp [ColumnLayer,Nat.mul_comm]
  unfold ColumnSite
  rw [Fintype.card_prod,layers]
  exact Nat.mul_le_mul_right _ (payloadColumns_card_le h d hd)

/-- Exterior and stage sockets on the two sides of the zero-price joins. -/
def payloadFreeFrom (p : R) : Fin (N+1) → PayloadColumns h d :=
  Fin.cases (.inl p) (fun t => .inr (.inl ⟨t,(advisedStage h d π t).group p,
    .inr ((advisedStage h d π t).output p)⟩))

def payloadFreeTo (p : R) : Fin (N+1) → PayloadColumns h d :=
  Fin.lastCases (.inr (.inr (π p))) (fun t => .inr (.inl ⟨t,(advisedStage h d π t).group p,
    .inl ((advisedStage h d π t).input p)⟩))

theorem payloadPlace_free (p : R) (j : Fin (N+1)) :
    let e : Fin (edgeCount N):=⟨2*j.val,by have:=j.isLt;dsimp [edgeCount];omega⟩
    let ends:=Strip.horizontal (edgeCount N) e
    payloadPlace π p ends.left=payloadFreeFrom π p j ∧
      payloadPlace π p ends.right=payloadFreeTo π p j ∧ length N e=0 := by
  intro e ends
  have left : ends.left=first N j := Subtype.ext (Fin.ext rfl)
  have right : ends.right=last N j := Subtype.ext (Fin.ext rfl)
  rw [left,right]
  refine ⟨?_,?_,?_⟩
  · refine Fin.cases ?_ (fun t=>?_) j
    · simpa only [payloadFreeFrom,Fin.cases_zero] using payloadPlace_input (d:=d) π p
    · simpa only [payloadFreeFrom,Fin.cases_succ] using payloadPlace_stage_out π p t
  · refine Fin.lastCases ?_ (fun t=>?_) j
    · simpa only [payloadFreeTo,Fin.lastCases_last] using payloadPlace_output (d:=d) π p
    · simpa only [payloadFreeTo,Fin.lastCases_castSucc] using payloadPlace_stage_in π p t
  · exact ite_eq_left (by change (2*j.val)%2=0;omega)

theorem payloadPlace_tile (p : R) (t : StageAt h d) :
    let e : Fin (edgeCount N):=⟨2*t.val+1,by have:=t.isLt;dsimp [edgeCount];omega⟩
    let ends:=Strip.horizontal (edgeCount N) e
    let a:=advisedStage h d π t
    payloadPlace π p ends.left=.inr (.inl ⟨t,a.group p,.inl (a.input p)⟩) ∧
      payloadPlace π p ends.right=.inr (.inl ⟨t,a.group p,.inr (a.output p)⟩) ∧ length N e=1 := by
  intro e ends a
  have left : ends.left=last N t.castSucc := Subtype.ext (Fin.ext rfl)
  have right : ends.right=first N t.succ := by
    apply Subtype.ext;apply Fin.ext;change 2*t.val+1+1=2*(t.val+1);omega
  rw [left,right]
  exact ⟨payloadPlace_stage_in π p t,payloadPlace_stage_out π p t,
    ite_eq_right (by change ¬(2*t.val+1)%2=0;omega)⟩

/-- Interior H-strips and exterior payload strips inhabit this same column board. -/
def stageColumnsIntoPayload : StageColumns h d ↪ PayloadColumns h d :=
  Function.Embedding.inl.trans Function.Embedding.inr

def stageSitesIntoPayload (k : ℕ) : ColumnSite (StageColumns h d) k ↪ ColumnSite (PayloadColumns h d) k :=
  (stageColumnsIntoPayload (h:=h) (d:=d)).prodMap (Function.Embedding.refl _)

/-- Combined physical positions include the unchanged radial layer of every site. -/
def payloadSitesAll (k : ℕ) : (R × ColumnSite (Columns N) k) ↪ ColumnSite (PayloadColumns h d) k where
  toFun z := (payloadPlaceAll π (z.1,z.2.1),z.2.2)
  inj' := by
    rintro ⟨p,i,l⟩ ⟨q,j,m⟩ eq
    have both := (payloadPlaceAll (d:=d) π).injective (congrArg Prod.fst eq)
    exact Prod.ext (congrArg (fun z : R × Columns N=>z.1) both) (Prod.ext (congrArg (fun z : R × Columns N=>z.2) both) (congrArg (fun z : ColumnSite (PayloadColumns h d) k=>z.2) eq))

def payloadSites {k : ℕ} (p : R) : ColumnSite (Columns N) k ↪ ColumnSite (PayloadColumns h d) k :=
  (payloadPlace π p).prodMap (Function.Embedding.refl _)

theorem payloadSitesAll_row {k : ℕ} (p : R) (i : ColumnSite (Columns N) k) :
    payloadSitesAll π k (p,i)=payloadSites (d:=d) π p i := rfl

/-- The physical order is the order induced in the full net by this particular
row. The resulting names and order embeddings may depend on the payload. -/
def namedPayload {k J : ℕ} (global : ColumnSite (PayloadColumns h d) k ↪ Fin J) (p : R) :=
  SiteOrder.ofEmbedding ((payloadSites π p).trans global)

theorem sorted_payload_site {k J : ℕ} (global : ColumnSite (PayloadColumns h d) k ↪ Fin J)
    (p : R) (i : ColumnSite (Columns N) k) :
    let physical:=namedPayload π global p
    physical.ord (physical.name i)=global (payloadSites π p i) :=
  (namedPayload π global p).reconstruct i


end
end Hierarchy.ProbeStage

end OAI

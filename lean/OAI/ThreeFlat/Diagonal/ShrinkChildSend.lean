import OAI.ThreeFlat.Diagonal.ShrinkOldBitHalf
import OAI.ThreeFlat.Diagonal.ShrinkHistoryWires

namespace OAI
/-! # The occupied party's old pin in child and physical half coordinates -/
namespace ThreeFlat.Diagonal.CompressorPacking.ChildSend
open Computability.VPVNP.Compression HistoryContraction MotifBinaryPacking LinearAlgebra.SpectralBooks
open scoped Classical Fin.CommRing
noncomputable section
variable {B H T L : Type} [AddCommGroup H] [AddCommGroup T] [AddCommGroup L]
  [Fintype B] [Fintype H] [Fintype T] [Fintype L] {d c Q : ℕ}
variable (P : PackingData B H T L d (c+1)) (code : Arc B H T L d (c+1) ↪ ℕ)
variable (width : Arc B H T L d (c+1)→ℕ) (hQ : 0<Q)
variable (num : P.Motif ≃ (Site B T L × Fin d) × Fin Q)
abbrev Request := Σ a : Arc B H T L d (c+1),Bool × Fin (width a)

def request (m : P.Motif) (side : Bool) (e : Fin 2) (j : Fin (demandWidth P width num m e)) : Request width :=
  demandBit P code width hQ num (fun a b t=>⟨a,b,t⟩) m side e j

theorem request_map {X : Type*} (f : (a : Arc B H T L d (c+1))→Bool→Fin (width a)→X)
    (m : P.Motif) (side : Bool) (e : Fin 2) (j : Fin (demandWidth P width num m e)) :
    let x:=request P code width hQ num m side e j
    demandBit P code width hQ num f m side e j=f x.1 x.2.1 x.2.2 := by fin_cases e <;> rfl

theorem request_owner (bundled : ∀m,(num m).1=P.bundle m) (lay : Bool)
    (m : P.Motif) (side : Bool) (e : Fin 2) (j : Fin (demandWidth P width num m e)) :
    let x:=request P code width hQ num m side e j
    P.placement lay ((oldGraph P).vertex x.1 x.2.1)=partySite P lay m (demandGraph.vertex e side) := by
  dsimp only
  rw [party_demandSite]
  fin_cases e
  · let a:=(oldBit P code width (num m).1).symm (SlotEnergy.pieceIndex _ _ hQ ⟨(num m).2,j⟩)
    cases side
    · exact (thick_placement P lay _ a.1).1.trans (congrArg Prod.fst (bundled m))
    · exact (thick_placement P lay _ a.1).2.trans (congrArg (fun p=>(P.siteGraph.target p).1) (bundled m))
  · change P.placement lay ((oldGraph P).vertex m.val
        (if P.thick (sourcePosition m.val) then !side else side)) =
      (if side then P.roleD lay m else P.placement lay (P.C m))
    cases side <;> by_cases ht : P.thick (sourcePosition m.val) <;>
      simp [oldGraph,PortGraph.vertex,PackingData.C,PackingData.roleD,PackingData.D,ht]

private def incidentEquiv (u : Position B H T L (c+1)) : Fin d ⊕ Fin d ≃ (oldGraph P).Port u where
  toFun
    | .inl i=>⟨(((u.1,i),u.2),false),rfl⟩
    | .inr i=>⟨(P.actual.symm ((u.1,i),u.2),true),by
        change sourcePosition (P.actual (P.actual.symm _))=u;rw [Equiv.apply_symm_apply];rfl⟩
  invFun q:=if q.val.2 then .inr (P.actual q.val.1).1.2 else .inl q.val.1.1.2
  left_inv:=by
    rintro (i|i)
    · rfl
    · change Sum.inr ((P.actual (P.actual.symm _)).1.2)=Sum.inr i
      rw [Equiv.apply_symm_apply]
  right_inv:=by
    rintro ⟨⟨a,b⟩,ha⟩
    cases b with
    | false =>
      change sourcePosition a=u at ha
      subst u;rfl
    | true =>
      change sourcePosition (P.actual a)=u at ha
      subst u
      apply Subtype.ext
      change (P.actual.symm (P.actual a),true)=(a,true)
      rw [Equiv.symm_apply_apply]

def portOrder (u : Position B H T L (c+1)) : Fin (2*d) ≃ (oldGraph P).Port u :=
  ((finCongr (two_mul d)).trans finSumFinEquiv.symm).trans (incidentEquiv P u)

omit [Fintype B] [Fintype H] [Fintype T] [Fintype L] in
theorem portNumber (a : Arc B H T L d (c+1)) (b : Bool) :
    ((portOrder P ((oldGraph P).vertex a b)).symm ⟨(a,b),rfl⟩).val=
      if b then d+(P.actual a).1.2.val else a.1.2.val := by cases b <;> rfl

variable {P width}
def ownedChild (lay : Bool) (v : Site B T L) (x : Request width)
    (atSite : P.placement lay ((oldGraph P).vertex x.1 x.2.1)=v) :
    {u // P.placement lay u=v} := ⟨_,atSite⟩

def ownedPort (lay : Bool) (v : Site B T L) (x : Request width)
    (atSite : P.placement lay ((oldGraph P).vertex x.1 x.2.1)=v) :
    (oldGraph P).Port (ownedChild lay v x atSite).val := ⟨(x.1,x.2.1),rfl⟩

theorem at_party (bundled : ∀m,(num m).1=P.bundle m) (lay : Bool) {v : Site B T L}
    (m : P.Motif) {party : Fin 6} (placed : partySite P lay m party=v)
    (q : demandGraph.Port party) (j : Fin (demandWidth P width num m q.val.1)) :
    let x:=request P code width hQ num m q.val.2 q.val.1 j
    P.placement lay ((oldGraph P).vertex x.1 x.2.1)=v :=
  (request_owner P code width hQ num bundled lay m q.val.2 q.val.1 j).trans
    ((congrArg (partySite P lay m) q.property).trans placed)

/-- The precise member of the `old` callback supplied to `Tree.occupiedTree` by
`shrinkPiece`. Locality rules out the default branch of `ownerSource`. -/
theorem oldPinSource_request {h p : ℕ} (bundled : ∀m,(num m).1=P.bundle m) (lay : Bool) (v : Site B T L)
    (old : (i : {u // P.placement lay u=v})→(q : (oldGraph P).Port i.val)→Fin (width q.val.1)→Fin p)
    (m : P.Motif) {party : Fin 6} (placed : partySite P lay m party=v)
    (q : demandGraph.Port party) (j : Fin (demandWidth P width num m q.val.1)) :
    let x:=request P code width hQ num m q.val.2 q.val.1 j
    let yes:=at_party code hQ num bundled lay m placed q j
    oldPinSource P width code hQ num lay v old m party q j=
      (BitSource.pin (old (ownedChild lay v x yes) (ownedPort lay v x yes) x.2.2) : BitSource h p) := by
  dsimp only
  unfold oldPinSource
  rw [request_map P code width hQ num]
  simp only [ownerSource,dite_eq_left (at_party code hQ num bundled lay m placed q j),ownedChild,ownedPort]

variable (P width)
def words (lay : Bool) (v : Site B T L) (x : Request width)
    (atSite : P.placement lay ((oldGraph P).vertex x.1 x.2.1)=v) : Fin 4→ℕ :=
  ![1,((Owner.childOrder P lay v).symm (ownedChild lay v x atSite)).val,
    ((portOrder P _).symm (ownedPort lay v x atSite)).val,x.2.2.val]

section Native
open Computability.VPVNP.BurstRAM PrivateRAM RAM.PhysicalPinsExpr Native.Placement Native.ShrinkStage
variable {w n t l : ℕ} {S : Native.Graph.Stage}
variable {P₀ : PackingData B H (BitWord t) (BitWord l) S.degree (c+1)}
  {width₀ : Arc B H (BitWord t) (BitWord l) S.degree (c+1)→ℕ}
  {E : Codec B w (c+1) t l} {pub : Param→Word w} {mem : Memory w} {vs : Fin n→Word w} {ptr : Formula n}
local notation "V" => Formula.value pub mem vs

omit [Fintype B] [Fintype H] in
/-- The four native words identify exactly the old-pin arguments of the occupied
tree in the requesting party's own child and half enumerations. -/
theorem native_words
    (R : ArcReads P₀ E ((oldColumns (Native.Demand.formulaOps n) ptr).map (Formula.value pub mem vs)) mem) (M : BitOrigins.MateReads (S:=S) P₀ E pub mem vs ptr)
    (colors : S.colors=c+1) (cw : c+1<w) (lay : Bool) (v : Site B (BitWord t) (BitWord l))
    (q : Request width₀) (atSite : P₀.placement lay ((oldGraph P₀).vertex q.1 q.2.1)=v)
    (e : Ends (Formula n)) (incoming bit : Formula n)
    (ends : e.map V=encodeEnds P₀ E q.1) (side : V incoming=(q.2.1.toNat:Word w))
    (idx : V bit=(q.2.2.val:Word w)) (k : Fin 4) :
    V (BitOrigins.oldHalf ptr S lay e incoming bit k)=(words P₀ width₀ lay v q atSite k:Word w) := by
  subst v
  have ep : BitOrigins.oldEndpoint P₀ q.1 q.2.1=(oldGraph P₀).vertex q.1 q.2.1 := by
    cases h : q.2.1 <;> rfl
  rw [BitOrigins.oldHalf_native R M colors cw lay q.2.1 e incoming bit q.1 ends side k]
  rw [ep]
  fin_cases k
  · rfl
  · rfl
  · exact congrArg (fun z : ℕ=>(z:Word w)) (portNumber P₀ q.1 q.2.1).symm
  · exact (Fin.cast_val_eq_self (V bit)).trans idx


end Native

end
end ThreeFlat.Diagonal.CompressorPacking.ChildSend

end OAI

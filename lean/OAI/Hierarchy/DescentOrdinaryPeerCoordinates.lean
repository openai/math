import OAI.Hierarchy.DescentOrdinaryPeerProduct
import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentFullHostOrdinal

namespace OAI
/-! # Ordinary neighbors in the actual numbered host rectangle -/
namespace Hierarchy.DescentHostDirectory
open DescentContacts DescentColonies
open private DescentHostDirectory.fields from OAI.Hierarchy.DescentFullHostOrdinal
open scoped Classical
noncomputable section

def shapeOrder (k slots : ℕ) : ↥(codes k)×Fin slots ≃ Fin ((2^(k+1)-1)*slots):=
  ((heapIndex k).prodCongr (Equiv.refl _)).trans finProdFinEquiv

def unpackShape (k slots : ℕ) (s : Fin ((2^(k+1)-1)*slots)) : ShapeSlot :=
  let a:=(shapeOrder k slots).symm s
  (a.1.val,a.2.val)

def shapeSet (window k slots : ℕ) (q : Fin ((2^(k+1)-1)*slots)) : Finset (Fin ((2^(k+1)-1)*slots)):=
  Finset.univ.filter fun s=>unpackShape k slots s∈shapeReach window slots 10 (unpackShape k slots q) ∧
    unpackShape k slots q∈shapeReach window slots 10 (unpackShape k slots s)

variable {V : Type} [Fintype V] {k slots : ℕ}
def shape (x : Host V k slots) : Fin ((2^(k+1)-1)*slots) :=
  let h:=Finset.mem_product.mp (Finset.mem_product.mp x.2).2
  shapeOrder k slots (⟨x.val.2.1,h.1⟩,⟨x.val.2.2,Finset.mem_range.mp h.2⟩)

theorem unpack_shape (x : Host V k slots) : unpackShape k slots (shape x)=x.val.2:=by
  simp [unpackShape,shape]

theorem shape_val (x : Host V k slots) : (shape x).val=nodeNumber x.val.2.1.1 x.val.2.1.2*slots+x.val.2.2:=by
  change x.val.2.2+slots*nodeNumber x.val.2.1.1 x.val.2.1.2=_
  ring

theorem shape_mem (window : ℕ) (x y : Host V k slots) : shape y∈shapeSet window k slots (shape x) ↔
    y.val.2∈shapeReach window slots 10 x.val.2 ∧ x.val.2∈shapeReach window slots 10 y.val.2:=by
  simp [shapeSet,unpack_shape]

def shapeCoordinates : Host V k slots ≃ V×Fin ((2^(k+1)-1)*slots) :=
  Equiv.trans (DescentHostDirectory.fields (V:=V) (k:=k) (slots:=slots))
    ((Equiv.refl V).prodCongr (shapeOrder k slots))

theorem shapeCoordinates_at (x : Host V k slots) :
    shapeCoordinates x=(x.val.1,shape x):=rfl

omit [Fintype V] in
private theorem first_hop [DecidableEq V] (near : V→Finset V) {v u : V} (h : u∈insert v (near v)) (t : ℕ)
    {z : V} (hz : z∈DescentOrdinaryDonorHalo.around near t u) : z∈DescentOrdinaryDonorHalo.around near (t+1) v:=by
  induction t generalizing z with
  | zero=>
    have eqn:=Finset.mem_singleton.mp hz
    subst z
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_singleton_self _,h⟩
  | succ t ih=>
    obtain ⟨a,early,step⟩:=Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨a,ih early,step⟩

omit [Fintype V] in
theorem around_reverse [DecidableEq V] (near : V→Finset V) (sym : ∀u v,u∈near v↔v∈near u)
    (t : ℕ) {u v : V} (seen : v∈DescentOrdinaryDonorHalo.around near t u) :
    u∈DescentOrdinaryDonorHalo.around near t v:=by
  induction t generalizing u v with
  | zero=>exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp seen).symm
  | succ t ih=>
    obtain ⟨a,earlier,step⟩:=Finset.mem_biUnion.mp seen
    apply first_hop near (u:=a) _ t (ih earlier)
    rcases Finset.mem_insert.mp step with rfl|h
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem ((sym v a).mp h)

end
end Hierarchy.DescentHostDirectory

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentKernelHistory DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε u : ℝ} {S : AtomSchedule}
  {W : MarkedWorld F d P bits} {i z D wire hist z' D' : ℕ}
  {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
  {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
  {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
  (ticket : OrdinaryLink source he T p n target)
set_option quotPrecheck false
local notation "slots" =>2^packExponent 20 source.placement.degree+2
local notation "window" =>gap source.placement.degree+gainExponent 20 source.placement.degree

include ticket

theorem OrdinaryLink.peer_coordinates :
    ∃ chart : target.V≃Host source.V k slots,
    (∀v,(target.vertex v).val=(source.vertex (chart v).val.1).val*((2^(k+1)-1)*slots)+(shape (chart v)).val) ∧
    ∀v x,x∈target.placement.mutual v ↔
      ((chart x).val.1∈around source.placement.near 10 (chart v).val.1 ∧
        (chart v).val.1∈around source.placement.near 10 (chart x).val.1) ∧
        shape (chart x)∈shapeSet window k slots (shape (chart v)):=by
  obtain ⟨chart,issued,adj⟩:=ticket.adjacency
  refine ⟨chart,fun v=>?_,fun v x=>?_⟩
  · rw [issued,shape_val]
    ring
  · have keep : x ∈ target.placement.mutual v ↔ x ∈ target.placement.near v :=
      ⟨fun hit=>(Finset.mem_filter.mp hit).1,
        fun hit=>Finset.mem_filter.mpr ⟨hit,(target.placement.symmetric v x).mp hit⟩⟩
    rw [keep,adj v x,restricted_product source.placement.near window k slots (chart v) (chart x),
      shape_mem window (chart v) (chart x)]

/-- All old hosts and all valid heap/slot pairs occur, including hosts with zero current load. -/
theorem OrdinaryLink.peer_card :
    ∃ e : target.V≃source.V×Fin ((2^(k+1)-1)*slots),
      (∀v,(target.vertex v).val=(source.vertex (e v).1).val*((2^(k+1)-1)*slots)+(e v).2.val) ∧
      (∀v x,x∈target.placement.mutual v ↔ (e x).1∈around source.placement.near 10 (e v).1 ∧
        (e x).2∈shapeSet window k slots (e v).2) ∧
      (∀v,(target.placement.mutual v).card=(around source.placement.near 10 (e v).1).card*
        (shapeSet window k slots (e v).2).card) ∧
      (∀v,(around source.placement.near 10 (e v).1).card*(shapeSet window k slots (e v).2).card≤target.placement.degree) ∧
      ∀v q,∃!x,e x=(v,q):=by
  classical
  obtain ⟨chart,where_,peers⟩:=ticket.peer_coordinates
  let e:=chart.trans shapeCoordinates
  have ij (v : target.V) : e v=((chart v).val.1,shape (chart v)):=shapeCoordinates_at (chart v)
  have iff_ (v x : target.V) : x∈target.placement.mutual v ↔
      (e x).1∈around source.placement.near 10 (e v).1 ∧ (e x).2∈shapeSet window k slots (e v).2:=by
    simp only [ij,peers]
    exact ⟨fun h=>⟨h.1.1,h.2⟩,fun h=>⟨⟨h.1,around_reverse _ (fun a b=>(source.placement.symmetric b a)) _ h.1⟩,h.2⟩⟩
  have count (v : target.V) : (target.placement.mutual v).card=(around source.placement.near 10 (e v).1).card*
      (shapeSet window k slots (e v).2).card:=by
    have eqn : (target.placement.mutual v).map e.toEmbedding=
        around source.placement.near 10 (e v).1 ×ˢ shapeSet window k slots (e v).2:=by
      ext z
      obtain ⟨x,rfl⟩:=e.surjective z
      simp [iff_,Finset.mem_product]
    simpa using congrArg Finset.card eqn
  refine ⟨e,where_,iff_,count,fun v=>(count v).symm.le.trans ((Finset.card_filter_le ..).trans (target.placement.degreeBound v)),?_⟩
  intro v c
  exact ⟨e.symm (v,c),e.apply_symm_apply _,fun x hx=>e.injective (hx.trans (e.apply_symm_apply _).symm)⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI

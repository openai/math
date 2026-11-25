import OAI.ThreeFlat.Diagonal.PhysicalShrinkAssembly
import OAI.ThreeFlat.Diagonal.ShrinkChildSend
import OAI.ThreeFlat.Diagonal.HistoryScopeOffsets

namespace OAI
/-! # Predecessor half-bit prefixes across the physical shrink chart -/
namespace ThreeFlat.Diagonal.HistoryRelabel
open HistoryContraction Computability.VPVNP.Compression LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
noncomputable section

variable {V E U D Pins : Type} [Fintype V] [Fintype E] [Fintype U] [Fintype D]
variable {G : PortGraph V E} {H : PortGraph U D} {w : E→ℕ} {b : D→ℕ}
variable (I : Iso (WordLayout.shape G w) (WordLayout.shape H b)) (L : WordLayout G w Pins)

/-- Transport preserves every half-port prefix, including the starts of empty fields. -/
theorem Iso.pushWord_start (hw : ∀e,w e=b (I.edge e)) (v : V) (p : G.Port v) :
    (I.pushWord L).ports.start (I.site v) (I.port v p)=L.ports.start v p := by
  obtain ⟨j,rfl⟩:=(L.order v).surjective p
  let e:=congrArg L.count (I.site.symm_apply_apply v)
  have direct : (I.pushWord L).order (I.site v) (j.cast e.symm)=I.port v (L.order v j) :=
    Subtype.ext (push_order_val I L _ (I.site.symm_apply_apply v) j)
  have inv:=((I.pushWord L).order (I.site v)).symm_apply_eq.mpr direct.symm
  let prefixSum {n : ℕ} (lengths : Fin n → ℕ) (i : Fin n) :=
    ∑ k : Fin i.val, lengths (Fin.castLE i.isLt.le k)
  change prefixSum ((I.pushWord L).ports.lengths (I.site v))
      (((I.pushWord L).order (I.site v)).symm (I.port v (L.order v j))) =
    prefixSum (L.ports.lengths v) ((L.order v).symm (L.order v j))
  rw [inv,Equiv.symm_apply_apply]
  dsimp only [prefixSum]
  exact Finset.sum_congr rfl (fun k _=>push_order_lengths I L hw v (Fin.castLE j.isLt.le k))


end
end ThreeFlat.Diagonal.HistoryRelabel

namespace ThreeFlat.Diagonal.CompressorPacking.ChildSend
open HistoryContraction PhysicalStage LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Native.ShrinkStage
open scoped Classical BigOperators
noncomputable section
variable {d l c : ℕ} {H T X Pins : Type} [AddCommGroup H] [AddCommGroup T] [AddCommGroup X]
variable [Fintype H] [Fintype T] [Fintype X] (A : State d l)
variable (u : BitWord l ≃+ BitWord (c+1) × H × T × X) (P : PackingData A.Base H T X d (c+1))
variable (agree : StageAddress.packedGraph P=changeLanes A.graph u)
local notation "I" => StageAddress.shrinkInputIso A.graph A.chart u P agree A.width

/-- Slot graphs have distinct endpoint bases. Thus at a fixed site the source
edge determines even the polarity of its half-port. -/
private theorem port_edge_ext {z : A.Site} {p q : A.shape.graph.Port z} (same : p.val.1=q.val.1) : p=q := by
  rcases p with ⟨⟨e,b⟩,pb⟩
  rcases q with ⟨⟨f,c'⟩,qc⟩
  change e=f at same
  subst f
  cases b <;> cases c' <;> try rfl
  · exact False.elim (A.graph.base.ends_ne e.1
      (congrArg (fun s : A.Base × BitWord l => s.1) (A.chart.injective (qc.trans pb.symm))))
  · exact False.elim (A.graph.base.ends_ne e.1
      (congrArg (fun s : A.Base × BitWord l => s.1) (A.chart.injective (pb.trans qc.symm))))

theorem old_port (L : A.Words Pins) (ord : A.OrderedHalves L) (x : A.Base×BitWord l)
    (j : Fin (L.count (A.chart x))) :
    L.order (A.chart x) j=Halves.portOrder A.graph A.chart x (j.cast (ord.count _)) := by
  apply port_edge_ext A
  let k := j.cast (ord.count (A.chart x))
  have site := congrArg (fun s => Halves.sourceHalf A.graph s k) (A.chart.symm_apply_apply x)
  have edge := congrArg Prod.fst (Halves.portOrder_value A.graph A.chart x k)
  exact (ord.edge (A.chart x) j).trans (site.trans edge.symm)

/-- Lane splitting preserves the source and target slot numbers exactly. -/
theorem splitPortOrdinal (x : A.Base×BitWord l) (p : A.shape.graph.Port (A.chart x)) :
    ((portOrder P ((I).site (A.chart x))).symm ((I).port (A.chart x) p)).val=
      ((Halves.portOrder A.graph A.chart x).symm p).val := by
  rcases p with ⟨⟨e,b⟩,inc⟩
  cases b with
  | false=>rfl
  | true=>
    change d+(P.actual (StageAddress.splitEdge u e)).1.2.val=d+(A.graph.actualTarget e).1.2.val
    exact congrArg (fun z=>d+z.1.2.val) (StageAddress.actual_conjugacy A.graph u P agree e)

/-- The native old half table is indexed exactly as the real packed old port
used by a shrink demand, including incoming rows. -/
theorem predecessor_prefix (L : A.Words Pins) (ord : A.OrderedHalves L)
    (v : Position A.Base H T X (c+1)) (p : (oldGraph P).Port v) :
    Halves.prefixValue A.graph A.width (A.chart.symm ((I).site.symm v)) ((portOrder P v).symm p)=
      ((I).pushWord L).ports.start v p := by
  obtain ⟨y,rfl⟩:=(I).site.surjective v
  obtain ⟨x,rfl⟩:=A.chart.surjective y
  obtain ⟨a,rfl⟩:=((I).port (A.chart x)).surjective p
  obtain ⟨j,rfl⟩:=(L.order (A.chart x)).surjective a
  have number : (portOrder P ((I).site (A.chart x))).symm ((I).port (A.chart x) (L.order (A.chart x) j))=
      j.cast (ord.count _) := by
    apply Fin.ext
    rw [splitPortOrdinal A u P agree,old_port A L ord,Equiv.symm_apply_apply]
  have width (e) : A.width e=(A.width ∘ (StageAddress.splitEdge u).symm) ((I).edge e) := by
    change A.width e=A.width ((StageAddress.splitEdge u).symm ((StageAddress.splitEdge u) e))
    rw [Equiv.symm_apply_apply]
  have chartAt : A.chart.symm ((I).site.symm ((I).site (A.chart x))) =
      A.chart.symm (A.chart x) :=
    congrArg (fun z : A.Site => A.chart.symm z) ((I).site.symm_apply_apply (A.chart x))
  rw [number]
  calc
    _ = Halves.prefixValue A.graph A.width (A.chart.symm (A.chart x)) (j.cast (ord.count _)) :=
      congrArg (fun z : A.Base × BitWord l =>
        Halves.prefixValue A.graph A.width z (j.cast (ord.count _))) chartAt
    _ = L.ports.start (A.chart x) (L.order (A.chart x) j) := by
      let totalBefore (k : Fin (L.count (A.chart x))) :=
        ∑ i : Fin k.val, L.ports.lengths (A.chart x) (Fin.castLE k.isLt.le i)
      change _ = totalBefore ((L.order (A.chart x)).symm (L.order (A.chart x) j))
      rw [(L.order (A.chart x)).symm_apply_apply j]
      exact ord.start (A.chart x) j
    _ = _ := ((I).pushWord_start L width (A.chart x) (L.order (A.chart x) j)).symm

/-- Read field three of the selected physical half row directly into the
shrinking subtree's packed word layout. -/
theorem predecessor_half_row (L : A.Words Pins) (ord : A.OrderedHalves L)
    (v : Position A.Base H T X (c+1)) (mem : ℕ→ℕ) (table : ℕ)
    (rows : ∀j : Fin (2*d),mem (table+(4*j.val+3))=
      Halves.prefixValue A.graph A.width (A.chart.symm ((I).site.symm v)) j)
    (p : (oldGraph P).Port v) :
    mem (table+(4*((portOrder P v).symm p).val+3))=((I).pushWord L).ports.start v p :=
  (rows _).trans (predecessor_prefix A u P agree L ord v p)

/-- Field two of the native demand location selects precisely this packed
child port's width-prefix cell (field three of its half record). -/
theorem predecessor_request_row (L : A.Words Pins) (ord : A.OrderedHalves L) (lay : Bool)
    (v : Site A.Base T X) (x : Request (A.width ∘ (StageAddress.splitEdge u).symm))
    (placed : P.placement lay ((oldGraph P).vertex x.1 x.2.1)=v) (mem : ℕ→ℕ) (table : ℕ)
    (rows : ∀j : Fin (2*d),mem (table+(4*j.val+3))=Halves.prefixValue A.graph A.width
      (A.chart.symm ((I).site.symm (ownedChild lay v x placed).val)) j) :
    mem (table+(4*(words P (A.width ∘ (StageAddress.splitEdge u).symm) lay v x placed 2)+3))=
      ((I).pushWord L).ports.start (ownedChild lay v x placed).val (ownedPort lay v x placed) :=
  predecessor_half_row A u P agree L ord _ mem table rows _


end
end ThreeFlat.Diagonal.CompressorPacking.ChildSend

end OAI

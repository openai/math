import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecord
import OAI.LinearAlgebra.SpectralBooks.ReplacementConnected
import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsViews

/-! # Expanding local patch records to a certified old map

The saved slots on the records give a consecutive numbering on the expanded
graph. A passing exterior edge reads the named stubs at both endpoints.
Together with the internal checks in each record these are exactly the old
map verifier on the glued graph, including both ends of internal loops.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph.PatchRecord

variable {J A : Type} {K : ℕ} (R : J → PatchRecord K A)
  (C : StubPairing (fun j => (R j).shape.Stub))

abbrev pieces (j : J) := (R j).toPiece
abbrev vertices := StubPairing.Vertex (pieces R)
abbrev graph := C.assemble (pieces R)

private def reassoc :
    (Σ j, (R j).shape.Dart) ≃ Σ v : vertices R, Fin ((R v.1).shape.typeAt v.2).degree.val where
  toFun q := ⟨⟨q.1,q.2.1⟩, q.2.2⟩
  invFun q := ⟨q.1.1, q.1.2, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- At an assembled dart, read its old occurrence, old vertex and numbered
port. Every original numbered port occurs once. -/
def namedDarts : C.Edge (pieces R) × Bool ≃
    Σ v : vertices R, Fin ((R v.1).shape.typeAt v.2).degree.val :=
  ((C.dartEquiv (pieces R)).trans (Equiv.sigmaCongrRight (fun j => (R j).shape.endEquiv))).trans (reassoc R)

theorem namedDarts_owner (q : C.Edge (pieces R) × Bool) :
    (namedDarts R C q).1 = (graph R C).vertex q.1 q.2 := by
  rcases q with ⟨(e | ⟨j,d⟩),(_|_)⟩ <;> rfl

variable (orient : ∀ (e : C.Wire) (b : Bool), (C.ends (e,b)).2.val.side = b)

include orient in
theorem namedDarts_side (q : C.Edge (pieces R) × Bool) :
    ((R (namedDarts R C q).1.1).shape.typeAt (namedDarts R C q).1.2).direction
      (namedDarts R C q).2 = q.2 := by
  rcases q with ⟨e | ⟨j,d⟩,b⟩
  · exact orient e b
  · exact (R j).shape.read_internal_side d b

private def fiberSlot {V : Type} {F : V → Type} (v : V) :
    {q : Σ v, F v // q.1 = v} ≃ F v where
  toFun := fun ⟨⟨_,i⟩,h⟩ => h ▸ i
  invFun i := ⟨⟨v,i⟩, rfl⟩
  left_inv := by rintro ⟨⟨_,i⟩,rfl⟩; rfl
  right_inv _ := rfl

private theorem fiberSlot_val {V : Type} {F : V → ℕ} (v : V)
    (q : {q : Σ v, Fin (F v) // q.1 = v}) : (fiberSlot v q).val = q.val.2.val := by
  rcases q with ⟨⟨_,i⟩,rfl⟩
  rfl

/-- The actual ports at an old vertex are exactly the slots listed for it in
its record. -/
def slotEquiv (v : vertices R) :
    (graph R C).Port v ≃ Fin ((R v.1).shape.typeAt v.2).degree.val :=
  ((namedDarts R C).subtypeEquiv (fun q => by rw [namedDarts_owner])).trans (fiberSlot v)

theorem slotEquiv_val {v : vertices R} (d : (graph R C).Port v) :
    (slotEquiv R C v d).val = (namedDarts R C d.val).2.val := by
  let a := namedDarts R C d.val
  have h : a.1 = v := (namedDarts_owner R C d.val).trans d.property
  change (fiberSlot v ⟨a,h⟩).val = a.2.val
  exact fiberSlot_val v _

private theorem card_ports [Fintype J] (v : vertices R) :
    Fintype.card ((graph R C).Port v) = ((R v.1).shape.typeAt v.2).degree.val := by
  rw [Fintype.card_congr (slotEquiv R C v), Fintype.card_fin]

variable [Fintype J] (r : vertices R) (hc : (graph R C).ConnectedFrom r)

/-- The reconstructed rooted numbered graph carries exactly the port orders
advertised in its records. -/
def asMap : RootedMap (vertices R) (C.Edge (pieces R)) where
  graph := graph R C
  root := r
  connected := hc
  num v := (slotEquiv R C v).trans (finCongr (card_ports R C v).symm)
  degree v := (card_ports R C v).le.trans (Nat.le_of_lt_succ ((R v.1).shape.typeAt v.2).degree.isLt)

theorem asMap_portNumber (e : C.Edge (pieces R)) (b : Bool) :
    (asMap R C r hc).portNumber e b = (namedDarts R C (e,b)).2.val :=
  slotEquiv_val R C _

variable (hr : ∀ v : vertices R, ((R v.1).shape.typeAt v.2).root = decide (v = r))

include orient hr in
/-- Directions, root flag, and degree all coincide with the listed old type. -/
theorem asMap_typeAt (v : vertices R) : (asMap R C r hc).typeAt v = (R v.1).shape.typeAt v.2 := by
  have map_ext {t s : MapType} (hd : t.degree.val = s.degree.val) (hf : t.root = s.root)
      (ha : ∀ a b, a.val = b.val → t.direction a = s.direction b) : t = s := by
    obtain ⟨d,f,i⟩ := t
    obtain ⟨d',f',i'⟩ := s
    obtain rfl : d = d' := Fin.ext hd
    obtain rfl : f = f' := hf
    exact congrArg (MapType.mk d f) (funext fun a => ha a a rfl)
  apply map_ext (card_ports R C v) (hr v).symm
  intro a b hab
  let p := ((asMap R C r hc).num v).symm a
  have hp : (slotEquiv R C v p).val = b.val := by
    exact (congrArg Fin.val (((asMap R C r hc).num v).apply_symm_apply a)).trans hab
  have hd := namedDarts_side R C orient p.val
  have ho : (namedDarts R C p.val).1 = v := (namedDarts_owner R C p.val).trans p.property
  have hn : (namedDarts R C p.val).2.val = b.val := (slotEquiv_val R C p).symm.trans hp
  change p.val.2 = _
  generalize namedDarts R C p.val = x at ho hn hd
  obtain ⟨y,i⟩ := x
  dsimp only at ho hn hd
  subst y
  rw [Fin.ext hn] at hd
  exact hd.symm

/-- Old certificate fields on expanded vertices are read unchanged. -/
def labels (v : vertices R) := (R v.1).label v.2

/-- Test the numbered old ports and their full certificates at a pair of stubs. -/
def stubTest (T : MapLabelTests A) (d t : Σ j, (R j).shape.Stub) : Prop :=
  let p := d.2.val
  let q := t.2.val
  T.edge (p.2.castLE (Nat.le_of_lt_succ ((R d.1).shape.typeAt p.1).degree.isLt))
    (q.2.castLE (Nat.le_of_lt_succ ((R t.1).shape.typeAt q.1).degree.isLt))
    ((R d.1).label p.1) ((R t.1).label q.1)

include orient hr in
/-- Each old vertex test and each old edge test passes on the single expanded
map, verifying the hypotheses of the old map-label theorem. -/
theorem asMap_pass {I : Type*} (T : MapLabelTests A) (name : A → ℕ) (id : A → I)
    (valid : ∀ j, (R j).Valid name id T.vertex T.edge)
    (external : ∀ e, stubTest R T (C.ends (e,false)) (C.ends (e,true))) :
    T.Pass (asMap R C r hc) (labels R) := by
  constructor
  · intro v
    rw [asMap_typeAt R C orient r hc hr]
    exact (valid v.1).vertexTests v.2
  · have hs (e : C.Edge (pieces R)) (b : Bool) :
        (asMap R C r hc).slots _ ⟨(e,b),rfl⟩ =
        (namedDarts R C (e,b)).2.castLE (Nat.le_of_lt_succ
          ((R (namedDarts R C (e,b)).1.1).shape.typeAt (namedDarts R C (e,b)).1.2).degree.isLt) :=
      Fin.ext (asMap_portNumber R C r hc e b)
    rintro (e | ⟨j,e⟩)
    · rw [hs, hs]
      exact external e
    · rw [hs, hs]
      exact (valid j).edgeTests e

end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI

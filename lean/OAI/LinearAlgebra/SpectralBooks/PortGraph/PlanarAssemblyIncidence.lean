import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldMap
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarNumberedRotation

/-! # Darts of a glued ribbon graph

In occurrence coordinates each vertex rotation is computed in its own piece.
Internal wires switch their two sides in the piece. Exterior wires switch two
named stubs according to the common boundary pairing.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm

namespace PortGraph

private theorem finCongr_rotate {m n : ℕ} (h : m = n) (x : Fin m) :
    finCongr h (finRotate m x) = finRotate n (finCongr h x) := by subst n; rfl

namespace StubPairing

universe u
variable {J : Type u} {S : J → Type u} (C : StubPairing S) (P : ∀ j, OpenPiece (S j))

abbrev PieceDart (j : J) := ((P j).Edge × Bool) ⊕ S j

/-- The exterior partner of a named stub, including its destination occurrence. -/
def stubMate : Perm (Σ j, S j) := C.ends.permCongr PortGraph.cross

/-- Internal darts switch in place, exterior darts follow the boundary pairing. -/
def pairedDart : (Σ j, PieceDart P j) → Σ j, PieceDart P j
  | ⟨j,.inl q⟩ => ⟨j,.inl (PortGraph.cross q)⟩
  | ⟨j,.inr s⟩ => let t := C.stubMate ⟨j,s⟩; ⟨t.1, .inr t.2⟩

theorem dartEquiv_cross (p : C.Edge P × Bool) :
    C.dartEquiv P (PortGraph.cross p) = C.pairedDart P (C.dartEquiv P p) := by
  rcases p with ⟨e | ⟨j,e⟩, b⟩
  · let inj : (Σ j, S j) → Σ j, PieceDart P j := fun t => ⟨t.1,.inr t.2⟩
    exact congrArg inj (by simp [stubMate] :
      C.ends (PortGraph.cross (e,b)) = C.stubMate (C.ends (e,b)))
  · rfl

/-- Embed the two sides of each cut wire in the assembled set of darts. -/
def exteriorMark : C.Wire × Bool ↪ C.Edge P × Bool where
  toFun q := (.inl q.1,q.2)
  inj' := by rintro ⟨e,b⟩ ⟨e',b'⟩ h; simpa using h

/-- Embed a stub by recovering its cut wire and side through the pairing. -/
def stubMark : (Σ j, S j) ↪ C.Edge P × Bool :=
  C.ends.symm.toEmbedding.trans (C.exteriorMark P)

theorem dartEquiv_stubMark (s : Σ j, S j) :
    C.dartEquiv P (C.stubMark P s) = ⟨s.1, Sum.inr s.2⟩ := by
  obtain ⟨⟨e,b⟩,rfl⟩ := C.ends.surjective s
  change C.dartEquiv P (C.exteriorMark P (C.ends.symm (C.ends (e,b)))) = _
  rw [C.ends.symm_apply_apply]
  rfl

/-- Cross just the cut wires, fixing both sides of every internal wire. -/
def outsidePairing : Perm (C.Edge P × Bool) :=
  Function.Involutive.toPerm (fun q => match q with
    | (.inl e,b) => (.inl e,!b)
    | (.inr e,b) => (.inr e,b)) (by rintro ⟨e|e,b⟩ <;> cases b <;> rfl)

theorem outsidePairing_mark (q : C.Wire × Bool) :
    C.outsidePairing P (C.exteriorMark P q) = C.exteriorMark P (PortGraph.cross q) := rfl

theorem outsidePairing_off_mark (x : C.Edge P × Bool) (h : x ∉ Set.range (C.exteriorMark P)) :
    C.outsidePairing P x = x := by
  rcases x with ⟨e|e,b⟩
  · exact False.elim (h ⟨(e,b),rfl⟩)
  · rfl

theorem outsidePairing_apply (x : C.Edge P × Bool) :
    C.outsidePairing P x = if (C.dartEquiv P x).1 = (C.dartEquiv P (PortGraph.cross x)).1
      then x else PortGraph.cross x := by
  rcases x with ⟨e|⟨j,e⟩,b⟩
  · cases b
    · exact (ite_eq_right (C.cross e)).symm
    · exact (ite_eq_right (C.cross e).symm).symm
  · exact (ite_eq_left rfl).symm

theorem outsidePairing_support_card [Fintype J] :
    (C.outsidePairing P).support.card = Fintype.card (C.Wire × Bool) := by
  let a : C.Wire × Bool ≃ ↥(C.outsidePairing P).support :=
    { toFun := fun q => ⟨C.exteriorMark P q, mem_support.mpr (by
        rw [C.outsidePairing_mark]
        exact (C.exteriorMark P).injective.ne (by cases q with | mk e b => cases b <;> intro h; all_goals cases h))⟩
      invFun := by
        rintro ⟨⟨e|e,b⟩,h⟩
        · exact (e,b)
        · exact False.elim ((mem_support.mp h) rfl)
      left_inv := by rintro ⟨e,b⟩; rfl
      right_inv := by rintro ⟨⟨e|e,b⟩,h⟩; exact rfl; exact False.elim ((mem_support.mp h) rfl) }
  simpa only [Fintype.card_coe] using (Fintype.card_congr a).symm

/-- Apply independent permutations of the piece darts in global edge coordinates. -/
def liftPiecePerm (f : ∀ j, Perm (PieceDart P j)) : Perm (C.Edge P × Bool) :=
  (C.dartEquiv P).symm.permCongr (Equiv.sigmaCongrRight f)

theorem dartEquiv_liftPiecePerm (f : ∀ j, Perm (PieceDart P j)) (x : C.Edge P × Bool) :
    C.dartEquiv P (C.liftPiecePerm P f x) = Equiv.sigmaCongrRight f (C.dartEquiv P x) :=
  (C.dartEquiv P).apply_symm_apply _

/-- Cross the internal wires of this occurrence and fix its boundary stubs. -/
def insideMate (j : J) : Perm (PieceDart P j) := Equiv.sumCongr PortGraph.cross (Equiv.refl _)

theorem liftPiecePerm_subpairing (f : ∀ j, Perm (PieceDart P j))
    (hf : ∀ j d, f j d = d ∨ f j d = insideMate P j d) (x : C.Edge P × Bool) :
    C.liftPiecePerm P f x = x ∨ C.liftPiecePerm P f x = PortGraph.cross x := by
  let e := C.dartEquiv P
  rcases hf (e x).1 (e x).2 with h | h
  · left
    apply e.injective
    exact (C.dartEquiv_liftPiecePerm P f x).trans (congrArg (Sigma.mk _) h)
  · rcases x with ⟨a | ⟨j,a⟩,b⟩
    · exact Or.inl (e.injective ((C.dartEquiv_liftPiecePerm P f _).trans (congrArg (Sigma.mk _) h)))
    · exact Or.inr (e.injective ((C.dartEquiv_liftPiecePerm P f _).trans (congrArg (Sigma.mk _) h)))

theorem inside_disjoint_outside : (C.liftPiecePerm P (insideMate P)).Disjoint (C.outsidePairing P) := by
  rintro ⟨e|⟨j,e⟩, b⟩
  · left
    apply (C.dartEquiv P).injective
    exact C.dartEquiv_liftPiecePerm P _ _
  · exact Or.inr rfl

/-- Crossing all internal wires followed by the boundary matching gives the full edge pairing. -/
theorem inside_mul_outsidePairing :
    C.liftPiecePerm P (insideMate P) * C.outsidePairing P = PortGraph.cross := by
  apply Equiv.ext
  rintro ⟨e|⟨j,e⟩, b⟩
  all_goals
    apply (C.dartEquiv P).injective
    rw [mul_apply, dartEquiv_liftPiecePerm]
    rfl

/-- Collect the ports of a single piece at their vertices. -/
def piecePorts (j : J) : (Σ v, LocalPort P j v) ≃ PieceDart P j :=
  (Equiv.sigmaCongrRight fun v => (Equiv.subtypeSum
    (p := fun q => owner P j q = v)).symm).trans (Equiv.sigmaFiberEquiv (owner P j))

theorem dartEquiv_port (j : J) (v : (P j).Vertex) (p : (C.assemble P).Port ⟨j,v⟩) :
    C.dartEquiv P p.val = ⟨j, piecePorts P j ⟨v,C.portEquiv P j v p⟩⟩ := by
  obtain ⟨t,rfl⟩ := (C.portEquiv P j v).symm.surjective p
  rw [Equiv.apply_symm_apply]
  rcases t with x | x
  · exact (C.dartEquiv P).apply_symm_apply ⟨j,.inl x.val⟩
  · exact (C.dartEquiv P).apply_symm_apply ⟨j,.inr x.val⟩

variable [∀ j, Fintype (S j)]

abbrev PieceNumbering := ∀ j v, LocalPort P j v ≃ Fin (Fintype.card (LocalPort P j v))

/-- The permutation on a piece obtained by turning in its given port order. -/
def pieceTurn (num : PieceNumbering P) (j : J) : Perm (PieceDart P j) :=
  (piecePorts P j).permCongr (Equiv.sigmaCongrRight fun v =>
    (num j v).symm.permCongr (finRotate _))

theorem pieceTurn_port (num : PieceNumbering P) (j : J) (v : (P j).Vertex) (p : LocalPort P j v) :
    pieceTurn P num j (piecePorts P j ⟨v,p⟩) =
      piecePorts P j ⟨v, (num j v).symm (finRotate _ (num j v p))⟩ := by
  simp [pieceTurn]

variable [Fintype J]

private theorem portEquiv_successor (num : PieceNumbering P) (j : J) (v : (P j).Vertex)
    (p : (C.assemble P).Port ⟨j,v⟩) :
    C.portEquiv P j v ((C.assembleNumbering P num).successor ⟨j,v⟩ p) =
      (num j v).symm (finRotate _ (num j v (C.portEquiv P j v p))) := by
  let e := C.portEquiv P j v
  let n := num j v
  let a := finCongr (C.card_assemble_port P j v).symm
  change e (e.symm (n.symm (a.symm (finRotate _ (a (n (e p))))))) = n.symm _
  rw [e.apply_symm_apply, ← finCongr_rotate, Equiv.symm_apply_apply]

theorem dartEquiv_assemble_turn (num : PieceNumbering P) (p : C.Edge P × Bool) :
    C.dartEquiv P ((C.assembleNumbering P num).turn p) =
      Equiv.sigmaCongrRight (pieceTurn P num) (C.dartEquiv P p) := by
  suffices h : ∀ (v : Vertex P) (q : (C.assemble P).Port v),
      C.dartEquiv P ((C.assembleNumbering P num).turn q.val) =
        Equiv.sigmaCongrRight (pieceTurn P num) (C.dartEquiv P q.val) from h _ ⟨p,rfl⟩
  rintro ⟨j,v⟩ q
  rw [Numbering.turn_port, C.dartEquiv_port P j v q, C.dartEquiv_port, C.portEquiv_successor]
  exact congrArg (Sigma.mk j) (pieceTurn_port P num j v _).symm

omit [∀ j, Fintype (S j)]

/-- Rotate each vertex after switching along the edges of a local forest. -/
def turnAfterForest (num : (C.assemble P).Numbering) (f : ∀ j, Perm (PieceDart P j)) :
    Perm (C.Edge P × Bool) :=
  num.turn * (C.dartEquiv P).symm.permCongr (Equiv.sigmaCongrRight f)

theorem dartEquiv_turnAfterForest (num : (C.assemble P).Numbering)
    (t f : ∀ j, Perm (PieceDart P j))
    (ht : ∀ p, C.dartEquiv P (num.turn p) = Equiv.sigmaCongrRight t (C.dartEquiv P p))
    (p : C.Edge P × Bool) :
    C.dartEquiv P (C.turnAfterForest P num f p) =
      Equiv.sigmaCongrRight (fun j => t j * f j) (C.dartEquiv P p) := by
  simp only [turnAfterForest, mul_apply, ht, permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

theorem card_vertices : Fintype.card (Vertex P) = ∑ j, Fintype.card (P j).Vertex :=
  Fintype.card_sigma

theorem card_edges : Fintype.card (C.Edge P) = Fintype.card C.Wire + ∑ j, Fintype.card (P j).Edge := by
  simp [Edge, Fintype.card_sigma]

section OccurrenceCycles

open HyperbolicObstruction.PictureSwitch

variable {D I : Type*} {L : I → Type*}
    (e : D ≃ Σ i, L i) (g : Perm D) (p : ∀ i, Perm (L i))
    (h : ∀ d, e (g d) = Equiv.sigmaCongrRight p (e d))

include h

/-- An assembled orbit is classified by its occurrence and its local orbit. -/
theorem sameCycle_iff_pieceClass (x y : D) :
    g.SameCycle x y ↔ (⟨(e x).1,Quotient.mk _ (e x).2⟩ : Σ i, VertexClasses (p i)) =
      ⟨(e y).1,Quotient.mk _ (e y).2⟩ := by
  let c : (Σ i, L i) → Σ i, VertexClasses (p i) := fun d => ⟨d.1, Quotient.mk _ d.2⟩
  constructor
  · intro hh
    apply sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Σ i, VertexClasses (p i))))
      (j := fun d => c (e d)) ?_ hh)
    intro d
    rw [h]
    exact congrArg (Sigma.mk (e d).1) (Quotient.sound (SameCycle.rfl (f := p (e d).1)).apply_left)
  · have lift (i : I) (z : L i) : e.symm ⟨i,p i z⟩ = g (e.symm ⟨i,z⟩) := by
      apply e.injective
      simp only [h,Equiv.apply_symm_apply]
      rfl
    obtain ⟨⟨a,x⟩,rfl⟩ := e.symm.surjective x
    obtain ⟨⟨b,y⟩,rfl⟩ := e.symm.surjective y
    change c (e (e.symm ⟨a,x⟩)) = c (e (e.symm ⟨b,y⟩)) → _
    rw [e.apply_symm_apply, e.apply_symm_apply]
    intro he
    obtain rfl : a = b := congrArg Sigma.fst he
    exact semiconj_perm_sameCycle (j := fun z => e.symm ⟨a,z⟩) (lift a)
      (Quotient.exact (Sigma.mk.inj_iff.mp he).2.eq)

/-- When every local contour has a single orbit, two darts lie on the same
assembled contour precisely when their occurrences coincide. -/
theorem sameCycle_iff_piece (hc : ∀ i (x y : L i), (p i).SameCycle x y) (x y : D) :
    g.SameCycle x y ↔ (e x).1 = (e y).1 := by
  rw [sameCycle_iff_pieceClass e g p h]
  refine ⟨congrArg Sigma.fst, ?_⟩
  generalize e x = a; generalize e y = b
  rcases a with ⟨a,x⟩
  rcases b with ⟨b,y⟩
  rintro rfl
  exact congrArg (Sigma.mk a) (Quotient.sound (hc a x y))

variable [Fintype D] [Fintype I] [∀ i, Fintype (L i)] [DecidableEq D] [∀ i, DecidableEq (L i)]

/-- The assembly cycle count is additive over its occurrence permutations. -/
theorem cycles_of_piecePerm : cycles g = ∑ i, cycles (p i) := by
  let (i : I) := Fintype.ofFinite (VertexClasses (p i))
  let c : D → Σ i, VertexClasses (p i) := fun x => ⟨(e x).1, Quotient.mk _ (e x).2⟩
  have hs : Function.Surjective c := by
    rintro ⟨i,q⟩
    obtain ⟨d,rfl⟩ := Quotient.exists_rep q
    let cls : (Σ i, L i) → Σ i, VertexClasses (p i) := fun z => ⟨z.1, Quotient.mk _ z.2⟩
    exact ⟨e.symm ⟨i,d⟩, congrArg cls (e.apply_symm_apply _)⟩
  rw [cycles_of_classifier g c (sameCycle_iff_pieceClass e g p h) hs, Fintype.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [cycles_eq_card_classes,Nat.card_eq_fintype_card]

/-- The support consists exactly of the moved darts in each piece. -/
theorem support_card_of_piecePerm : g.support.card = ∑ i, (p i).support.card := by
  let forget : (Σ i, ↥(p i).support) → Σ i, L i := fun z => ⟨z.1,z.2.val⟩
  have inj : Function.Injective forget := by
    rintro ⟨i,x⟩ ⟨j,y⟩ he
    obtain rfl : i = j := congrArg Sigma.fst he
    exact congrArg (Sigma.mk i) (Subtype.ext (Sigma.mk.inj_iff.mp he).2.eq)
  let a : ↥g.support ≃ Σ i, ↥(p i).support :=
    { toFun := fun ⟨d,hd⟩ => ⟨(e d).1, (e d).2, mem_support.mpr fun hh =>
        mem_support.mp hd (e.injective ((h d).trans (congrArg (Sigma.mk _) hh)))⟩
      invFun := fun ⟨i,d⟩ => ⟨e.symm ⟨i,d.val⟩, mem_support.mpr fun he =>
        mem_support.mp d.property (by
          have ht := (h (e.symm ⟨i,d.val⟩)).symm.trans (congrArg e he)
          simp only [Equiv.apply_symm_apply] at ht
          exact (Sigma.mk.inj_iff.mp ht).2.eq)⟩
      left_inv := fun d => Subtype.ext (e.symm_apply_apply d.val)
      right_inv := by
        rintro ⟨i,⟨d,hd⟩⟩
        exact inj (e.apply_symm_apply _) }
  simpa only [Fintype.card_coe, Fintype.card_sigma] using Fintype.card_congr a

end OccurrenceCycles

end StubPairing

namespace PatchRecord

variable {J A : Type} {K : ℕ} (R : J → PatchRecord K A)
  (C : StubPairing (fun j => (R j).shape.Stub))

/-- The old records rotate by the successor in each recorded list of slots. -/
def recordTurn (j : J) : Perm (StubPairing.PieceDart (pieces R) j) :=
  (R j).shape.endEquiv.symm.permCongr (Equiv.sigmaCongrRight fun _ => finRotate _)

private theorem namedDarts_port (v : vertices R) (p : (graph R C).Port v) :
    namedDarts R C p.val = ⟨v, slotEquiv R C v p⟩ := by
  obtain ⟨w,i⟩ := v
  have ho := (namedDarts_owner R C p.val).trans p.property
  have hv := slotEquiv_val R C p
  generalize namedDarts R C p.val = q at ho hv ⊢
  obtain ⟨q,k⟩ := q
  obtain rfl : q = ⟨w,i⟩ := ho
  exact congrArg (Sigma.mk _) (Fin.ext hv.symm)

variable [Fintype J] (r : vertices R) (hc : (graph R C).ConnectedFrom r)

theorem namedDarts_asMap_turn (p : C.Edge (pieces R) × Bool) :
    namedDarts R C ((asMap R C r hc).num.turn p) =
      Equiv.sigmaCongrRight (fun _ => finRotate _) (namedDarts R C p) := by
  let M := asMap R C r hc
  suffices h : ∀ v (q : (graph R C).Port v), namedDarts R C (M.num.turn q.val) =
      Equiv.sigmaCongrRight (fun _ => finRotate _) (namedDarts R C q.val) from h _ ⟨p,rfl⟩
  intro v q
  rw [M.num.turn_port q, namedDarts_port R C v q, namedDarts_port R C v (M.num.successor v q)]
  apply congrArg (Sigma.mk v)
  have deg : ((R v.1).shape.typeAt v.2).degree.val = Fintype.card ((graph R C).Port v) := by
    rw [Fintype.card_congr (slotEquiv R C v), Fintype.card_fin]
  let e := slotEquiv R C v
  let a := finCongr deg
  change e (e.symm (a.symm (finRotate _ (a (e q))))) = _
  rw [e.apply_symm_apply, ← finCongr_rotate, Equiv.symm_apply_apply]

/-- In occurrence coordinates the old map turns entirely inside its record. -/
theorem dartEquiv_asMap_turn (p : C.Edge (pieces R) × Bool) :
    C.dartEquiv (pieces R) ((asMap R C r hc).num.turn p) =
      Equiv.sigmaCongrRight (recordTurn R) (C.dartEquiv (pieces R) p) := by
  let e := C.dartEquiv (pieces R)
  let n := namedDarts R C
  apply (e.symm.trans n).injective
  change n (e.symm (e _)) = n (e.symm _)
  rw [e.symm_apply_apply, namedDarts_asMap_turn]
  change _ = ((e.symm.trans n) (Equiv.sigmaCongrRight (recordTurn R) (e p)))
  suffices h : ∀ d, Equiv.sigmaCongrRight (fun _ => finRotate _) ((e.symm.trans n) d) =
      (e.symm.trans n) (Equiv.sigmaCongrRight (recordTurn R) d) by
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using h (e p)
  rintro ⟨j,d⟩
  dsimp only [e, n, namedDarts, Equiv.trans_apply]
  simp only [Equiv.apply_symm_apply]
  change (⟨⟨j,((R j).shape.endEquiv d).1⟩, finRotate _ ((R j).shape.endEquiv d).2⟩ :
      Σ v : vertices R, Fin ((R v.1).shape.typeAt v.2).degree.val) =
    ⟨⟨j, ((R j).shape.endEquiv (recordTurn R j d)).1⟩, ((R j).shape.endEquiv (recordTurn R j d)).2⟩
  have ht : (R j).shape.endEquiv (recordTurn R j d) = Equiv.sigmaCongrRight
      (fun _ => finRotate _) ((R j).shape.endEquiv d) := (R j).shape.endEquiv.apply_symm_apply _
  rw [ht]
  rfl

end PatchRecord
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI

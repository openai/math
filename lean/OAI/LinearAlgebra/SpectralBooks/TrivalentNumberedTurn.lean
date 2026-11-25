import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentNamedForest

/-! # Vertex rotations of numbered trivalent pieces

The assembly's rotation depends only on the numbering of the local ports of
the occurrence. Substituting the output-left-right numbering yields the
positive turn of the named trivalent tree.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv

namespace PortGraph

universe u
variable {S : Type u}

namespace OpenPiece
variable (O : OpenPiece S)

abbrev Ports (v : O.Vertex) := O.graph.Port v ⊕ {s // O.attach s = v}

/-- Gather the ports by owner in an open piece. -/
def localDarts : (Σ v, O.Ports v) ≃ ((O.Edge × Bool) ⊕ S) :=
  StubPairing.piecePorts (fun _ : PUnit.{u+1} => O) .unit

/-- A cycle through the numbered ports at each vertex of one open piece. -/
def slotTurn {n : O.Vertex → ℕ} (num : ∀ v, O.Ports v ≃ Fin (n v)) : Perm ((O.Edge × Bool) ⊕ S) :=
  O.localDarts.permCongr (Equiv.sigmaCongrRight fun v => (num v).symm.permCongr (finRotate _))

theorem slotTurn_port {n : O.Vertex → ℕ} (num : ∀ v, O.Ports v ≃ Fin (n v))
    (v : O.Vertex) (p : O.Ports v) :
    O.slotTurn num (O.localDarts ⟨v,p⟩) = O.localDarts ⟨v,(num v).symm (finRotate _ (num v p))⟩ := by
  simp [slotTurn]

private theorem rotate_cast {n m : ℕ} (h : n = m) (i : Fin n) :
    (finCongr h).symm (finRotate _ (finCongr h i)) = finRotate n i := by
  subst m
  rfl

/-- Replacing a slot count by an equal natural number preserves the turn. -/
theorem slotTurn_finCongr {n m : O.Vertex → ℕ} (num : ∀ v, O.Ports v ≃ Fin (n v))
    (hm : ∀ v, n v = m v) :
    O.slotTurn (fun v => (num v).trans (finCongr (hm v))) = O.slotTurn num := by
  ext a
  obtain ⟨⟨v,p⟩,rfl⟩ := O.localDarts.surjective a
  simp only [slotTurn_port, Equiv.trans_apply, Equiv.symm_trans_apply, rotate_cast]

end OpenPiece

/-- The assembly's occurrence rotation is the rotation of the single numbered piece. -/
theorem StubPairing.pieceTurn_eq_slotTurn {J : Type u} {T : J → Type u} [∀ j, Fintype (T j)]
    (P : ∀ j, OpenPiece (T j)) (num : StubPairing.PieceNumbering P) (j : J) :
    StubPairing.pieceTurn P num j = (P j).slotTurn (num j) := by
  have he : StubPairing.piecePorts P j = (P j).localDarts := by
    ext ⟨v,p⟩
    cases p <;> rfl
  unfold StubPairing.pieceTurn OpenPiece.slotTurn
  rw [he]

end PortGraph

namespace PlanarPatch.TrivalentTree

open PortGraph

variable {K V : Type*} {S : Type} {d : V → ℕ} {q : ℕ} (t : TrivalentTree K d q)
    (h : [] ∈ t.branchAddresses) (e : t.Stub ≃ S)

/-- The literal trivalent incidence piece with its boundary given original names. -/
def namedPiece : OpenPiece S where
  Vertex := t.Role
  Edge := t.InternalWire
  graph := t.internalGraph
  attach := t.attach h ∘ e.symm

private theorem namedPiece_localDarts (v : t.Role) (p : (t.namedPiece h e).Ports v) :
    (t.namedPiece h e).localDarts ⟨v,p⟩ = t.nameEnds e ((t.namedDartEquiv h e.symm v) p).val := by
  cases p with
  | inl p => rfl
  | inr p =>
    change Sum.inr p.val = Sum.inr (e (e.symm p.val))
    rw [e.apply_symm_apply]

/-- Turning to the successor of the numbered slot in the assembly is the
positive turn in the trivalent tree's named contour. -/
theorem slotTurn_eq_namedTurn :
    (t.namedPiece h e).slotTurn (t.namedSlotEquiv h e.symm) = t.namedTurn h e := by
  ext a
  obtain ⟨⟨v,p⟩,rfl⟩ := (t.namedPiece h e).localDarts.surjective a
  obtain ⟨i,rfl⟩ := (t.namedSlotEquiv h e.symm v).symm.surjective p
  let n : (v : (t.namedPiece h e).Vertex) → (t.namedPiece h e).Ports v ≃ Fin 3 :=
    t.namedSlotEquiv h e.symm
  change (t.namedPiece h e).slotTurn n ((t.namedPiece h e).localDarts ⟨v, (n v).symm i⟩) =
    t.namedTurn h e ((t.namedPiece h e).localDarts ⟨v, (n v).symm i⟩)
  rw [(t.namedPiece h e).slotTurn_port n v ((n v).symm i), Equiv.apply_symm_apply]
  rw [t.namedPiece_localDarts h e v ((n v).symm (finRotate _ i)),
    t.namedPiece_localDarts h e v ((n v).symm i), ← nameEnds_turn]
  exact congrArg (t.nameEnds e) (t.positiveTurn_namedSlot h e.symm v i).symm

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI

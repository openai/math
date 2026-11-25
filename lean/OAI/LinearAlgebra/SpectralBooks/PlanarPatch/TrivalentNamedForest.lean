import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentVertexCycles
import OAI.LinearAlgebra.SpectralBooks.PlanarSurgery.PlanarReturnWord
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyIncidence
import OAI.Geometry.HyperbolicGroups.PictureLeaf
import OAI.Geometry.HyperbolicGroups.IndexedFillingValue

/-! # First return of the actual tree forest in named dart coordinates

Turning at the vertices and crossing all the internal wires follows the disk
boundary. Reading the named stubs along this orbit gives the cyclic permutation
of the original boundary list.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

namespace PlanarPatch.TrivalentTree
open PlanarSurgery

variable {K V S : Type*} {d : V → ℕ} {q : ℕ} (t : TrivalentTree K d q)

abbrev NamedEnd (S : Type*) := (t.InternalWire × Bool) ⊕ S

/-- Name the boundary stubs, preserving both darts of each internal edge. -/
def nameEnds (e : t.Stub ≃ S) : t.TreeEnd ≃ t.NamedEnd S := Equiv.sumCongr (.refl _) e

variable (h : [] ∈ t.branchAddresses) (e : t.Stub ≃ S)

/-- The vertex rotation in the original boundary names. -/
def namedTurn : Perm (t.NamedEnd S) := (t.nameEnds e).permCongr (t.positiveTurn h)

/-- The internal forest involution in the names of the closed occurrence. -/
def namedMate (S : Type*) : Perm (t.NamedEnd S) := Equiv.sumCongr PortGraph.cross (Equiv.refl S)

theorem nameEnds_turn (a : t.TreeEnd) :
    t.nameEnds e (t.positiveTurn h a) = t.namedTurn h e (t.nameEnds e a) := by simp [namedTurn]

theorem nameEnds_mate (a : t.TreeEnd) :
    t.nameEnds e (t.internalPairing a) = t.namedMate S (t.nameEnds e a) := by
  rcases a with ⟨w,b⟩ | s <;> rfl

theorem nameEnds_diskTurn (a : t.TreeEnd) :
    t.nameEnds e (t.diskTurn h a) = (t.namedTurn h e * t.namedMate S) (t.nameEnds e a) := by
  rw [diskTurn, mul_apply, mul_apply, nameEnds_turn, nameEnds_mate]

/-- The tree disk visits all occurrence darts in a single orbit. -/
theorem sameCycle_namedContour (a b : t.NamedEnd S) :
    (t.namedTurn h e * t.namedMate S).SameCycle a b := by
  obtain ⟨a,rfl⟩ := (t.nameEnds e).surjective a
  obtain ⟨b,rfl⟩ := (t.nameEnds e).surjective b
  exact semiconj_perm_sameCycle (t.nameEnds_diskTurn h e)
    ((t.diskWalk_isBoundary h).sameCycle (t.diskWalk_all h a) (t.diskWalk_all h b))

/-- Every contour reaches a named boundary stub, including the root output stub. -/
theorem covers_namedContour : Covers (t.namedTurn h e * t.namedMate S) (.inr : S ↪ t.NamedEnd S) :=
  fun a => ⟨e none, t.sameCycle_namedContour h e a _⟩

private def readNamed (a : t.NamedEnd S) : Option S := Sum.elim (fun _ => none) some a

private theorem readNamed_partialInv :
    Function.IsPartialInv (.inr : S ↪ t.NamedEnd S) (t.readNamed (S := S)) := by
  rintro s (p | s')
  · simp [readNamed]
  · simp [readNamed, eq_comm]

private theorem namedWord (out : V) (nd : (out :: t.labels).Nodup)
    (all : ∀ v, v ∈ out :: t.labels) :
    (((t.diskWalk h).map (t.nameEnds (t.stubNames out nd all))).filterMap t.readNamed) =
      out :: t.labels := by
  rw [← t.diskWalk_namedStubs h out nd all, List.map_filterMap, List.filterMap_map]
  congr 1
  funext a
  cases a <;> rfl

/-- First return to the named boundary runs through the output and then the
ordered input names, including the closing step back to the output. -/
theorem onStubs_namedContour [Fintype V] [DecidableEq V] (out : V)
    (nd : (out :: t.labels).Nodup) (all : ∀ v, v ∈ out :: t.labels) :
    let names := t.stubNames out nd all
    onStubs (t.namedTurn h names * t.namedMate V) .inr (t.covers_namedContour h names) =
      (out :: t.labels).formPerm := by
  let e := t.stubNames out nd all
  have hw := (t.diskWalk_isBoundary h).map (t.nameEnds e) (t.nameEnds e).injective (t.nameEnds_diskTurn h e)
  have hr := onStubs_boundary_of_read _ _ (t.covers_namedContour h e)
    t.readNamed (t.readNamed_partialInv (S := V)) hw
  rw [show (((t.diskWalk h).map (t.nameEnds e)).filterMap t.readNamed) = out :: t.labels from
    t.namedWord h out nd all] at hr
  apply Equiv.ext
  exact fun v => hr.turn v (all v)

/-- Every internal edge merges two successive vertex cycles. The final contour
has one cycle and the edge pairing moves two darts per merge. -/
theorem namedForest_euler [Fintype S] :
    2 * (cycles (t.namedTurn h e) - cycles (t.namedTurn h e * t.namedMate S)) =
      ((t.namedMate S).support.card : ℤ) := by
  have ht := (cycles_equiv _ _ (t.nameEnds e) (t.nameEnds_turn h e)).symm.trans
    (t.cycles_positiveTurn h)
  have hdisk := (t.diskWalk_isBoundary h).cycles_eq_one (t.diskWalk_all h)
    (List.ne_nil_of_mem (t.diskWalk_all h (.inr none)))
  have hc := (cycles_equiv _ _ (t.nameEnds e) (t.nameEnds_diskTurn h e)).symm.trans hdisk
  have hs (a : t.TreeEnd) :
      a ∈ t.internalPairing.support ↔ t.nameEnds e a ∈ (t.namedMate S).support := by
    simp only [mem_support, ← nameEnds_mate]
    exact (not_congr (t.nameEnds e).injective.eq_iff).symm
  have hcard := Fintype.card_congr ((t.nameEnds e).subtypeEquiv hs)
  simp only [Fintype.card_coe] at hcard
  have hr := t.card_internalWire_add_one h
  have hi := t.internalPairing_support_card
  omega

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI

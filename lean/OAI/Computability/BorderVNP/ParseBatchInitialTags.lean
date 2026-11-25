import OAI.Computability.BorderVNP.ParseBatchUniversal
import OAI.Computability.BorderVNP.ParseBatchScalarExtension
import OAI.Computability.BorderVNP.DiagonalCellLeaves
import OAI.Computability.BorderVNP.DiagonalTallies

/-! # Initial power and Boolean events on the physical batched query network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open VPVNP VPVNP.VerifierNetwork MvPolynomial ParseBatch ParseBatchTrees
open Diagonal.CellEntries
open scoped Classical

variable {m g n r : ℕ} {Gadget E : Type*} [CommRing E]
variable (d : Fin n) (trees : Frame (BatchPins m g n r d) Unit)

private abbrev Param (m g n : ℕ) := GrammarLabel (Fin m × Bool) (Fin g) n

/-- The checker sees a single power event at each designated unary vertex, and
a Boolean check at every other vertex. The site and the supplying wire are
the actual incidences of the shared Boolean verifier network. -/
noncomputable def initialLeaf : (queryLayout d trees).network.Tables (Leaf (Param m g n) Gadget) :=
  fun v a x => if hw : ∃ j : WeightSites m g r d,
        BooleanLayout.weightSite (verifier d trees) weightedPin j = v then
    let j := hw.choose
    let edge := BooleanLayout.weightEdge (verifier d trees) weightedPin j
    have atSite : (queryLayout d trees).network.dst edge = v :=
      (BooleanLayout.weightEdge_dst ..).trans hw.choose_spec
    .power j.1 j.2.val (a ⟨edge, Or.inr atSite⟩ 0)
  else
    .check (decide ((queryLayout d trees).tables
      (BooleanLayout.factor (verifier d trees) unaryWeight) v a x = 1))

/-- At a weight site, the supplied bit selects its parameter and its exponent.
There is no scalar-gadget event in this original, uncompressed batch. -/
theorem initialLeaf_at_weight (j : WeightSites m g r d) (a x) :
    initialLeaf (Gadget := Gadget) d trees
      (BooleanLayout.weightSite (verifier d trees) weightedPin j) a x =
    .power j.1 j.2.val (a ⟨BooleanLayout.weightEdge (verifier d trees) weightedPin j,
      Or.inr (BooleanLayout.weightEdge_dst ..)⟩ 0) := by
  have hw : ∃ t : WeightSites m g r d, BooleanLayout.weightSite (verifier d trees) weightedPin t =
      BooleanLayout.weightSite (verifier d trees) weightedPin j := ⟨j,rfl⟩
  have hj : hw.choose = j := (BooleanLayout.weightSite (verifier d trees) weightedPin).injective hw.choose_spec
  simp only [initialLeaf, dite_eq_left hw, hj]
  congr 1
  apply congrArg (fun e => a e 0)
  exact Subtype.ext (congrArg (BooleanLayout.weightEdge (verifier d trees) weightedPin) hj)

/-- The initial table of multiplicative counter entries. -/
noncomputable def initialTags : (queryLayout d trees).network.Tables (Diagonal.CellEntries.Entry (Param m g n) Gadget) :=
  fun v a x => (initialLeaf d trees v a x).entry

/-- Each tagged local entry interprets as the corresponding integral polynomial
table entry, specialized to any coefficient ring. This also holds at failed checks. -/
theorem interpret_initialTags (val : Gadget → E) (v : (queryLayout d trees).Site) (a x) :
    interpret val (initialTags d trees v a x) =
      map (Int.castRingHom E) ((queryLayout d trees).tables
        (BooleanLayout.factor (verifier d trees) unaryWeight) v a x) := by
  by_cases hw : ∃ j : WeightSites m g r d, BooleanLayout.weightSite (verifier d trees) weightedPin j = v
  · obtain ⟨j,rfl⟩ := hw
    rw [initialTags, initialLeaf_at_weight, Leaf.entry, interpret_unary, BooleanLayout.weight_table]
    cases a ⟨BooleanLayout.weightEdge (verifier d trees) weightedPin j,
      Or.inr (BooleanLayout.weightEdge_dst ..)⟩ 0 <;> simp [unaryWeight]
  · have hbool := BooleanLayout.other_tables_zero_one (verifier d trees) weightedPin
      unaryWeight v (fun j he => hw ⟨j,he.symm⟩) a x
    rcases hbool with h | h <;> simp [initialTags, initialLeaf, hw, h, Leaf.entry]

/-- Interpretation commutes with the whole physical contraction. Every passing
internal assignment contributes its original integral monomial after scalar extension. -/
theorem initialTags_contraction (val : Gadget → E) (x : Fin r → Fin m → Bool) :
    (queryLayout d trees).network.value (fun v a p => interpret val (initialTags d trees v a p))
      (fun ij _ => x ij.1 ij.2) =
    map (Int.castRingHom E) ((queryLayout d trees).network.value
      ((queryLayout d trees).tables (BooleanLayout.factor (verifier d trees) unaryWeight))
      (fun ij _ => x ij.1 ij.2)) := by
  simp_rw [interpret_initialTags]
  exact Crossing.Network.value_mapTables _ _ _ _

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI

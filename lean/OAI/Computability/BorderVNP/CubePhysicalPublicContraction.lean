import OAI.Computability.BorderVNP.CubePhysicalPaddingPublic
import OAI.Computability.BorderVNP.CubePhysicalDeclarationBudget
import OAI.Computability.BorderVNP.CubePhysicalTally

/-! # Publicly selected layouts and physical path tallies

The layout uses the actual conditional-moment cell-label scan and cable-order
offsets, at the rounded common capacity. A single fixed table is used in every
packet and every profile; the resulting path sum preserves formal parameters.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal Diagonal.CellEntries MvPolynomial
open scoped Classical

set_option synthInstance.maxSize 768

variable {n d m b h K s D B : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell] {A : Type} [Fintype A] [DecidableEq A]
variable {Team Param Gadget E : Type*} [Fintype Team] [Fintype Param] [Fintype Gadget] [Field E]

/-- For a real packed network satisfying Lemma 8.2's numerical hypotheses,
the public wire intervals, cell labels and selected coordinate give the
team-owned path expansion with no free choice of an embedding or a label.
The tag addresses may identify equal table entries, while the counts preserve
every selected position with its prescribed address. -/
theorem public_value_eq_tallied_paths (N : Network D P bits) (cell : N.Site → Cell) [DecidableEq N.Edge]
    (recv : A → Cell) (dataWidth : A → ℕ) (ord : N.CrossingEdge cell ≃ Fin m)
    (cs : List Cell) (hcs : cs.toFinset = Finset.univ) (hd : 0 < d) (hb : 0 < h*b)
    {W : ℝ} {M : ℕ} (budget : PackedLabelBudget N cell recv dataWidth W M (d^(n+1)))
    (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (pos : TableEntry n b h K s → Gadget) (values : Gadget → E) (valid : ValidTables (values ∘ pos))
    (words : PowerWords Team Param Gadget B N tags) (team : Fin d → Team) :
    let slot := publicPackedEmbedding N cell recv dataWidth ord cs hcs n d hd hb budget
    let label := publicPackedLabel N cell recv dataWidth cs n d hd
    let record := pathTag N cell slot tags x (fun _ => pos)
    let tally := pathTally slot tags x (fun _ => pos) words label team
    N.value (fun v r p => interpret values (tags v r p)) x =
      ∑ a ∈ Finset.univ.filter (fun a => record a ≠ 0), monomial (tally a).exponents ((tally a).coefficient values) := by
  intro slot label record tally
  exact value_eq_enumerated_tallies slot tags x (fun _ => pos) words label team values (fun _ => valid)
    inferInstance inferInstance

/-- All fields admit fixed physical cube tables at arbitrarily large block
widths, with the actual least-minimizing declaration satisfying (8.1) for
every selector path and every positive product alphabet. -/
theorem exists_physical_tables (E : Type*) [Field E] (n B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ b h K s : ℕ, B ≤ h*b ∧ 0 < h*b ∧ 1 ≤ K ∧
      ∃ table : TableEntry n b h K s → E, ValidTables table ∧
        ∀ d blocks : ℕ, 0 < d → ∀ select : Packet n d blocks → Selector n K h,
          (cutWidth b s select (chosen b s select) : ℝ) +
            ∑ _p : Packet n d blocks,
              (VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤
            padded n d blocks (h*b) * (2/Real.sqrt (n+1) + (n+1)/d + η) := by
  obtain ⟨b, h, K, s, hB, hb, hK, hid, hbudget⟩ := exists_identity_with_chosen_budget E n B η hη
  obtain ⟨table, htable⟩ := exists_validTables_iff.mpr hid
  exact ⟨b, h, K, s, hB, hb, hK, table, htable, hbudget⟩

end Cube.Physical

end BorderVNP
end Computability
end OAI

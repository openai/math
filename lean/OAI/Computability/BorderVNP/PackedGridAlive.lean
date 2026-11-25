import OAI.Computability.BorderVNP.PackedGridOwnerBank

/-! # Exact survival criterion for private Boolean and unary seed-grid factors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse Diagonal.CellEntries ParseBatch VPVNP.BooleanTranscript
open scoped Classical
variable {D : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}

/-- The Boolean gate check of a sparse verifier factor. A polynomial unary
contributes a monomial on either physical bit. -/
def Rule.base {v : N.Site} : Rule N v → (CellBox.Lane N v → Bool) → Bool
  | .truth f, read => f read
  | .unary _ _, _ => true

/-- Report consistency of a sparse factor, separated from the ordinary gate test. -/
def Rule.reportOK {v : N.Site} : Rule N v → (CellBox.Lane N v → Bool) → (Port → Bool) → Bool
  | .truth _, _, _ => true
  | .unary l p, read, use => read l == use p

/-- A physical sparse check passes precisely when the gate and report tests pass. -/
theorem Rule.passes_iff {v : N.Site} (r : Rule N v) (read use) :
    r.passes read use = true ↔ r.base read = true ∧ r.reportOK read use = true := by
  cases r <;> simp [Rule.passes,Rule.base,Rule.reportOK]

/-- The verifier's tagged polynomial entry survives exactly the original Boolean
base test. A selected or unselected parameter unary always survives. -/
theorem verifier_alive {X W Param Gadget : Type} [Fintype X] [Fintype W] [Fintype Param] {s b : ℕ}
    (c : Circuit (X ⊕ W) s) (weighted : Param × Fin b → W) (report : Param × Fin b → Port)
    (v : (BooleanLayout.layout c weighted).Site) (read : CellBox.Lane (BooleanLayout.layout c weighted).network v → Bool) :
    CellBox.localRow (BooleanLayout.layout c weighted).network (BooleanLayout.powerTags (Gadget := Gadget) c weighted) v read ≠ 0 ↔
      (verifierRule c weighted BooleanLayout.powerWeight report v).base read = true := by
  by_cases h : ∃ j, BooleanLayout.weightSite c weighted j = v
  · simp only [CellBox.localRow,BooleanLayout.powerTags,verifierRule,h,dite_true,Rule.base]
    unfold unary
    split <;> simp [passed]
  · simp only [CellBox.localRow,BooleanLayout.powerTags,verifierRule,h,dite_false,Rule.base]
    split <;> simp_all

variable {Param Gadget : Type*} (routes : N.WireRoutes)
    (tags : N.Tables (Entry Param Gadget)) (rules : ∀ v, Rule N v)

/-- Replacing each edge by equality hops preserves the base survival test and
gives the physical equality test at every newly inserted vertex. -/
theorem routed_alive (h : ∀ v read, CellBox.localRow N tags v read ≠ 0 ↔ (rules v).base read = true)
    (v : (N.subdivide routes).Site) (read : CellBox.Lane (N.subdivide routes) v → Bool) :
    CellBox.localRow (N.subdivide routes) (N.subdivideTables routes tags) v read ≠ 0 ↔
      (routedRule N routes rules v).base read = true := by
  rcases v with old | hop
  · rw [routed_local_row N routes tags old read,h]
    cases hr : rules old <;> simp [routedRule,hr,Rule.base]
  · dsimp only [CellBox.localRow,Network.subdivideTables,routedRule,Rule.base]
    rw [decide_eq_true_eq,← funext_iff]
    split <;> simp_all <;> assumption

/-- Pointwise truth tables for the gates alone and for their auxiliary report comparisons. -/
def baseTable : N.Tables Bool := fun v a x => (rules v).base (readLane v a x)

/-- Report comparison on the original physically selected bit, independent of the
Boolean part of a verifier site's check. -/
def reportTable (use : Port → Bool) : N.Tables Bool := fun v a x => (rules v).reportOK (readLane v a x) use

variable {Cell Q : Type} [Fintype Cell] [DecidableEq Cell] [Fintype Q]
    (cell : N.Site → Cell) (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (hidden : ∀ i, N.InsideAssignment cell i) {src dst : Q → Cell} {H : ℕ}
    (packing : (N.cellNetwork cell position).ChannelPacking src dst H)

/-- Read a fine factor inside a specified cell of the padded grid, on the chosen
private words and the genuinely supplied external cable subwords. -/
noncomputable def cellRead {A : Type*} (table : N.Tables A) (c : Cell) (v : {v : N.Site // cell v = c})
    (a : {q : Q // src q = c ∨ dst q = c} → Fin H → Bool)
    (x : ∀ p : {p : P // cell (N.attach p) = c}, Fin (bits p.val) → Bool) : A :=
  fineFactor cell table c (hidden c) v (fun e i => publicWords cell position packing c a x (.inl e) i) x

/-- On a chosen hidden assignment, the grid tag survives exactly when padding is
zero and every Boolean base guard in the cell passes. -/
theorem cell_alive (h : ∀ v read, CellBox.localRow N tags v read ≠ 0 ↔ (rules v).base read = true) (c a x) :
    conditionedGridTags cell position packing tags hidden c a x ≠ 0 ↔
      padOK packing c a x ∧ ∀ v, cellRead cell position hidden packing (baseTable rules) c v a x = true := by
  by_cases hp : padOK packing c a x
  · simp only [conditionedGridTags,paddedFactor,hp,ite_true,true_and,unpackFactor,conditionedCellTags]
    rw [Finset.prod_ne_zero_iff]
    simp only [Finset.mem_univ,true_implies]
    apply forall_congr'
    intro v
    exact h v.val (readLane v.val _ _)
  · simp [conditionedGridTags,paddedFactor,hp]

omit [Fintype Q] in
/-- When all live report comparisons agree with their designated unary bit,
the full sparse checks coincide exactly with the gate tests. -/
theorem cell_checks (use : Port → Bool) (c a x)
    (h : ∀ v, cellRead cell position hidden packing (reportTable rules use) c v a x = true) :
    (∀ v, cellRead cell position hidden packing (guard rules use) c v a x = true) ↔
      ∀ v, cellRead cell position hidden packing (baseTable rules) c v a x = true := by
  apply forall_congr'
  intro v
  exact (Rule.passes_iff (rules v.val) _ use).trans (and_iff_left (h v))

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI

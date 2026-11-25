import OAI.LinearAlgebra.SpectralBooks.WireTransport
import OAI.ThreeFlat.CrossingBudget
import OAI.LinearAlgebra.SpectralBooks.WireIdentity

namespace OAI
/-! # Routing the remainder after repeating a crossing tile

The unused part of each crossed wire is carried on its original pair of sites.
The horizontal remainder passes through site zero, which contracts its two
ends against the identity there. All other slack edges may be discarded.
-/

noncomputable section

namespace ThreeFlat.CrossingSupply

open LinearAlgebra.SpectralBooks
open ChordGraph SiteTensor

/-- The two crossed wires, each of width `t`. -/
def crossWires (t : ℕ) : Widths 6 :=
  wire 0 2 (by decide) t + wire 1 3 (by decide) t

/-- The crossing and its horizontal catalyst at physical width `t`. -/
def crossDemand (t R : ℕ) : Widths 6 :=
  crossWires t + wire 4 5 (by decide) (t*R)

/-- A remainder uses only the per-pair slack and the prescribed horizontal bits. -/
def remainderSupply (t R : ℕ) : Widths 6 :=
  slack t + arms 0 (t*R) (t*R)

/-- Adding the leftover wires to the repeated cleared-denominator demand
reconstructs the crossing with its original integer width exactly. -/
theorem repeat_demand_add (q R b t r : ℕ) :
    t • (b • demand q R) + crossDemand r R = crossDemand (4*q*b*t+r) R := by
  have scale (w : ℕ) : crossDemand w R = w • crossDemand 1 R := by
    simp [crossDemand, crossWires, wire, smul_add, Finsupp.smul_single]
  change t • (b • crossDemand (4*q) R) + crossDemand r R = _
  rw [scale (4*q), scale r, scale (4*q*b*t+r), smul_smul, smul_smul, ← add_smul]
  congr 1
  ring

/-- A single binary identity from 4 to 5 is obtained by transmitting the
first index from site zero to site four. -/
private theorem binaryWire_le_via_zero (F : Type*) [Field F] :
    ChordGraph.wire F (edge 4 5 (by decide) : Chord 6) ≤
      ChordGraph.wire F (edge 0 4 (by decide)) * ChordGraph.wire F (edge 0 5 (by decide)) := by
  let T := Raw.diagonal (Fin 2) F (Fin 2)
  let p : Fin 2 → Fin 6 := ![0,5]
  let q : Fin 2 → Fin 6 := ![4,5]
  have move := Raw.move_restricts_with_wire T p q 0 (by
    intro i hi
    fin_cases i <;> first | rfl | exact (hi rfl).elim)
  have hc := ofRaw_le_iff.mpr move
  rw [ofRaw_mul] at hc
  rw [mul_comm]
  exact hc

theorem graphClass_crossDemand_le (F : Type*) [Field F] (r R : ℕ) :
    graphClass F (crossDemand r R) ≤ graphClass F (remainderSupply r R) := by
  let unused := wire 0 1 (by decide) r + wire 0 3 (by decide) r +
    wire 1 2 (by decide) r + wire 2 3 (by decide) r
  have hslack : slack r = crossWires r + unused := by
    let a := wire 0 1 (by decide) r
    let b := wire 0 2 (by decide) r
    let c := wire 0 3 (by decide) r
    let d := wire 1 2 (by decide) r
    let e := wire 1 3 (by decide) r
    let f := wire 2 3 (by decide) r
    change a+b+c+d+e+f = b+e+(a+c+d+f)
    ac_rfl
  have vertical : graphClass F (crossWires r) ≤ graphClass F (slack r) := by
    rw [hslack, graphClass_add]
    simpa only [mul_one] using
      mul_mono (le_refl (graphClass F (crossWires r)))
        (SiteTensor.one_le_of_ne_zero (graphClass_ne_zero F unused))
  have horizontal : graphClass F (wire 4 5 (by decide) (r*R)) ≤
      graphClass F (arms 0 (r*R) (r*R)) := by
    simp only [arms, wire, graphClass_add, graphClass_single]
    rw [← mul_pow]
    exact pow_le_pow_left' (binaryWire_le_via_zero F) _
  exact (graphClass_add F _ _).le.trans
    ((mul_mono vertical horizontal).trans_eq (graphClass_add F _ _).symm)

/-- A local linear restriction proving the coefficient identity of the
remainder network at every width, including width zero. -/
theorem remainder_restricts (F : Type*) [Field F] (r R : ℕ) :
    (raw F (crossDemand r R)).Restricts (raw F (remainderSupply r R)) := by
  apply ofRaw_le_iff.mp
  simpa only [ofRaw_raw] using graphClass_crossDemand_le F r R

@[simp] theorem arms_load_four (i : Fin 4) (u v : ℕ) : load 4 (arms i u v) = u := by
  have h4 : (4 : Fin 6) ≠ site i := Ne.symm (ne_of_lt (show site i < 4 from i.isLt))
  simp [arms, h4]

@[simp] theorem arms_load_five (i : Fin 4) (u v : ℕ) : load 5 (arms i u v) = v := by
  have h5 : (5 : Fin 6) ≠ site i :=
    Ne.symm (ne_of_lt ((show site i < 4 from i.isLt).trans (show (4 : Fin 6) < 5 by decide)))
  simp [arms, h5]

@[simp] theorem remainder_load_four (t R : ℕ) :
    load 4 (remainderSupply t R) = t*R := by
  norm_num [remainderSupply, slack, arms, site]

@[simp] theorem remainder_load_five (t R : ℕ) :
    load 5 (remainderSupply t R) = t*R := by
  norm_num [remainderSupply, slack, arms, site]

/-- The two linear maps on the horizontal memory in a budgeted crossing
restriction have the same input and output dimension. -/
theorem crossing_endpoint_cards (w R u v a : ℕ) (H : Widths 6)
    (h4 : load 4 H = w*R) (h5 : load 5 H = w*R) :
    let g := matching true u + matching false v + slack a + H
    Fintype.card (State (crossDemand w R) 4) = Fintype.card (State g 4) ∧
      Fintype.card (State (crossDemand w R) 5) = Fintype.card (State g 5) := by
  dsimp only
  have l4 : load 4 (matching true u + matching false v + slack a + H) = w*R := by
    rw [map_add, side_load 4 le_rfl, zero_add, h4]
  have l5 : load 5 (matching true u + matching false v + slack a + H) = w*R := by
    rw [map_add, side_load 5 (by decide), zero_add, h5]
  simp only [card_state, l4, l5]
  norm_num [crossDemand, crossWires]

end ThreeFlat.CrossingSupply

end
end OAI

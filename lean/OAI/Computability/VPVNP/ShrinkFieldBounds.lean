import OAI.Computability.VPVNP.ShrinkConversion
import OAI.Computability.VPVNP.ShrinkPayload
import OAI.Computability.VPVNP.ShrinkRoles

/-!
# Widths and local map descriptions in the shrinking step

With a fixed six-party conversion block, every supply width (including its
selectors), outer coordinate, and matrix-entry degree is linear in the
maximum old width plus one. At each packed site each of the six parties has
exactly `dQ` resident maps and each of the four absorbed types has `dQ`
resident fields. The resulting local bounds depend only on the block and
degree, allowing different widths and different selections on every lane.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open WireTensor MotifGrid MotifBlocks MotifConversion MotifSelector MotifDemandPadding
open SurvivingSlots

namespace ShrinkMotif

variable {k : Type*} [Field k] {H' : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) H')

/-- If the conversion index bound is `A`, the supply payload and its selector
list together have width at most `A * (1 + selectorBits) * (W + 1)`. -/
noncomputable def fieldFactor : ℕ :=
  (linear_index_bound B supplyMass_pos).choose * (1 + B.selectorBits)

theorem linear_field_bounds (W : ℕ) (u : Bool → ℕ) (hu : ∀ e, u e ≤ W) :
    repetitions B u ≤ fieldFactor B * (W + 1) ∧ ∀ v ∈ outerIndices B u, ∀ e,
      v e ≤ fieldFactor B * (W + 1) ∧ supplyWidths B u v e ≤ fieldFactor B * (W + 1) := by
  let A := (linear_index_bound B supplyMass_pos).choose
  obtain ⟨hr,hv⟩ := (linear_index_bound B supplyMass_pos).choose_spec W u hu
  have hA : A * (W + 1) ≤ fieldFactor B * (W + 1) := by
    unfold fieldFactor
    apply Nat.mul_le_mul_right
    exact Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨hr.trans hA, fun v hm e ↦ ⟨(hv v hm e).trans hA, ?_⟩⟩
  calc
    supplyWidths B u v e ≤ A * (W + 1) + (A * (W + 1)) * B.selectorBits :=
      Nat.add_le_add (hv v hm e) (Nat.mul_le_mul_right _ hr)
    _ = fieldFactor B * (W + 1) := by change _ = (A * (1 + B.selectorBits)) * _; ring

end ShrinkMotif

namespace PackingData

open ShrinkMotif

variable {V H Tag L : Type} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c) (hc : 2 ≤ c) (hd : 0 < d)
variable (number : P.BundleNumbering) (w : Arc V H Tag L d c → ℕ) {W : ℕ}
variable (hw : ∀ a, w a ≤ W)

include hc hd hw

/-- Dividing the thick bundle among its assigned demands keeps even the
AB demand within the maximum old width. The CD demand uses its old wire. -/
theorem shrinkDemandWidths_le (m : P.Motif) (e : Bool) :
    P.shrinkDemandWidths number w m e ≤ W := by
  cases e
  · exact P.abWidth_le hc hd number w hw m
  · exact hw m.val

variable {k : Type*} [Field k] {H' : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) H')

/-- For each admitted term, bound the number of base entries in a map, its
outer coordinates and all eight supply fields with one block constant. -/
theorem shrinkTerm_bounds (m : P.Motif) (i : P.ShrinkChoice number w B m) :
    repetitions B (P.shrinkDemandWidths number w m) ≤ fieldFactor B * (W + 1) ∧
      ∀ e, i.val e ≤ fieldFactor B * (W + 1) ∧
        P.shrinkSupplyWidths number w B m i e ≤ fieldFactor B * (W + 1) := by
  have h := linear_field_bounds B W _ (P.shrinkDemandWidths_le hc hd number w hw m)
  exact ⟨h.1, h.2 _ i.property⟩

/-- The scalar-independent polynomial specified by each local matrix entry
is zero or a monomial with at most the stated total exponent. -/
theorem shrinkEntry_degree_le (m : P.Motif) (i : P.ShrinkChoice number w B m) (j : Fin 6)
    (x : HalfBits demandSource demandTarget (P.shrinkDemandWidths number w m) j)
    (y : HalfBits supply.src supply.dst (P.shrinkSupplyWidths number w B m i) j) :
    let poly := P.shrinkMap number w B (MvPolynomial.X (R := ℤ)) m i j x y
    (poly = 0 ∨ ∃ f, poly = MvPolynomial.monomial f 1) ∧
      poly.totalDegree ≤ fieldFactor B * (W + 1) := by
  obtain ⟨h, hdeg⟩ := entry_monomial B demandMass_pos _ i.val j x y
  exact ⟨h,hdeg.trans (P.shrinkTerm_bounds hc hd number w hw B m i).1⟩

omit hc hd hw

private theorem splitWidth_le_width (b q : ℕ) (i : Fin q) :
    splitWidth b q i ≤ b := by
  have h := Finset.single_le_sum (f := splitWidth b q) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)
  simpa only [sum_splitWidth b q (Nat.zero_lt_of_lt i.isLt)] using h

include hc hd hw

/-- The bound holds on the actual slots, including the dummy arcs, for any
list of admitted motif terms and either layout. -/
theorem shrinkSlotWidth_le (sel : ∀ m, P.ShrinkChoice number w B m)
    (l : Bool) (subdiv : Fin 4 → ℕ) {pad d' : ℕ}
    (outgoing : PaddedId (V × Tag) (Id P.BaseMotif subdiv) pad ≃ (V × Tag) × Fin d')
    (a : ((V × Tag) × Fin d') × L) :
    P.shrinkSlotWidth l subdiv (fun m t ↦ P.shrinkSupplyWidths number w B m (sel m) (l,t))
      outgoing a ≤ fieldFactor B * (W + 1) := by
  unfold shrinkSlotWidth
  cases (P.shrinkArcEquiv l subdiv outgoing).symm ((a.1.1,a.2),a.1.2) with
  | inl i =>
    exact (splitWidth_le_width ..).trans
      ((P.shrinkTerm_bounds hc hd number w hw B i.2.1 (sel i.2.1)).2 (l,i.1)).2
  | inr _ => exact Nat.zero_le _

omit hd hw

private theorem card_placed_roles {T : Type} [Fintype T] (l : Bool) (pick : T → PackedRole)
    (s : (V × Tag) × L) :
    Fintype.card {x : P.Motif × T // packedSiteEquiv (P.survivingRole l (pick x.2) x.1) = s} =
      Fintype.card T * (d * pieceCount d c) := by
  classical
  let e : {x : P.Motif × T // packedSiteEquiv (P.survivingRole l (pick x.2) x.1) = s} ≃
      Σ t : T, {m : P.Motif // P.survivingRole l (pick t) m = packedSiteEquiv.symm s} := {
    toFun x := ⟨x.1.2,x.1.1, packedSiteEquiv.injective (x.2.trans
      (packedSiteEquiv.apply_symm_apply s).symm)⟩
    invFun z := ⟨(z.2.1,z.1), by rw [z.2.2, Equiv.apply_symm_apply]⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have count (r : PackedRole) : Fintype.card {m : P.Motif //
      P.survivingRole l r m = packedSiteEquiv.symm s} = d * pieceCount d c := by
    cases r with
    | a => exact P.card_roleA hc _
    | b => exact P.card_roleB hc _
    | d => exact P.card_roleD hc l _
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp [count]

/-- The resident map records include a separate occurrence of each party,
even when several parties of one motif are assigned to the same site. -/
theorem card_shrinkPartySite (l : Bool) (s : (V × Tag) × L) :
    Fintype.card {x : P.Motif × Fin 6 // P.shrinkPartySite l x.1 x.2 = s} =
      6 * (d * pieceCount d c) := by
  exact (Fintype.card_congr (Equiv.refl _)).trans
    ((P.card_placed_roles hc l (partyRole l) s).trans (by rw [Fintype.card_fin]))

/-- Every absorbed wire is recorded at its common owner exactly once. -/
theorem card_shrinkInternalOwner (l : Bool) (s : (V × Tag) × L) :
    Fintype.card {e : P.Motif × Fin 4 // P.shrinkInternalOwner l e = s} =
      4 * (d * pieceCount d c) := by
  exact (Fintype.card_congr (Equiv.refl _)).trans
    ((P.card_placed_roles hc l (internalRole l) s).trans (by rw [Fintype.card_fin]))

include hd hw

/-- Total length of the parameter lists of all resident maps before their
product is evaluated. Failed entry checks require no additional entries. -/
theorem shrinkSite_repetitions_le (l : Bool) (s : (V × Tag) × L) :
    (∑ z : {x : P.Motif × Fin 6 // P.shrinkPartySite l x.1 x.2 = s},
      repetitions B (P.shrinkDemandWidths number w z.1.1)) ≤
      (6 * (d * pieceCount d c) * fieldFactor B) * (W + 1) := by
  classical
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun z : {x : P.Motif × Fin 6 // P.shrinkPartySite l x.1 x.2 = s} ↦ fun _ ↦
      (linear_field_bounds B W _ (P.shrinkDemandWidths_le hc hd number w hw z.1.1)).1)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
    P.card_shrinkPartySite hc, Nat.mul_assoc] using h

/-- Total width of all the fields summed inside one packed site. -/
theorem shrinkSite_internalWidth_le (sel : ∀ m, P.ShrinkChoice number w B m)
    (l : Bool) (s : (V × Tag) × L) :
    (∑ z : {e : P.Motif × Fin 4 // P.shrinkInternalOwner l e = s},
      P.shrinkSupplyWidths number w B z.1.1 (sel z.1.1) (!l,z.1.2)) ≤
      (4 * (d * pieceCount d c) * fieldFactor B) * (W + 1) := by
  classical
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun z : {e : P.Motif × Fin 4 // P.shrinkInternalOwner l e = s} ↦ fun _ ↦
      ((P.shrinkTerm_bounds hc hd number w hw B z.1.1 (sel z.1.1)).2 (!l,z.1.2)).2)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
    P.card_shrinkInternalOwner hc, Nat.mul_assoc] using h

end PackingData

end Compression

end VPVNP
end Computability
end OAI

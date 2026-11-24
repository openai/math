import OAI.Computability.VPVNP.PackedSubdivision
import OAI.Computability.VPVNP.ShrinkMotif
import OAI.Computability.VPVNP.ShrinkPayload

/-!
# Quadratic energy bound for the actual shrinking step

The degree threshold in Section 7.2 works for every packed graph with the
same old degree and number of color bits. Each list of admitted six-party
terms determines a single layout. With the paper's floor subdivisions, the
energy of its numbered outgoing arcs (including the zero-width dummies)
satisfies equation (7.2), with a constant independent of the old widths and
of the number of positions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.ShrinkMotif

/-- Parallel slots assigned to each of the four surviving supply types. -/
noncomputable def subdivisions (d c d' : ℕ) (e : Fin 4) : ℕ :=
  SlotSubdivision.count (2 ^ c * d) d d' (relativeMass e)

/-- The same integral subdivision profile is used on all motifs and all lanes. -/
structure Ready (d c d' : ℕ) (δ : ℝ) : Prop where
  degree_pos : 0 < d'
  count_pos : ∀ e, 0 < subdivisions d c d' e
  degree_budget : d * PackingData.pieceCount d c * ∑ e, subdivisions d c d' e ≤ d'
  mass : ∀ {p p' : ℝ}, 0 < p → p' = p * ((2 ^ c * d : ℕ) * (d : ℝ)) / d' →
    ∀ e, (1 - δ) * p * relativeMass e ≤ (subdivisions d c d' e : ℝ) * p'

/-- In particular, all sufficiently large power-of-two degrees can be used. -/
theorem eventually_ready (d c : ℕ) (hd : 0 < d) (hc : 2 ≤ c) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1) : ∃ N : ℕ, ∀ d' ≥ N, Ready d c d' δ := by
  let q := fun e ↦ (relativeMass e : ℝ)
  have hq e : 0 < q e := Rat.cast_pos.mpr (relativeMass_pos e)
  obtain ⟨N, hN⟩ := SlotSubdivision.eventually_represented q hq
    (Nat.mul_pos (pow_pos (by decide : 0 < 2) c) hd) hd hδ hδ'
  refine ⟨N, fun d' hd' ↦ ?_⟩
  obtain ⟨hdegree, hm⟩ := hN d' hd'
  refine ⟨hdegree, fun e ↦ (hm 1 _ zero_lt_one rfl e).1,
    PackingData.packed_degree_budget q (fun e ↦ (hq e).le) sum_relativeMass hc hd d', ?_⟩
  exact fun hp hmass e ↦ (hm _ _ hp hmass e).2

/-- Strict contraction of the leading term under the chosen loss allowance. -/
theorem shrinkFactor_lt_one {δ H' : ℝ} (hδ : δ < 1) (hgap : H' < 2 * (1 - δ)) :
    H' / (2 * (1 - δ)) < 1 := by
  rwa [div_lt_one (mul_pos (by norm_num) (sub_pos.mpr hδ))]

end Compression.ShrinkMotif

namespace Compression.PackingData

open MotifGrid MotifBlocks MotifConversion ShrinkMotif ShrinkEnergy SurvivingSlots

variable {V H Tag L : Type} {d c d' : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable {k : Type*} [Field k] {factor δ : ℝ}
variable (P : PackingData V H Tag L d c)
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (number : P.BundleNumbering) (old : Arc V H Tag L d c → ℕ)
variable (choice : ∀ m : P.Motif,
  ↥(outerIndices B (demandWidths (P.abWidth number old m) (old m.val))))

/-- All eight supply widths at each occurrence, for the selected term list. -/
noncomputable def termWidths (m : P.Motif) (l : Bool) (e : Fin 4) : ℕ :=
  supplyWidths B (demandWidths (P.abWidth number old m) (old m.val)) (choice m).val (l,e)

/-- The energy of the genuine, subdivided arc identifiers before reindexing. -/
theorem packed_energy_from_terms [Nonempty V] (hc : 2 ≤ c) (hd : 0 < d)
    (ready : Ready d c d' δ) (hδ : δ < 1) (hfactor : 0 ≤ factor) :
    let p := equalArcMass (Position V H Tag L c) d
    let p' := equalArcMass (Site V Tag L) d'
    let w := P.termWidths B number old choice
    let l := chosenLayout p (fun e ↦ (relativeMass e : ℝ)) w
    let m := subdivisions d c d'
    (∑ i : Id P.Motif m, (slotWidth m w l i : ℝ) ^ 2 / p') ≤
      factor / (2 * (1 - δ)) * (∑ a, (old a : ℝ) ^ 2 / p) +
        roundingConstant d d' (pieceCount d c) factor B.energyConstant (1 - δ) m *
          (Fintype.card (Position V H Tag L c) : ℝ) ^ 2 := by
  apply P.packed_energy_le hc hd ready.degree_pos number old _ _ _ (sub_pos.mpr hδ) hfactor
    (fun e ↦ Rat.cast_pos.mpr (relativeMass_pos e)) ready.count_pos
  · apply ready.mass _ (P.equalArcMass_packed hd d')
    exact one_div_pos.mpr (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr hd))
  · exact fun m ↦ term_energy_le B _ _ (choice m).property

/-- Equation (7.2) on the numbered outgoing arcs of the graph passed to the
next compressor step. Dummy arcs carry zero payload at every remaining lane. -/
theorem shrinkSlotWidth_energy_le [Nonempty V] (hc : 2 ≤ c) (hd : 0 < d)
    (ready : Ready d c d' δ) (hδ : δ < 1) (hfactor : 0 ≤ factor)
    {pad : ℕ} (outgoing : PaddedId (V × Tag) (Id P.BaseMotif (subdivisions d c d')) pad ≃
      (V × Tag) × Fin d') :
    let p := equalArcMass (Position V H Tag L c) d
    let p' := equalArcMass (Site V Tag L) d'
    let w := P.termWidths B number old choice
    let l := chosenLayout p (fun e ↦ (relativeMass e : ℝ)) w
    let m := subdivisions d c d'
    let width := P.shrinkSlotWidth l m (fun a t ↦ w a l t) outgoing
    (∑ a : ((V × Tag) × L) × Fin d', (width ((a.1.1,a.2),a.1.2) : ℝ) ^ 2 / p') ≤
      factor / (2 * (1 - δ)) * (∑ a, (old a : ℝ) ^ 2 / p) +
        roundingConstant d d' (pieceCount d c) factor B.energyConstant (1 - δ) m *
          (Fintype.card (Position V H Tag L c) : ℝ) ^ 2 := by
  intro p p' w l m width
  exact (P.sum_shrinkSlotWidth l m (fun a t ↦ w a l t) outgoing
    (fun n ↦ (n : ℝ) ^ 2 / p') (by simp)).trans_le
    (P.packed_energy_from_terms B number old choice hc hd ready hδ hfactor)

end Compression.PackingData

end VPVNP
end Computability
end OAI

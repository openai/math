import OAI.Computability.VPVNP.StatePassHistory
import OAI.Computability.VPVNP.DegreeRefreshPass

/-!
# Local records of a degree refresh

Each physical port keeps exactly one old vertex. Its kernel checks the two
diagonal segment equalities and evaluates one expander-motif entry. The demand
arguments read the old half-wires and the two lists of external segments. The
supply arguments use the two directions of the inner expander slots. The
remaining slot fields, including the external and padding wires, are recorded
by the common pass constructor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Refresh

open NetworkKernel SpectralGeometry DegreeRefresh MotifConversion
open scoped Classical

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (X : State a (a + g)) (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
variable {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R) (hκ : (parameterData F).IsSolution κ)

/-- Identify old sites with physical ports in the dyadic refresh. -/
private def placedPort : X.network.Site ≃ (X.Base × Fin (2 ^ a)) × BitWord g :=
  ((Equiv.refl X.Base).prodCongr (splitBitWord a g).toEquiv).trans (refreshPositions (bitWordFinEquiv a))

/-- The actual outgoing and incoming segment widths at the indicated port. -/
private def segmentWidth (s : X.Base × BitWord g) (j : Fin (2 ^ a)) (dir : Bool) (l : Fin (2 ^ a)) : ℕ :=
  let arc := ((s, j), l)
  groupedWidths (bitWordFinEquiv a) (splitWidths X)
    (if dir then (oldPortMatching (splitSlots X) (bitWordFinEquiv a)).symm arc else arc)

/-- Local views used by the refresh map. `Fin 3` distinguishes the motif map
from the two diagonal equality checks, whose scalar degree is zero. -/
noncomputable def refreshLocalRecords :
    (dyadicRefreshPass X P hdH hconn F hD hd κ hκ).Records := fun choice v =>
  let s := (v.1.1, v.2)
  { Map := Fin 3
    mapFintype := inferInstance
    degree j := if j = 0 then repetitions F (blockDemandWidths (splitSlots X)
        (bitWordFinEquiv a) (splitWidths X) s) else 0
    Field := (Bool × Fin (2 ^ a)) ⊕ ((Bool × Fin (2 ^ a)) ⊕ (Bool × Fin dH))
    fieldFintype := inferInstance
    width := Sum.elim (fun j => segmentWidth X s v.1.2 j.1 j.2) (Sum.elim
      (fun j => X.halfWidth ((placedPort X).symm v) j.1 j.2)
      (fun j => (dyadicRefreshNext X P hdH hconn F hD hd choice).halfWidth v j.1
        (refreshSlots hd (.inr (.inl j.2))))) }

/-- A degree-dependent upper bound on the counts of the local descriptors,
including the complete demand and supply argument views. -/
def refreshExtraCount (a dH : ℕ) : ℕ := 4 + 4 * 2 ^ a + 2 * dH

set_option backward.isDefEq.respectTransparency false in
theorem refreshLocalRecords_count (choice : DyadicRefreshChoice X P hdH hconn F)
    (v : (X.Base × Fin (2 ^ a)) × BitWord g) :
    (refreshLocalRecords X P hdH hconn F hD hd κ hκ choice v).count = refreshExtraCount a dH := by
  simp [refreshLocalRecords, SiteRecords.count, refreshExtraCount, Fintype.card_sum, Fintype.card_prod]
  ring

/-- An integral constant large enough for both refreshed widths and expander entry degrees. -/
noncomputable def refreshLengthConstant := max 1 (max (Fintype.card (Tie (2 ^ a)))
  ⌈max ((2 ^ a : ℕ) : ℝ) (Real.sqrt ((((2 ^ a : ℕ) : ℝ) / (2 ^ a₀ : ℕ)) *
    (K' * Fintype.card (Tie (2 ^ a)) + max 0 F.energyConstant)))⌉₊)

private theorem refreshNext_width_bound (hK' : 0 ≤ K') (choice : DyadicRefreshChoice X P hdH hconn F)
    (e : ((X.Base × Fin (2 ^ a)) × Fin (2 ^ a₀)) × BitWord g) :
    (dyadicRefreshNext X P hdH hconn F hD hd choice).width e ≤
      refreshLengthConstant P hdH hconn F * (X.maxWireWidth + 1) := by
  have hh := dyadicRefreshNext_width X P hdH hconn F hD hd hK' choice X.width_le_maxWireWidth e
  let U := max ((2 ^ a : ℕ) : ℝ) (Real.sqrt ((((2 ^ a : ℕ) : ℝ) / (2 ^ a₀ : ℕ)) *
    (K' * Fintype.card (Tie (2 ^ a)) + max 0 F.energyConstant)))
  have hu : U ≤ (refreshLengthConstant P hdH hconn F : ℝ) :=
    (Nat.le_ceil U).trans (Nat.cast_le.mpr ((le_max_right ..).trans (le_max_right ..)))
  exact_mod_cast hh.trans (mul_le_mul_of_nonneg_right hu (by positivity))

/-- The placement is a bijection even when it is viewed in the term's own output coordinates. -/
private theorem refreshPreimage_card (choice : DyadicRefreshChoice X P hdH hconn F)
    (v : (X.Base × Fin (2 ^ a)) × BitWord g) :
    Fintype.card (((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term choice).Preimage v) = 1 := by
  let e := placedPort X
  let equiv : (((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term choice).Preimage v) ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨e.symm v, (e.apply_symm_apply v).symm⟩
      left_inv := fun u => Subtype.ext (by
        have h : v = e u.val := u.prop
        exact e.symm_apply_eq.mpr h)
      right_inv := fun _ => rfl }
  simpa using Fintype.card_congr equiv

/-- The chosen layout and every local field and monomial-degree descriptor
satisfy the one-step bound with constants independent of the lanes and old widths. -/
theorem refreshPass_records_bounded (hK' : 0 ≤ K') :
    let pass := dyadicRefreshPass X P hdH hconn F hD hd κ hκ
    let extra := refreshLocalRecords X P hdH hconn F hD hd κ hκ
    pass.Bounded (pass.slotRecords extra)
      (max (refreshExtraCount a dH + 1 * (2 * 2 ^ a) + 2 * 2 ^ a₀ + 1)
        (refreshLengthConstant P hdH hconn F + 1)) := by
  let E := refreshLengthConstant P hdH hconn F
  have hE : 1 ≤ E := le_max_left _ _
  have hW : X.maxWireWidth ≤ E * (X.maxWireWidth + 1) := by nlinarith [Nat.zero_le X.maxWireWidth]
  apply StatePass.slotRecords_bounded _ _ 1 (refreshExtraCount a dH) E hE
  · exact fun i v => (refreshPreimage_card X P hdH hconn F hD hd κ hκ i v).le
  · exact fun i v => (refreshLocalRecords_count X P hdH hconn F hD hd κ hκ i v).le
  · intro i v
    apply max_le
    · apply Finset.sup_le
      rintro (j | (j | j)) _
      · exact (X.width_le_maxWireWidth _).trans hW
      · exact (X.halfWidth_le_max _ _ _).trans hW
      · exact refreshNext_width_bound X P hdH hconn F hD hd hK' i _
    · apply Finset.sup_le
      intro j _
      change Fin 3 at j
      change (if j = 0 then repetitions F _ else 0) ≤ _
      split_ifs
      · have ht : Fintype.card (Tie (2 ^ a)) ≤ E := (le_max_left ..).trans (le_max_right ..)
        refine (term_repetitions_le F _ (W := X.maxWireWidth) ?_).trans (Nat.mul_le_mul ht (by omega))
        intro tie
        unfold blockDemandWidths internalWidth
        split_ifs <;> exact X.width_le_maxWireWidth _
      · exact Nat.zero_le _
  · exact refreshNext_width_bound X P hdH hconn F hD hd hK'

end Compression.Refresh

end VPVNP
end Computability
end OAI

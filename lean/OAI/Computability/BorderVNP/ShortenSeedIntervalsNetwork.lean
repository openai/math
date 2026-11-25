import OAI.Computability.BorderVNP.ShortenNetworkHost
import Mathlib.Data.Finset.Sort

/-!
# Refining the bit intervals of a placed network

Every bit gets one band label. A parallel cable carries the bits of one band,
in their original order. Reassembly works for arbitrary local tables and
preserves width-weighted length for any inherited charge mask.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {J : Type} [Fintype J] (label : ∀ e, Fin (N.width e) → J)

/-- Old bit ordinals carried by a particular piece. -/
abbrev BandBits (e : N.Edge) (j : J) := {k : Fin (N.width e) // label e k = j}

/-- Split every old cable into its labelled pieces, retaining its sites. -/
noncomputable def bands : Network D P bits where
  Site := N.Site
  Edge := N.Edge × J
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := N.src e.1
  dst e := N.dst e.1
  width e := Fintype.card (N.BandBits label e.1 e.2)
  attach := N.attach
  position := N.position
  in_ball := N.in_ball

/-- Increasing numbering of the bits on one new cable. -/
noncomputable def bandOrder (e : N.Edge) (j : J) :
    Fin ((N.bands label).width (e,j)) ≃o N.BandBits label e j :=
  Fintype.orderIsoFinOfCardEq _ rfl

/-- A band's name and its local ordinal identify an old bit uniquely. -/
noncomputable def bandIndex (e : N.Edge) :
    (Σ j, Fin ((N.bands label).width (e,j))) ≃ Fin (N.width e) :=
  (Equiv.sigmaCongrRight fun j => (N.bandOrder label e j).toEquiv).trans
    (Equiv.sigmaFiberEquiv (label e))

/-- The pieces of a cable have its original total width. -/
theorem sum_bands_width (e : N.Edge) : ∑ j, (N.bands label).width (e,j) = N.width e := by
  simpa using Fintype.card_congr (N.bandIndex label e)

/-- Bijective reassembly of the parallel bands, with both ends using the same bit map. -/
noncomputable def bandAssignments : (N.bands label).Assignment ≃ N.Assignment where
  toFun a e k := let q := (N.bandIndex label e).symm k; a (e,q.1) q.2
  invFun a := fun ⟨e,j⟩ k => a e (N.bandIndex label e ⟨j,k⟩)
  left_inv a := by
    funext ⟨e,j⟩ k
    exact congrArg (fun q : Σ i, Fin ((N.bands label).width (e,i)) => a (e,q.1) q.2)
      ((N.bandIndex label e).symm_apply_apply ⟨j,k⟩)
  right_inv a := by
    funext e k
    exact congrArg (a e) ((N.bandIndex label e).apply_symm_apply k)

/-- An old tensor reads the original bits at its own incident cables. -/
noncomputable def bandTables {R : Type*} (table : N.Tables R) : (N.bands label).Tables R :=
  fun v a x => table v (fun e k => let q := (N.bandIndex label e.val).symm k
    a ⟨(e.val,q.1), e.property⟩ q.2) x

/-- Splitting the bands preserves contraction against every external assignment. -/
theorem value_bands {R : Type*} [CommSemiring R] (table : N.Tables R) (x : Ports bits) :
    (N.bands label).value (N.bandTables label table) x = N.value table x := by
  unfold value
  exact Fintype.sum_equiv (N.bandAssignments label) _ _ fun _ => rfl

/-- Every weight depending only on the old cable charges the same total after splitting. -/
theorem weighted_bands (weight : N.Edge → ℝ) :
    ∑ c : (N.bands label).Edge, ((N.bands label).width c : ℝ) * weight c.1 =
      ∑ e, (N.width e : ℝ) * weight e := by
  change (∑ c : N.Edge × J, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  change (∑ j, ((N.bands label).width (e,j) : ℝ) * weight e) = _
  exact (Finset.sum_mul _ _ _).symm.trans (congrArg (· * weight e) (by exact_mod_cast N.sum_bands_width label e))

/-- The inherited old charge mask preserves charged length in any metric placement. -/
theorem chargedLength_bands {H : Type*} [PseudoMetricSpace H] (place : N.Site → H)
    (charged : N.Edge → Bool) :
    Epoch.chargedLength (N.bands label) place (fun c => charged c.1) =
      Epoch.chargedLength N place charged := by
  unfold Epoch.chargedLength
  simpa only [bands, mul_ite, mul_zero] using N.weighted_bands label
    (fun e => if charged e then dist (place (N.src e)) (place (N.dst e)) else 0)

end Crossing.Network

end BorderVNP
end Computability
end OAI

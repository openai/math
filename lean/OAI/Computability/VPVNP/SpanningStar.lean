import OAI.Computability.VPVNP.WireSpectrum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.CastCard

/-! # Diameter of a spectral configuration on all parties

A star joining a central party to every party restricts to the all-parties
diagonal. The loop at the central party has spectral wire distance zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v w

namespace WireTensor

open scoped NNReal

variable {k : Type u} {J : Type v} [Fintype J]

/-- At each party keep the basis vectors whose incident wire labels are all
the output coordinate. Along a spanning star these restrictions impose the
all-parties diagonal. -/
theorem starNetwork_restricts_diagonal [CommSemiring k] {E : Type*} [Fintype E]
    (center : J) (leaf : E → J) (hcover : Function.Surjective leaf)
    (I : Type w) [Fintype I] :
    Restricts (wireNetwork (k := k) (fun _ ↦ center) leaf (fun _ ↦ I)) (diagonal I) := by
  classical
  let W := wireNetwork (k := k) (fun _ : E ↦ center) leaf (fun _ ↦ I)
  let select (j : J) (i : I) : W.Basis j := ⟨fun _ _ ↦ i, fun _ _ ↦ i⟩
  refine ⟨_, (applyLocal_pullback select W.coeff).trans ?_⟩
  funext x
  simp only [W, select, wireNetwork, diagonal]
  rw [Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨x center, fun j ↦ by obtain ⟨e, rfl⟩ := hcover j; exact (h e).symm⟩
  · rintro ⟨i, hi⟩ e
    exact (hi center).trans (hi (leaf e)).symm

namespace SpectralPoint

variable [Field k] (F : SpectralPoint k J)

/-- The total wire distance along the spanning star is at least one. -/
theorem one_le_sum_wireDistance (center : J) : 1 ≤ ∑ j, F.wireDistance center j := by
  have : Nonempty J := ⟨center⟩
  let leaf := (Fintype.equivFin J).symm
  have h := F.monotone (starNetwork_restricts_diagonal (k := k) center leaf leaf.surjective (Fin 2))
  rw [F.value_diagonal_fin, F.value_wireNetwork] at h
  have hprod : (2 : ℝ) ≤ ∏ i, F.wireDimension center (leaf i) 2 := by
    change (2 : ℝ) ≤ ∏ i, (F.value (wire center (leaf i) (Fin 2)) : ℝ)
    exact_mod_cast h
  have hpos (j : J) : 0 < F.wireDimension center j 2 :=
    zero_lt_one.trans_le (F.one_le_wireDimension center j (by decide))
  have hlog := Real.log_le_log (by norm_num : 0 < (2 : ℝ)) hprod
  rw [Real.log_prod fun i _ ↦ (hpos (leaf i)).ne',
    leaf.sum_comp (fun j ↦ Real.log (F.wireDimension center j 2))] at hlog
  simp only [wireDistance, ← Finset.sum_div]
  exact (one_le_div (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

include F in
/-- A nonempty party set admitting a spectral point has at least two parties.
For a singleton, the star sum would vanish. -/
theorem nontrivial_parties [Nonempty J] : Nontrivial J := by
  by_contra! h
  have : Subsingleton J := h
  let center : J := Classical.ofNonempty
  have hzero (j : J) : F.wireDistance center j = 0 := by
    rw [Subsingleton.elim center j, F.wireDistance_self]
  simpa only [hzero, Finset.sum_const_zero, not_le.mpr zero_lt_one] using
    F.one_le_sum_wireDistance center

/-- The sharp normalization bound for the diameter of any configuration whose
labels cover all parties. -/
theorem inv_card_sub_one_le_wire_diameter {ι : Type*} [Fintype ι] [Nonempty ι]
    (label : ι → J) (hlabel : Function.Surjective label) (hcard : 1 < Fintype.card J) :
    1 / ((Fintype.card J : ℝ) - 1) ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun i : ι × ι ↦ F.wireDistance (label i.1) (label i.2)) := by
  classical
  let c : ι := Classical.ofNonempty
  let center := label c
  let diam := Finset.univ.sup' Finset.univ_nonempty
    (fun i : ι × ι ↦ F.wireDistance (label i.1) (label i.2))
  have hdist (j : J) : F.wireDistance center j ≤ diam := by
    obtain ⟨i, rfl⟩ := hlabel j
    exact Finset.le_sup' (fun i : ι × ι ↦ F.wireDistance (label i.1) (label i.2))
      (Finset.mem_univ (c, i))
  have hpos : (0 : ℝ) < Fintype.card J - 1 := sub_pos.mpr (by exact_mod_cast hcard)
  apply (div_le_iff₀ hpos).mpr
  calc
    1 ≤ ∑ j, F.wireDistance center j := F.one_le_sum_wireDistance center
    _ = ∑ j ∈ Finset.univ.erase center, F.wireDistance center j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ center), F.wireDistance_self, add_zero]
    _ ≤ ∑ _j ∈ Finset.univ.erase center, diam := Finset.sum_le_sum fun j _ ↦ hdist j
    _ = diam * ((Fintype.card J : ℝ) - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.cast_card_erase_of_mem (Finset.mem_univ center),
        Finset.card_univ, mul_comm]

end SpectralPoint
end WireTensor

end VPVNP
end Computability
end OAI

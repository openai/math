import OAI.Computability.BorderVNP.CoverLorentzCompact
import OAI.Computability.BorderVNP.CoverLorentzTorsion
import OAI.Computability.BorderVNP.CoverHeckeCorrespondence

/-!
# Compact quaternion frame quotients

Every frame orbit has a bounded representative, and only finitely many integral
quaternion matrices lie in any fixed compact matrix set. In particular, deeply
enough in the congruence tower a compact set contains only the identity among
the subgroup matrices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix Set

/-- The level group, as a subgroup of the real determinant-one matrices. -/
noncomputable abbrev frameGroup (l : ℕ) := (gammaSL l).range

/-- Compactness of the frame quotient, with the congruence group acting on the left. -/
instance compactFrameQuotient (l : ℕ) : CompactSpace (BorderVNP.Hecke.Cosets (frameGroup l)) := by
  obtain ⟨K,hK,hmeet⟩ := exists_compact_representatives l
  let q := BorderVNP.Hecke.coset (frameGroup l)
  have himg : q '' K = univ := by
    apply eq_univ_iff_forall.mpr
    intro z
    induction z using Quotient.inductionOn with
    | _ g =>
      obtain ⟨u,hu⟩ := hmeet g
      refine ⟨gammaSL l u * g,hu,Quotient.sound ?_⟩
      apply QuotientGroup.rightRel_apply.mpr
      simp
  exact ⟨himg ▸ hK.image (show Continuous q from continuous_quot_mk)⟩

/-- Linear reconstruction of the four quaternion coordinates from a real matrix. -/
noncomputable def extract (A : Mat) : Fin 4 → ℝ :=
  ![(A 0 0 + A 1 1)/2, (A 0 0 - A 1 1)/(2*Real.sqrt 2),
    (A 0 1 / 3 + A 1 0)/2, (A 0 1 / 3 - A 1 0)/(2*Real.sqrt 2)]

private theorem extract_continuous : Continuous extract := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [extract] <;> fun_prop

private theorem extract_split (x : Order) :
    extract (split x) = fun i => (↑(QuaternionAlgebra.equivTuple 2 0 3 x i) : ℝ) := by
  funext i
  have ht : Real.sqrt 2 ≠ 0 := by positivity
  fin_cases i <;> simp [split,extract,QuaternionAlgebra.equivTuple_apply] <;>
    field_simp <;> ring

/-- Only finitely many integral quaternions are represented in a compact set of matrices. -/
theorem split_preimage_compact_finite {K : Set Mat} (hK : IsCompact K) :
    (split ⁻¹' K).Finite := by
  let c (a : Fin 4 → ℤ) := fun i => (a i : ℝ)
  have hce : Topology.IsClosedEmbedding c :=
    Topology.IsClosedEmbedding.piMap (fun _ : Fin 4 => Int.isClosedEmbedding_coe_real)
  have hc := (hce.isCompact_preimage (hK.image extract_continuous)).finite_of_discrete
  apply (hc.preimage (QuaternionAlgebra.equivTuple 2 0 3).injective.injOn).subset
  intro x hx
  exact ⟨split x,hx,extract_split x⟩

/-- Each compact matrix region eventually avoids every nonidentity member of a level group. -/
theorem eventually_identity_on_compact {K : Set Mat} (hK : IsCompact K) :
    ∃ l, ∀ d ≥ l, ∀ u : gamma d, split u.val.val ∈ K → u.val = 1 := by
  classical
  let E := {u : Orderˣ | split u.val ∈ K ∧ u ≠ 1}
  have hf : E.Finite := (split_preimage_compact_finite hK).preimage Units.val_injective.injOn
    |>.subset (fun _ hx => hx.1)
  have h (u : E) : ∃ d, u.val ∉ gamma (d+1) := by
    by_contra! hn
    exact u.property.2 (eq_one_of_mem_all hn)
  choose d hd using h
  let := hf.fintype
  let l := (Finset.univ.image d).sup id + 1
  refine ⟨l,?_⟩
  intro n hn u hu
  by_contra hne
  let v : E := ⟨u.val,hu,hne⟩
  have hi : d v ≤ (Finset.univ.image d).sup id :=
    Finset.le_sup (f := id) (Finset.mem_image_of_mem d (Finset.mem_univ v))
  exact hd v (gamma_antitone (show d v + 1 ≤ n by dsimp [l] at hn; omega) u.2)

end Cover

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.Model
import OAI.Computability.VPVNP.BalancedCircuit

/-!
# Balanced cut factorizations at the border

For each balanced subset of the parties, §4.3 uses two local tables coupled by one
rank index. Equation (4.3) puts the target in the Zariski closure of the *sums* of
these contractions. Selecting the set-multilinear coefficients is a polynomial map
on the degree component, so the balanced expansion of actual circuits passes to this
closure even when the tables themselves have no limits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open MvPolynomial VPVNP

variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Field K]

/-- The attainable coefficient arrays obtained by summing one contraction on each balanced
party cut. The rank wire is padded to the same `r` labels on every cut. -/
def balancedCutSums (I J K : Type*) [Fintype I] [DecidableEq I] [Field K]
    (r : ℕ) : Set ((I → J) → K) :=
  {A | ∃ F : (S : Finset I) → CutFactors S (Fin r) J K,
    ∀ a : I → J, A a = ∑ S : Finset I with
      Fintype.card I ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * Fintype.card I,
        (F S).matrix (fun i ↦ a i.val) (fun i ↦ a i.val)}

/-- Padded rank wires retain the specified rank bound on every flattening. -/
theorem mem_balancedCutSums_rank {r : ℕ} {A : (I → J) → K}
    (h : A ∈ balancedCutSums I J K r) :
    ∃ M : (S : Finset I) → Matrix (S → J) (↥(Sᶜ : Finset I) → J) K,
      (∀ a : I → J, A a = ∑ S : Finset I with
        Fintype.card I ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * Fintype.card I,
          M S (fun i ↦ a i.val) (fun i ↦ a i.val)) ∧ ∀ S, (M S).rank ≤ r := by
  obtain ⟨F, hF⟩ := h
  exact ⟨fun S => (F S).matrix, hF, fun S => by simpa using (F S).rank_le⟩

private noncomputable def pad {B : Type*} [Fintype B] (r : ℕ)
    {S : Finset I} (F : CutFactors S B J K) : CutFactors S (Fin r) J K :=
  ⟨.of fun x z => if hz : z.val < Fintype.card B then
      F.left x ((Fintype.equivFin B).symm ⟨z, hz⟩) else 0,
   .of fun z y => if hz : z.val < Fintype.card B then
      F.right ((Fintype.equivFin B).symm ⟨z, hz⟩) y else 0⟩

omit [Fintype J] in
private theorem pad_matrix {B : Type*} [Fintype B] {r : ℕ} (h : Fintype.card B ≤ r)
    {S : Finset I} (F : CutFactors S B J K) : (pad r F).matrix = F.matrix := by
  classical
  ext x y
  let e : B ↪ Fin r := (Fintype.equivFin B).toEmbedding.trans (Fin.castLEEmb h)
  let f (i : Fin r) := (pad r F).left x i * (pad r F).right i y
  change ∑ i, f i = ∑ b, F.left x b * F.right b y
  calc
    ∑ i, f i = ∑ i ∈ Finset.univ.map e, f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hout : ¬ i.val < Fintype.card B := by
        intro hin
        apply hi
        apply Finset.mem_map.mpr
        refine ⟨(Fintype.equivFin B).symm ⟨i, hin⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        simp [e]
      simp [f, pad, hout]
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro b _
      simp [f, e, pad, (Fintype.equivFin B b).isLt]

/-- Exact circuits contribute arrays of the factored form in (4.3). The number of graded
states gives the explicit common bound on all rank wires. -/
theorem circuit_mem_balancedCutSums {s r : ℕ} (c : Circuit K (I × J) s)
    (hI : 3 ≤ Fintype.card I)
    (hr : Fintype.card I * (Fintype.card I * Fintype.card J + s + 1) ≤ r) :
    (fun a : I → J => c.polynomial.coeff (partyExponent Finset.univ a)) ∈
      balancedCutSums I J K r := by
  classical
  obtain ⟨F, hF, hzero⟩ := c.exists_balanced_cutFactors hI
  have h := (Circuit.card_balancedStates_le I J s).trans hr
  refine ⟨fun S => pad r (F S), fun a => ?_⟩
  simp_rw [pad_matrix h]
  rw [hF]
  symm
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro S hS hnot
  rw [hzero S (fun hbal => hnot (Finset.mem_filter.mpr ⟨hS, hbal⟩))]
  rfl

/-- Selecting the set-multilinear coefficients in a degree-component approximation gives
the closure of balanced, rank-bounded contractions, over the very same ambient field. -/
theorem geometricApprox_balancedCutSums {s r : ℕ} {p : MvPolynomial (I × J) K}
    (hI : 3 ≤ Fintype.card I)
    (h : geometricApprox (Fintype.card I) s p)
    (hr : Fintype.card I * (Fintype.card I * Fintype.card J + s + 1) ≤ r) :
    (fun a : I → J => p.coeff (partyExponent Finset.univ a)) ∈
      imageClosure (balancedCutSums I J K r) := by
  classical
  let idx (a : I → J) : DegreeMonomial (I × J) (Fintype.card I) :=
    ⟨partyExponent Finset.univ a, by simp⟩
  have hmap := imageClosure_polynomial h (fun a => X (idx a))
  simp only [eval_X] at hmap
  apply imageClosure_mono _ hmap
  rintro A ⟨v, ⟨m, hm, c, rfl⟩, rfl⟩
  apply circuit_mem_balancedCutSums c hI
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) hr

end Crossing

end BorderVNP
end Computability
end OAI

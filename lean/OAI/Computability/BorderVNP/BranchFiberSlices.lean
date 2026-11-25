import OAI.Computability.BorderVNP.BranchSlice
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Polynomial.Roots

/-! # Dimension descent by weighted slices

For a positive-dimensional component, the weighted polynomial in the scalar is nonzero
modulo its prime ideal if one of the original coefficients survives. This gives a
cardinality estimate on the scalars that fail to cut that component. Each cut raises
the minimum height of the remaining nonmaximal components by one.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open Finset Polynomial

variable {E R : Type*} [Field E] [Fintype E] [CommRing R] [Algebra E R]

/-- At most `deg p` scalars from the advice field land in a given prime component when
some coefficient of `p` is outside that prime. -/
theorem card_bad_slice_scalars (p : Polynomial R) (P : Ideal R) [P.IsPrime]
    (hne : ∃ n, p.coeff n ∉ P) :
    ({a : E | p.eval (algebraMap E R a) ∈ P} : Set E).ncard ≤ p.natDegree := by
  classical
  let S := univ.filter fun a : E ↦ p.eval (algebraMap E R a) ∈ P
  let φ := (Ideal.Quotient.mk P).comp (algebraMap E R)
  let T := S.map ⟨φ, φ.injective⟩
  let q := p.map (Ideal.Quotient.mk P)
  have hq : q ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro eq
    apply hi
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [q] using (congrArg (fun z : Polynomial (R ⧸ P) ↦ z.coeff i) eq)
  have hsub : T.val ⊆ q.roots := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp (show x ∈ T from hx)
    have hp := (mem_filter.mp ha).2
    apply (Polynomial.mem_roots hq).mpr
    change (p.map (Ideal.Quotient.mk P)).eval ((Ideal.Quotient.mk P) (algebraMap E R a)) = 0
    rw [Polynomial.eval_map_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  have hcard : S.card ≤ q.natDegree := by
    simpa [T] using Polynomial.card_le_degree_of_subset_roots hsub
  have hset : {a : E | p.eval (algebraMap E R a) ∈ P} = ↑S := by ext; simp [S]
  rw [hset, Set.ncard_coe_finset]
  exact hcard.trans Polynomial.natDegree_map_le

/-- The equations retained after choosing a list of slice scalars. -/
noncomputable def sliceIdeal (p : Polynomial R) : List E → Ideal R
  | [] => ⊥
  | a :: l => sliceIdeal p l ⊔ Ideal.span {p.eval (algebraMap E R a)}

omit [Fintype E] in
/-- Every original fiber point is retained at every stage. -/
theorem sliceIdeal_le_of_coeff_mem (p : Polynomial R) (P : Ideal R)
    (hp : ∀ n, p.coeff n ∈ P) (l : List E) : sliceIdeal p l ≤ P := by
  induction l with
  | nil => exact bot_le
  | cons a l ih =>
    refine sup_le ih (P.span_singleton_le_iff_mem.mpr ?_)
    have hz : p.map (Ideal.Quotient.mk P) = 0 := by
      ext n
      simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (hp n)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← Polynomial.eval_map_apply, hz, Polynomial.eval_zero]

private theorem exists_good_cut [IsNoetherianRing R] (p : Polynomial R) (I : Ideal R)
    (hbase : ∀ P : Ideal R, P.IsPrime → (∀ n, p.coeff n ∈ P) → P.IsMaximal)
    (hsize : I.minimalPrimes.ncard * p.natDegree < Fintype.card E) :
    ∃ a : E, ∀ P ∈ I.minimalPrimes, ¬ P.IsMaximal → p.eval (algebraMap E R a) ∉ P := by
  classical
  let comps := (I.finite_minimalPrimes_of_isNoetherianRing R).toFinset.filter fun P ↦ ¬P.IsMaximal
  let bad (P : Ideal R) := univ.filter fun a : E ↦ p.eval (algebraMap E R a) ∈ P
  have hcomp : comps.card ≤ I.minimalPrimes.ncard := by
    change (Finset.filter _ _).card ≤ _
    exact (Finset.card_filter_le ..).trans (Set.ncard_eq_toFinset_card _ _).symm.le
  have hone (P : Ideal R) (hP : P ∈ comps) : (bad P).card ≤ p.natDegree := by
    have hs : P ∈ I.minimalPrimes ∧ ¬P.IsMaximal := by simpa [comps] using hP
    let := hs.1.isPrime
    have hne : ∃ n, p.coeff n ∉ P := by
      by_contra! hall
      exact hs.2 (hbase P hs.1.isPrime hall)
    have heq : {a : E | p.eval (algebraMap E R a) ∈ P} = ↑(bad P) := by ext; simp [bad]
    simpa only [heq, Set.ncard_coe_finset] using card_bad_slice_scalars (E := E) p P hne
  have hcard : (comps.biUnion bad).card < Fintype.card E := by
    apply lt_of_le_of_lt (card_biUnion_le ..) _
    apply lt_of_le_of_lt (sum_le_sum hone) _
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_right p.natDegree hcomp).trans_lt hsize
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (t := Finset.univ) (by simpa using hcard)
  refine ⟨a, fun P hP hnm hin ↦ ha (mem_biUnion.mpr ⟨P, ?_, ?_⟩)⟩ <;>
    simp [comps, bad, hP, hnm, hin]

/-- Choose `h` slice scalars over the fixed grid. Once the graph chart has dimension `h`,
every prime through the final cut is maximal. The explicit grid test applies only to
partial choices of fewer than `h` scalars. -/
theorem exists_dimension_cut_slices [IsNoetherianRing R] (p : Polynomial R) (h : ℕ)
    (hdim : ringKrullDim R ≤ h)
    (hbase : ∀ P : Ideal R, P.IsPrime → (∀ n, p.coeff n ∈ P) → P.IsMaximal)
    (hgrid : ∀ l : List E, l.length < h →
      (sliceIdeal p l).minimalPrimes.ncard * p.natDegree < Fintype.card E) :
    ∃ l : List E, l.length = h ∧ ∀ P : Ideal R, P.IsPrime → sliceIdeal p l ≤ P → P.IsMaximal := by
  have build (k : ℕ) (hk : k ≤ h) : ∃ l : List E, l.length = k ∧
      ∀ P ∈ (sliceIdeal p l).minimalPrimes, ¬P.IsMaximal → (k : ℕ∞) ≤ P.height := by
    induction k with
    | zero => exact ⟨[], rfl, fun _ _ _ ↦ zero_le⟩
    | succ k ih =>
      obtain ⟨l, hlen, hold⟩ := ih (by omega)
      obtain ⟨a, ha⟩ := exists_good_cut p (sliceIdeal p l) hbase (hgrid l (by omega))
      refine ⟨a :: l, by simp [hlen], fun P hP hnm ↦ ?_⟩
      let := hP.isPrime
      obtain ⟨Q, hQ, hle⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hP.le)
      let := hQ.isPrime
      have hQnm : ¬Q.IsMaximal := fun hmax ↦ hnm ((hmax.eq_of_le hP.isPrime.ne_top hle) ▸ hmax)
      have hlt : Q < P := lt_of_le_of_ne hle (fun heq ↦ ha Q hQ hQnm (heq ▸
        hP.le (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))))
      exact (add_le_add_left (hold Q hQ hQnm) 1).trans (Ideal.height_add_one_le_of_lt_of_isPrime hlt)
  obtain ⟨l, hl, hs⟩ := build h le_rfl
  refine ⟨l, hl, fun P hP hle ↦ ?_⟩
  let := hP
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hle
  by_contra hnm
  let := hQ.isPrime
  have hQnm : ¬Q.IsMaximal := fun hmax ↦ hnm ((hmax.eq_of_le hP.ne_top hQP) ▸ hmax)
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hP.ne_top
  let := hM
  have hlt : P < M := lt_of_le_of_ne hPM (fun e ↦ hnm (e ▸ hM))
  have hlo : (h : ℕ∞) + 1 ≤ M.height :=
    (add_le_add_left ((hs Q hQ hQnm).trans (Ideal.height_mono hQP)) 1).trans
      (Ideal.height_add_one_le_of_lt_of_isPrime hlt)
  have hhi : M.height ≤ (h : ℕ∞) := WithBot.coe_le_coe.mp (M.height_le_ringKrullDim_of_isPrime.trans hdim)
  exact (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self h)).not_ge (hlo.trans hhi)

end Branch

end BorderVNP
end Computability
end OAI

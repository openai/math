import OAI.Optimization.LinearProgramming.Compression.Representatives
import OAI.Optimization.LinearProgramming.Compression.AffineValue
import OAI.Optimization.LinearProgramming.Compression.ProjectionSmallPoint
import OAI.Optimization.LinearProgramming.Compression.MinorIndex
import OAI.Optimization.LinearProgramming.Compression.OfflineBudget

/-! Offline existence part of the minor-log compression theorem. A single bounded rational
assignment works simultaneously for the four-term comparisons on every nonzero minor. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators Matrix

/-- One small rational point of the whole clipping polyhedron supplies the entire assignment. -/
theorem exists_offline_assignment_of_family {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (F : AffineFamily ι κ) (l : ι → ℝ) (y : κ → ℝ)
    (B E s : ℕ) (hE : 0 < E) (hs : Fintype.card κ ≤ s)
    (happrox : ∀ u, |F.eval y u - l u| ≤ 1 / (E : ℝ))
    (hc : ∀ u j, (F.coefficient u j).num.natAbs ≤ 2*E ∧ (F.coefficient u j).den ≤ 2*E)
    (ho : ∀ u, (F.offset u).num.natAbs ≤ 2*E ∧ (F.offset u).den ≤ 2*E) :
    ∃ f : ι → ℚ, (∀ i, (f i).num.natAbs ≤ offlineValueCap s (2*E) (offlinePointCap s (offlineRowCap B E)) ∧
      (f i).den ≤ offlineValueCap s (2*E) (offlinePointCap s (offlineRowCap B E))) ∧
      ∀ a : ι → ℤ, (∑ i, |(a i : ℝ)|) ≤ 4 →
        |clip B (intForm a (fun i ↦ (f i : ℝ))) - clip B (intForm a l)| ≤ 17 * (1 / (E : ℝ)) := by
  classical
  let η := (1 / (E : ℚ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηcast : (η : ℝ) = 1 / (E : ℝ) := by simp [η]
  let A := clippingMatrix F (B : ℚ) η l
  let b := clippingRhs F (B : ℚ) η l
  let K := offlineRowCap B E
  have hK : 0 < K := by simp only [K, offlineRowCap]; omega
  have hC : 0 < 2*E := by omega
  have abs_from_num (q : ℚ) {c : ℕ} (h : q.num.natAbs ≤ c) : |q| ≤ (c : ℚ) := by
    exact (rat_abs_le_num_natAbs q).trans (by exact_mod_cast h)
  have ⟨hA, hb⟩ := clipping_entries_bounds F B η l hC
    (fun u j ↦ ⟨abs_from_num _ (hc u j).1, (hc u j).2⟩)
    (fun u ↦ ⟨abs_from_num _ (ho u).1, (ho u).2⟩)
    (fun a t ↦ comparisonRow_endpoint_bounds B E hE (intForm a.val l) t)
  have hAk (t j) : (A t j).num.natAbs ≤ K ∧ (A t j).den ≤ K := by
    have h := hA t j
    change _ ≤ K ∧ _ ≤ K
    dsimp only [K, offlineRowCap]
    dsimp only [A]
    omega
  have hbk (t) : (b t).num.natAbs ≤ K ∧ (b t).den ≤ K := by
    have h := hb t
    dsimp only [K, offlineRowCap, b]
    omega
  have hreal := (comparisonRows_iff_mulVec_le F B η l y).mp
    (affineFamily_comparisonRows_feasible F y l l B η hη
      (fun u ↦ (hηcast ▸ happrox u)) (fun u ↦ by simp [hη.le]))
  obtain ⟨v, hv, hheight⟩ := exists_small_rat_feasible A b hK hAk hbk ⟨y, hreal⟩
  have hheight' (j) : (v j).num.natAbs ≤ offlinePointCap s K ∧ (v j).den ≤ offlinePointCap s K := by
    obtain ⟨hn,hd⟩ := hheight j
    exact ⟨hn.trans (offlinePointCap_mono hs hK), hd.trans (offlinePointCap_mono hs hK)⟩
  refine ⟨F.evalRat v, fun i ↦ affine_evalRat_height F v i s (2*E) (offlinePointCap s K) hs
    (hc i) (ho i) hheight', ?_⟩
  have hvr : A.map (Rat.cast : ℚ → ℝ) *ᵥ (fun j ↦ (v j : ℝ)) ≤ fun t ↦ (b t : ℝ) := by
    intro t
    change (∑ j, (A t j : ℝ) * (v j : ℝ)) ≤ (b t : ℝ)
    exact_mod_cast (hv t : (∑ j, A t j * v j) ≤ b t)
  have hr := (comparisonRows_iff_mulVec_le F B η l (fun j ↦ (v j : ℝ))).mpr hvr
  intro a ha
  simpa only [AffineFamily.cast_evalRat, hηcast, Rat.cast_natCast] using
    comparisonRow_abs_clip_sub_le (B := (B : ℚ)) (by positivity) hη (hr a ha)

/-- On any finite index set, a dimension bound on its dissociated subsets gives a height bound
for simultaneous clipped comparison representatives. -/
theorem exists_offline_assignment_of_dissociated_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : ι → ℝ) (B E s : ℕ) (hE : 0 < E)
    (hd : ∀ I : Finset ι, IsDissociated l I → I.card ≤ s) :
    ∃ f : ι → ℚ, (∀ i, (f i).num.natAbs ≤ offlineValueCap s (2*E) (offlinePointCap s (offlineRowCap B E)) ∧
      (f i).den ≤ offlineValueCap s (2*E) (offlinePointCap s (offlineRowCap B E))) ∧
      ∀ a : ι → ℤ, (∑ i, |(a i : ℝ)|) ≤ 4 →
        |clip B (intForm a (fun i ↦ (f i : ℝ))) - clip B (intForm a l)| ≤ 17 * (1 / (E : ℝ)) := by
  classical
  let U := (Finset.univ : Finset ι)
  have hnone : IsDissociated l ∅ := by
    intro A hA B hB hne
    exact (hne ((Finset.subset_empty.mp hA).trans (Finset.subset_empty.mp hB).symm)).elim
  let zeroFamily : AffineFamily U (∅ : Finset ι) := ⟨fun _ _ ↦ 0, fun _ ↦ 0⟩
  obtain ⟨I, _, _, hI, F, hF, _, hc, ho⟩ := exists_completed_affineFamily l U ∅
    (Finset.empty_subset _) hnone E 0 hE ∅ zeroFamily (by simp) (by simp) (by simp)
  let lift := fun i : ι ↦ (⟨i, Finset.mem_univ i⟩ : U)
  let G : AffineFamily ι I := ⟨fun i ↦ F.coefficient (lift i), fun i ↦ F.offset (lift i)⟩
  apply exists_offline_assignment_of_family G l (fun i ↦ l i) B E s hE (by simpa using hd I hI)
  · intro i; exact hF (lift i)
  · intro i j; simpa [G] using hc (lift i) j
  · intro i; simpa [G] using ho (lift i)

open scoped Classical in
/-- The offline mathematical assertion of Theorem 1.4 for the actual nonzero minors of the
input matrices. All coordinates of a single rational assignment have dimension-polynomial
binary length, and all clipped four-term comparisons are simultaneous. -/
theorem exists_bounded_minor_log_assignment {R : Type*} [CommRing R] {rD rE N : ℕ}
    (D : Matrix (Fin rD) (Fin N) R) (E : Matrix (Fin rE) (Fin N) R)
    (hN : 1 ≤ N) (hrows : rD + rE = N) (v : R →+* ℝ) (hv : Function.Injective v) :
    let B : ℕ := 100 * (N + 1)^3
    let l := fun i : NonzeroPairMinor D E ↦ Real.logb 2 (|v (pairMinorValue D E i.val)|)
    ∃ f : NonzeroPairMinor D E → ℚ,
      (∀ i, |f i| ≤ ((2 : ℕ)^offlineValueBits N : ℕ) ∧
        (f i).num.natAbs ≤ 2^offlineValueBits N ∧ (f i).den ≤ 2^offlineValueBits N) ∧
      ∀ a : NonzeroPairMinor D E → ℤ, (∑ i, |(a i : ℝ)|) ≤ 4 →
        |clip B (intForm a (fun i ↦ (f i : ℝ))) - clip B (intForm a l)| ≤ 1 / (2 : ℝ)^B := by
  classical
  let B := 100 * (N + 1)^3
  let G := 2^(B + 7)
  let s := (N + 1)^6
  let l := fun i : NonzeroPairMinor D E ↦ Real.logb 2 (|v (pairMinorValue D E i.val)|)
  have hG : 0 < G := by dsimp [G]; positivity
  have hcard (I : Finset (NonzeroPairMinor D E)) (hI : IsDissociated l I) : I.card ≤ s := by
    have h := dissociated_nonzeroPairMinor_card_le D E hN hrows v hv I l
      (fun i _ ↦ by dsimp [l]; simp only [sub_self, abs_zero]; positivity) hI
    have hs : (I.card : ℝ) ≤ ((N : ℝ) + 1)^6 := h.trans (log_bound_lt_cutoff N).le
    exact_mod_cast hs
  obtain ⟨f, hheight, hclip⟩ := exists_offline_assignment_of_dissociated_bound l B G s hG hcard
  refine ⟨f, ?_, ?_⟩
  · intro i
    obtain ⟨hn,hd⟩ := hheight i
    have hpow := offlineValueCap_le_two_pow N
    have hn' : (f i).num.natAbs ≤ 2^offlineValueBits N := hn.trans hpow
    have hd' : (f i).den ≤ 2^offlineValueBits N := hd.trans hpow
    exact ⟨(rat_abs_le_num_natAbs _).trans (by exact_mod_cast hn'), hn', hd'⟩
  · intro a ha
    apply (hclip a ha).trans
    change 17 * (1 / ((2^(B+7) : ℕ) : ℝ)) ≤ 1 / (2 : ℝ)^B
    push_cast
    rw [pow_add]
    have hp : (0 : ℝ) < 2^B := by positivity
    field_simp
    norm_num

end Compression
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Compression.RequestNative
import OAI.Optimization.LinearProgramming.Compression.AffineRows
import OAI.Optimization.LinearProgramming.Lattice.ShortSelectorSize

/-! Global encoded size of the reduced graph basis. This bound covers the rows the
request scan rejects, in addition to the small row it may return. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators
open _root_.OAI.Optimization.LinearProgramming.Lattice

/-- If the input rows all have norm at most `M`, every reduced row has norm at most
`2ᵖ M`. Otherwise the earlier reduced rows alone would span the whole input lattice. -/
theorem reduceRational_all_rows_le {p n : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ)
    (ha : LinearIndependent ℚ A) {M : ℝ} (hM : ∀ i, ‖euclideanRow (A i)‖ ≤ M)
    (bad : Fin (p+1)) : ‖euclideanRow (reduceRational A bad)‖ ≤ (2 : ℝ)^(p+1)*M := by
  let b := reduceRational A
  obtain ⟨_, hsp⟩ := reduceRational_spec A ((euclideanRow_linearIndependent_iff A).mpr ha)
  have hbindR := independent_of_same_integer_row_lattice ((euclideanRow_linearIndependent_iff A).mpr ha) hsp
  have hbind : LinearIndependent ℤ b :=
    ((euclideanRow_linearIndependent_iff b).mp hbindR).restrict_scalars' _
  by_contra! hlarge
  let S := Set.Iio bad
  have old (i : Fin (p+1)) : A i ∈ Submodule.span ℤ (b '' S) := by
    obtain ⟨j, hj, hn⟩ := reduceRational_short_prefix A ha (A i)
      (Submodule.subset_span (Set.mem_range_self i)) (ha.ne_zero i)
    have hjb : j < bad := by
      by_contra! hb
      exact (not_le_of_gt hlarge) ((hn bad hb).trans (mul_le_mul_of_nonneg_left (hM i) (by positivity)))
    apply (Submodule.span_mono ?_) hj
    exact Set.image_mono (fun _ hi => lt_of_le_of_lt hi hjb)
  have contain : Submodule.span ℤ (Set.range b) ≤ Submodule.span ℤ (b '' S) := by
    rw [show Submodule.span ℤ (Set.range b) = Submodule.span ℤ (Set.range A) from hsp]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact old i)
  exact hbind.notMem_span_image (s := S) (show bad ∉ S by simp [S]) (contain
    (Submodule.subset_span (Set.mem_range_self bad)))

private theorem input_graph_row_norm {d B : ℕ} (w : Fin d → ℚ)
    (hw : ∀ i, (w i).num.natAbs ≤ B) (i : Fin d) :
    ‖euclideanRow (requestInputRows w i)‖ ≤ (B : ℝ)+1 := by
  have hs : ‖euclideanRow (requestInputRows w i)‖^2 = 1 + (w i : ℝ)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    change (∑ j : Fin d, (requestInputRows w i j.castSucc : ℝ)^2) + (requestInputRows w i (Fin.last d) : ℝ)^2 = _
    simp [apply_ite, ite_pow]
  have habsQ := (rat_abs_le_num_natAbs (w i)).trans (show ((w i).num.natAbs : ℚ) ≤ B by exact_mod_cast hw i)
  have habs : |((w i : ℚ) : ℝ)| ≤ (B : ℝ) := by exact_mod_cast habsQ
  have hsq := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg (α := ℝ) B)).mpr habs
  rw [sq_abs] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hs]
  nlinarith [Nat.cast_nonneg (α := ℝ) B]

/-- Multiplying the coordinate magnitude bound by the denominator bound controls the
canonical numerator, even for unreduced descriptions of a lattice row. -/
private theorem num_le_magnitude_mul_den {v : ℚ} {B D : ℕ} (h : |v| ≤ B) (hd : v.den ≤ D) :
    v.num.natAbs ≤ B*D := by
  have hpos : 0 < (v.den : ℚ) := by exact_mod_cast v.den_pos
  rw [← Rat.num_div_den v, abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at h
  have h' : |v.num| ≤ (B*v.den : ℕ) := by exact_mod_cast h
  have hi : v.num.natAbs ≤ B*v.den := Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using h')
  exact hi.trans (Nat.mul_le_mul_left _ hd)

/-- A height bound for every entry of the entire rational reduced graph basis. The
base-two logarithm of the bound is an explicit polynomial in the row count and input
bit width. -/
theorem nativeGraphRowReducer_height {n L : ℕ} (w : Fin (n+1) → ℚ)
    (hw : ∀ i, (w i).num.natAbs.size ≤ L ∧ (w i).den.size ≤ L)
    (i : Fin (n+1)) (j : Fin ((n+1)+1)) :
    let e := (n+1) + (L+1) + L*((n+1)*((n+1)+1))
    ((nativeGraphRowReducer n w i) j).num.natAbs ≤ 2^e ∧
      ((nativeGraphRowReducer n w i) j).den ≤ 2^e := by
  let A := requestInputRows w
  let r := nativeGraphRowReducer n w i
  have hb : 1 ≤ 2^L := Nat.one_le_pow L 2 (by decide)
  have hA : ∀ s t, (A s t).den ≤ 2^L := by
    intro s t
    refine Fin.lastCases ?_ (fun t => ?_) t
    · simpa only [A, requestInputRows_last] using (Nat.size_le.mp (hw s).2).le
    · simp [A, apply_ite, hb]
  have hsp := (nativeGraphRowReducer_correct.spec n w).2.2
  have hm : r ∈ Submodule.span ℤ (Set.range A) := by
    rw [← show Submodule.span ℤ (Set.range (nativeGraphRowReducer n w)) = Submodule.span ℤ (Set.range A) from hsp]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hden := (Nat.le_of_dvd (matrixDenominator_pos A) (rowLattice_denominator_dvd A hm j)).trans
    (matrixDenominator_le_pow A (2^L) hA)
  rw [← pow_mul] at hden
  have hnorm := reduceRational_all_rows_le A (requestInputRows_independent w)
    (input_graph_row_norm w (fun s => (Nat.size_le.mp (hw s).1).le)) i
  have he : |(r j : ℝ)| ≤ ‖euclideanRow r‖ := by
    have h := PiLp.norm_apply_le (euclideanRow r) j
    change ‖(r j : ℝ)‖ ≤ ‖euclideanRow r‖ at h
    rwa [Real.norm_eq_abs] at h
  have hmag : |r j| ≤ ((2 : ℕ)^((n+1)+(L+1)) : ℕ) := by
    have hreal : |(r j : ℝ)| ≤ ((2 : ℝ)^((n+1)+(L+1))) := by
      calc
        _ ≤ (2 : ℝ)^(n+1)*(((2^L : ℕ) : ℝ)+1) := he.trans hnorm
        _ ≤ _ := by
          rw [pow_add (2:ℝ) (n+1) (L+1)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          push_cast
          rw [pow_succ]
          nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := L)]
    exact_mod_cast hreal
  dsimp only
  change (r j).num.natAbs ≤ _ ∧ (r j).den ≤ _
  constructor
  · simpa only [pow_add] using num_le_magnitude_mul_den hmag hden
  · exact hden.trans (Nat.pow_le_pow_right (by decide) (by omega))

end Compression
end LinearProgramming
end Optimization
end OAI

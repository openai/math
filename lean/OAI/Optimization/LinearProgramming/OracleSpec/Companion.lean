import OAI.Optimization.LinearProgramming.OracleSpec.Compression
import OAI.Optimization.LinearProgramming.Compression.Offline

/-! The simultaneous, offline assertion of minor-log compression in the public specification. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace MinorLog

open scoped BigOperators

/-- The public strictly increasing lists carry precisely the same data as the polynomial
proof's canonical row and column order embeddings. -/
def squareEquiv (r n : ℕ) : Square r n ≃ Compression.SquareMinorIndex r n where
  toFun u := ⟨u.order, .ofStrictMono u.rows u.increasingRows, .ofStrictMono u.cols u.increasingCols⟩
  invFun u := ⟨u.1, u.2.1, u.2.2, u.2.1.strictMono, u.2.2.strictMono⟩
  left_inv u := by cases u; rfl
  right_inv u := by rcases u with ⟨k, r, c⟩; rfl

/-- Transport both the matrix tag and the nonzero determinant requirement. -/
def indexEquiv {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ) :
    Index D E ≃ Compression.NonzeroPairMinor D E :=
  (Equiv.sumCongr (squareEquiv d n) (squareEquiv e n)).subtypeEquiv fun u ↦ by
    cases u with
    | inl u => cases u; rfl
    | inr u => cases u; rfl

theorem indexEquiv_minor {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ)
    (E : Matrix (Fin e) (Fin n) ℚ) (u : Index D E) :
    Compression.pairMinorValue D E (indexEquiv D E u).val = minor D E u.val := by
  rcases u with ⟨u, hu⟩
  cases u with
  | inl u => cases u; rfl
  | inr u => cases u; rfl

/-- Theorem 1.4, simultaneous existence, including a polynomial bound on every reduced rational
encoding. This statement uses the same finitely supported comparisons as the online endpoint. -/
theorem offline_bounded_assignment {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ)
    (E : Matrix (Fin e) (Fin n) ℚ) (hn : 1 ≤ n) (hrows : d + e = n) :
    let p : ℕ := 6689 * (n + 1)^21
    ∃ f : Index D E → ℚ,
      (∀ u, |(f u : ℝ)| ≤ (2 : ℝ)^p ∧ RAM.ratBits (f u) ≤ 3 + 2*p) ∧
      ∀ a : Index D E →₀ ℤ, a.sum (fun _ c => c.natAbs) ≤ 4 →
        |clip (threshold n) (a.sum (fun u c => (c : ℝ) * (f u : ℝ))) -
          clip (threshold n) (a.sum (fun u c => (c : ℝ) * logarithm D E u))| ≤
          (1 / 2 : ℝ)^(threshold n) := by
  classical
  let eqv := indexEquiv D E
  let : DecidableEq ℚ := fun x y ↦ Classical.propDecidable (x = y)
  let : Fintype (Index D E) := Fintype.ofEquiv _ eqv.symm
  let p := 6689 * (n+1)^21
  have hp : Compression.offlineValueBits n ≤ p := Compression.offlineValueBits_le n
  have logBound {k b : ℕ} (h : k ≤ 2^b) : k.log2 ≤ b := by
    rcases eq_or_ne k 0 with rfl | hne
    · simp
    · exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ((Nat.log2_self_le hne).trans h)
  obtain ⟨f, hf, hcomp⟩ := Compression.exists_bounded_minor_log_assignment D E hn hrows
    (Rat.castHom ℝ) (Rat.cast_injective (α := ℝ))
  refine ⟨fun u ↦ f (eqv u), ?_, ?_⟩
  · intro u
    obtain ⟨habs, hnum, hden⟩ := hf (eqv u)
    have hnum' : (f (eqv u)).num.natAbs.log2 ≤ p :=
      (logBound hnum).trans hp
    have hden' : (f (eqv u)).den.log2 ≤ p :=
      (logBound hden).trans hp
    constructor
    · have h : |f (eqv u)| ≤ (2 : ℚ)^p := by
        refine habs.trans ?_
        exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) hp
      exact_mod_cast h
    · change 3 + (f (eqv u)).num.natAbs.log2 + (f (eqv u)).den.log2 ≤ 3 + 2*p
      omega
  · intro a ha
    have habs : (∑ j, |(a (eqv.symm j) : ℝ)|) ≤ 4 := by
      rw [eqv.symm.sum_comp (fun i ↦ |(a i : ℝ)|)]
      have hnat : ∑ i, (a i).natAbs ≤ 4 := by simpa [Finsupp.sum_fintype] using ha
      have hcast : (∑ i, |(a i : ℝ)|) = ((∑ i, (a i).natAbs : ℕ) : ℝ) := by
        push_cast; simp only [Nat.cast_natAbs, Int.cast_abs]
      rw [hcast]; exact_mod_cast hnat
    have transport (g : Compression.NonzeroPairMinor D E → ℝ) :
        Compression.intForm (fun j ↦ a (eqv.symm j)) g = a.sum (fun i c ↦ (c : ℝ) * g (eqv i)) := by
      rw [a.sum_fintype (fun i c ↦ (c : ℝ) * g (eqv i)) (fun _ ↦ by simp)]
      unfold Compression.intForm
      simpa only [Equiv.symm_apply_apply] using
        (eqv.sum_comp (fun j ↦ (a (eqv.symm j) : ℝ) * g j)).symm
    have h := hcomp (fun j ↦ a (eqv.symm j)) habs
    rw [transport, transport] at h
    have hcast (x : ℚ) : Rat.castHom ℝ x = (x : ℝ) := rfl
    simpa only [threshold, clip, Compression.clip, logarithm, eqv, indexEquiv_minor,
      hcast, one_div, inv_pow] using h

end MinorLog
end OracleSpec
end LinearProgramming
end Optimization
end OAI

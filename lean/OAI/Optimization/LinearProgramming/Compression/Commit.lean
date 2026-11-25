import OAI.Optimization.LinearProgramming.Compression.Request
import OAI.Optimization.LinearProgramming.Compression.ProjectionCramer
import OAI.Optimization.LinearProgramming.Lattice.Rounding

/-! ## Committing to bounded generator values

Apply homogeneous sign-preserving rounding to the augmented vector and divide by
its last (positive) coordinate. This gives a common rational commitment before
the sequence of successful minor requests is known.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open SignType

/-- Strict numerator and denominator height bound for the normalized representative. -/
def commitHeight (d M : ℕ) : ℕ := Lattice.comparisonRadix (d + 1) M ^ (d + 1)

/-- The normalized height has binary logarithm polynomial in the dimension
and the binary length of the affine-form budget. -/
theorem commitHeight_log2_le (d M : ℕ) :
    (commitHeight d M).log2 ≤ ((d + M.log2 + 4) * (d+1) + M.log2 + 4) * (d+1) := by
  let p := d + 1
  let m := M.log2 + 1
  let t := 2 + p + m
  let h := t * p
  have hbase : 4 * p * M ≤ 2 ^ t := by
    calc
      _ ≤ (2^2 * 2^p) * 2^m :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 p.lt_two_pow_self.le) M.lt_log2_self.le
      _ = _ := by rw [← pow_add, ← pow_add]
  have hone : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hD : Lattice.directionBound p M ≤ 2 ^ (h+1) := by
    unfold Lattice.directionBound
    calc
      _ ≤ (2^t)^p + 1 := Nat.add_le_add_right (Nat.pow_le_pow_left hbase p) 1
      _ = 2^h + 1 := by rw [← pow_mul]
      _ ≤ 2^(h+1) := by rw [pow_succ]; omega
  let k := 1 + m + (h+1)
  have hr : 2 * M * Lattice.directionBound p M ≤ 2^k := by
    calc
      _ ≤ (2^1 * 2^m) * 2^(h+1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 M.lt_log2_self.le) hD
      _ = _ := by rw [← pow_add, ← pow_add]
  have hk : 2 ≤ 2^k := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ k from by dsimp [k]; omega)
  have hradix : Lattice.comparisonRadix p M ≤ 2^(k+1) := by
    rw [Lattice.comparisonRadix, pow_succ]
    omega
  have hp : commitHeight d M ≤ 2^((k+1)*p) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hradix p
  have hlog : (commitHeight d M).log2 ≤ (k+1)*p := by
    by_cases hz : commitHeight d M = 0
    · simp [hz]
    · exact Nat.le_of_lt_succ ((Nat.log2_lt hz).mpr (hp.trans_lt
        (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))))
  convert hlog using 1
  dsimp [k, h, t, m, p]
  ring

/-- Divide the first d integer coordinates by the final coordinate. -/
def normalizeCommit {d : ℕ} (z : Fin (d+1) → ℤ) (i : Fin d) : ℚ :=
  (z i.castSucc : ℚ) / (z (Fin.last d) : ℚ)

/-- A homogeneous sign representative gives valid normalized coordinates for all
affine tests at once. The denominator is strictly positive. -/
theorem normalizeCommit_spec_of_height {d M H : ℕ} (x : Fin d → ℝ) (hM : 0 < M)
    (z : Fin (d+1) → ℤ)
    (hzb : ∀ i, (z i).natAbs < H)
    (hz : ∀ a : Fin (d+1) → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
      sign (dotProduct a z) = sign (dotProduct (Lattice.realCoordinates a) (Fin.snoc x 1))) :
    0 < z (Fin.last d) ∧
    (∀ i, (normalizeCommit z i).num.natAbs < H ∧
      (normalizeCommit z i).den < H) ∧
    (∀ (a : Fin d → ℤ) (c : ℤ), (∑ i, |a i|) + |c| ≤ (M : ℤ) →
      sign (requestForm (fun i => (normalizeCommit z i : ℝ)) a + c) =
        sign (requestForm x a + c)) ∧
    RequestSigns x (fun i => (normalizeCommit z i : ℝ)) M := by
  classical
  let q := z (Fin.last d)
  have test (a : Fin d → ℤ) (c : ℤ) (ha : (∑ i, |a i|) + |c| ≤ (M : ℤ)) :
      sign ((∑ i, a i * z i.castSucc) + c * q) = sign (requestForm x a + c) := by
    have h := hz (Fin.snoc a c) (by simpa [Fin.sum_univ_castSucc] using ha)
    simpa [q, requestForm, Lattice.realCoordinates, dotProduct, Fin.sum_univ_castSucc] using h
  have hq : 0 < q := sign_eq_one_iff.mp (by
    have hm' : (1 : ℤ) ≤ M := by exact_mod_cast hM
    have h := test (fun _ => 0) 1 (by simpa using hm')
    simpa [requestForm] using h)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let γ : Fin d → ℚ := fun i => (z i.castSucc : ℚ) / (q : ℚ)
  have hsign (a : Fin d → ℤ) (c : ℤ) (ha : (∑ i, |a i|) + |c| ≤ (M : ℤ)) :
      sign (requestForm (fun i => (γ i : ℝ)) a + c) = sign (requestForm x a + c) := by
    have hnorm : requestForm (fun i => (γ i : ℝ)) a + c =
        (((∑ i, a i * z i.castSucc) + c * q : ℤ) : ℝ) / (q : ℝ) := by
      simp only [requestForm, γ, Rat.cast_div, Rat.cast_intCast, Int.cast_add, Int.cast_sum,
        Int.cast_mul, ← mul_div_assoc, ← Finset.sum_div]
      field_simp [hqr.ne']
    rw [hnorm, div_eq_mul_inv, sign_mul, sign_pos (inv_pos.mpr hqr), mul_one, sign_intCast]
    exact test a c ha
  refine ⟨hq, ?_, hsign, ?_⟩
  · intro i
    obtain ⟨hn, hd⟩ := reduced_fraction_height (z i.castSucc) q hq.ne'
    exact ⟨hn.trans_lt (hzb _), hd.trans_lt (hzb _)⟩
  · intro a c hbudget
    have ha : (∑ i, |a i|) + |c| ≤ (M : ℤ) := by exact_mod_cast hbudget
    calc
      _ ↔ 0 ≤ sign (requestForm x a + c) := sign_nonneg_iff.symm
      _ ↔ 0 ≤ sign (requestForm (fun i => (γ i : ℝ)) a + c) := by rw [hsign a c ha]
      _ ↔ _ := sign_nonneg_iff

/-- Specialization to the height of the homogeneous existential rounding theorem. -/
theorem normalizeCommit_spec {d M : ℕ} (x : Fin d → ℝ) (hM : 0 < M)
    (z : Fin (d+1) → ℤ)
    (hzb : ∀ i, |z i| < (Lattice.comparisonRadix (d+1) M : ℤ)^(d+1))
    (hz : ∀ a : Fin (d+1) → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
      sign (dotProduct a z) = sign (dotProduct (Lattice.realCoordinates a) (Fin.snoc x 1))) :
    0 < z (Fin.last d) ∧
    (∀ i, (normalizeCommit z i).num.natAbs < commitHeight d M ∧
      (normalizeCommit z i).den < commitHeight d M) ∧
    (∀ (a : Fin d → ℤ) (c : ℤ), (∑ i, |a i|) + |c| ≤ (M : ℤ) →
      sign (requestForm (fun i => (normalizeCommit z i : ℝ)) a + c) =
        sign (requestForm x a + c)) ∧
    RequestSigns x (fun i => (normalizeCommit z i : ℝ)) M := by
  apply normalizeCommit_spec_of_height x hM z _ hz
  intro i
  have h : ((z i).natAbs : ℤ) < (commitHeight d M : ℤ) := by
    simpa [commitHeight, Int.natCast_natAbs] using hzb i
  exact_mod_cast h

/-- Normalizing the last coordinate preserves every bounded affine sign, including
ties, without increasing numerator or denominator height. -/
theorem exists_bounded_affine_representative {d M : ℕ} (x : Fin d → ℝ) (hM : 0 < M) :
    ∃ γ : Fin d → ℚ,
      (∀ i, (γ i).num.natAbs < commitHeight d M ∧ (γ i).den < commitHeight d M) ∧
      (∀ (a : Fin d → ℤ) (c : ℤ), (∑ i, |a i|) + |c| ≤ (M : ℤ) →
        sign (requestForm (fun i => (γ i : ℝ)) a + c) = sign (requestForm x a + c)) ∧
      RequestSigns x (fun i => (γ i : ℝ)) M := by
  obtain ⟨z, hzb, hz⟩ := Lattice.exists_bounded_sign_representative
    (Nat.succ_pos d) hM (Fin.snoc x (1 : ℝ))
  exact ⟨normalizeCommit z, (normalizeCommit_spec x hM z hzb hz).2⟩

/-- Reindex the finite generator list. Preserving bounded affine signs on that
list preserves all halfspaces in the coefficientwise box on the original type. -/
theorem projection_tests_of_requestSigns {κ : Type*} [Fintype κ] {d : ℕ} (e : κ ≃ Fin d)
    (x : κ → ℝ) (γ : Fin d → ℚ) (Q : ℕ)
    (hγ : RequestSigns (fun i => x (e.symm i)) (fun i => (γ i : ℝ)) ((d+1)*Q+1)) :
    ∀ (a : κ → ℤ) (b : ℤ), (∀ i, (a i).natAbs ≤ Q) → b.natAbs ≤ Q →
      (∑ i, (a i : ℝ)*x i) ≤ b → (∑ i, (a i : ℝ)*(γ (e i) : ℝ)) ≤ b := by
  classical
  let M := (d+1)*Q+1
  have hcard : Fintype.card κ = d := (Fintype.card_congr e).trans (Fintype.card_fin d)
  intro a b ha hbc hx
  let a' := fun i => -a (e.symm i)
  have hsum : (∑ i : κ, |(a i : ℝ)|) ≤ Fintype.card κ * (Q : ℝ) := by
    calc
      _ ≤ ∑ _ : κ, (Q : ℝ) := Finset.sum_le_sum fun i _ => (by
        exact_mod_cast (Int.natCast_natAbs (a i)) ▸
          (show ((a i).natAbs : ℤ) ≤ (Q : ℤ) from by exact_mod_cast ha i))
      _ = _ := by simp
  have hb' : |(b : ℝ)| ≤ Q := by
    exact_mod_cast (Int.natCast_natAbs b) ▸
      (show ((b.natAbs : ℕ) : ℤ) ≤ (Q : ℤ) from by exact_mod_cast hbc)
  have hbudget : (∑ i, |(a' i : ℝ)|) + |(b : ℝ)| ≤ M := by
    simp only [a', Int.cast_neg, abs_neg]
    rw [e.symm.sum_comp (fun i => |(a i : ℝ)|)]
    dsimp [M]
    push_cast
    rw [hcard] at hsum
    linarith
  have evaluate (w : κ → ℝ) : requestForm (fun i => w (e.symm i)) a' =
      -(∑ i, (a i : ℝ) * w i) := by
    simp only [requestForm, a', Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
    rw [e.symm.sum_comp (fun i => (a i : ℝ) * w i)]
  have htest := (hγ a' b hbudget).mp (by rw [evaluate]; linarith)
  have heval := evaluate (fun i => (γ (e i) : ℝ))
  simp only [Equiv.apply_symm_apply] at heval
  rw [heval] at htest
  linarith

/-- A single bounded rational vector obeys every integer half-space with bounded
coefficients and constant that contains x. The bound depends only on dimension
and coefficient height, even when the system has arbitrarily many rows. -/
theorem exists_bounded_projection_commit {κ : Type*} [Fintype κ] (x : κ → ℝ) (Q : ℕ) :
    ∃ γ : κ → ℚ,
      (∀ i, (γ i).num.natAbs < commitHeight (Fintype.card κ) ((Fintype.card κ+1)*Q+1) ∧
        (γ i).den < commitHeight (Fintype.card κ) ((Fintype.card κ+1)*Q+1)) ∧
      ∀ (a : κ → ℤ) (b : ℤ), (∀ i, (a i).natAbs ≤ Q) → b.natAbs ≤ Q →
        (∑ i, (a i : ℝ) * x i) ≤ b → (∑ i, (a i : ℝ) * (γ i : ℝ)) ≤ b := by
  classical
  let e := Fintype.equivFin κ
  let M := (Fintype.card κ + 1) * Q + 1
  obtain ⟨γ, hb, _, hγ⟩ := exists_bounded_affine_representative (M := M)
    (fun i => x (e.symm i)) (Nat.succ_pos _)
  exact ⟨fun i => γ (e i), fun i => hb (e i), projection_tests_of_requestSigns e x γ Q hγ⟩

end Compression
end LinearProgramming
end Optimization
end OAI

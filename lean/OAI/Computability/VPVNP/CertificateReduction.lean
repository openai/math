import OAI.Computability.VPVNP.GreedyBasis
import OAI.Computability.VPVNP.RankMinors
import OAI.Computability.VPVNP.SmallPrime
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Reduction of the bounded certificate matrix to prime characteristic

Section 8.2 of *VP and VNP differ over every field* uses an integer matrix of
coefficient rows and the target row for the constant polynomial one. When the
target raises the rational rank, every prime avoiding a fixed nonzero maximal
minor of the augmented matrix preserves nonmembership in the row span.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CertificateReduction

open Set VPVNP.Crossing VPVNP.RankQuery

variable {n m q : ℕ}

private theorem exists_nonzero_minor {K : Type*} [Field K] (M : Matrix (Fin n) (Fin m) K) :
    ∃ I J, compound M.rank M I J ≠ 0 := by
  obtain ⟨I, hI, _⟩ := exists_isolatedBasis K M.row M.rank_eq_finrank_span_row
  obtain ⟨J, hJ, _⟩ := exists_isolatedBasis K M.col M.rank_eq_finrank_span_cols
  exact ⟨I, J, (compound_ne_zero_iff M rfl I J).mpr ⟨hI, hJ⟩⟩

/-- An integer coefficient matrix over a specified ring. -/
abbrev castMatrix (R : Type*) [CommRing R] (M : Matrix (Fin n) (Fin m) ℤ) :=
  M.map (Int.castRingHom R)

/-- Add the target coefficient row to the matrix of candidate certificates. -/
def augment {R : Type*} (M : Matrix (Fin n) (Fin m) R) (v : Fin m → R) :
    Matrix (Fin (n + 1)) (Fin m) R := Fin.cons v M

theorem cast_compound (R : Type*) [CommRing R] (M : Matrix (Fin n) (Fin m) ℤ)
    (I : powersetCard (Fin n) q) (J : powersetCard (Fin m) q) :
    compound q (castMatrix R M) I J = (compound q M I J : ℤ) := by
  exact ((Int.castRingHom R).map_det _).symm

private theorem order_le_rank_of_minor {K : Type*} [Field K] (M : Matrix (Fin n) (Fin m) K)
    (I : powersetCard (Fin n) q) (J : powersetCard (Fin m) q) (h : compound q M I J ≠ 0) :
    q ≤ M.rank := le_of_not_gt (fun hlt => h (compound_eq_zero_of_rank_lt M hlt I J))

/-- Reduction of an integer matrix modulo a prime cannot increase its rational rank. -/
theorem rank_mod_le_rat (M : Matrix (Fin n) (Fin m) ℤ) (p : ℕ) [Fact p.Prime] :
    (castMatrix (ZMod p) M).rank ≤ (castMatrix ℚ M).rank := by
  by_contra! hlt
  obtain ⟨I, J, hIJ⟩ := exists_nonzero_minor (castMatrix (ZMod p) M)
  have hz := compound_eq_zero_of_rank_lt (castMatrix ℚ M) hlt I J
  rw [cast_compound] at hz hIJ
  have hint : compound _ M I J = 0 := by exact_mod_cast hz
  exact hIJ (by rw [hint, Int.cast_zero])

private theorem cast_augment (R : Type*) [CommRing R] (M : Matrix (Fin n) (Fin m) ℤ)
    (v : Fin m → ℤ) :
    castMatrix R (augment M v) = augment (castMatrix R M) (fun j => (v j : R)) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

/-- A target is outside the row span precisely when adding it raises rank. -/
theorem rank_lt_augment_iff {K : Type*} [Field K] (M : Matrix (Fin n) (Fin m) K)
    (v : Fin m → K) :
    M.rank < (augment M v).rank ↔ v ∉ Submodule.span K (range M.row) := by
  have hr : range (augment M v).row = insert v (range M.row) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact Fin.cases (.inl rfl) (fun k => .inr ⟨k, rfl⟩) i
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨0, rfl⟩
      · exact ⟨i.succ, rfl⟩
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row, hr]
  constructor
  · intro hlt hv
    rw [Submodule.span_insert_eq_span hv] at hlt
    exact hlt.false
  · intro hv
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne (Submodule.span_mono (subset_insert _ _)) (fun he => hv ?_)
    rw [he]
    exact Submodule.subset_span (mem_insert _ _)

/-- The explicit good-prime test. A nonvanishing augmented minor whose order
exceeds the original rational rank obstructs row-span membership modulo `p`. -/
theorem notMem_rowSpan_of_not_dvd_minor (M : Matrix (Fin n) (Fin m) ℤ) (v : Fin m → ℤ)
    (hq : (castMatrix ℚ M).rank < q) (I : powersetCard (Fin (n + 1)) q)
    (J : powersetCard (Fin m) q) (p : ℕ) [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ compound q (augment M v) I J) :
    (fun j => (v j : ZMod p)) ∉ Submodule.span (ZMod p) (range (castMatrix (ZMod p) M).row) := by
  intro hmem
  have hn : compound q (castMatrix (ZMod p) (augment M v)) I J ≠ 0 := by
    rw [cast_compound]
    exact fun h => hp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hle := order_le_rank_of_minor _ I J hn
  rw [cast_augment] at hle
  exact (rank_lt_augment_iff _ _).mp (((rank_mod_le_rat M p).trans_lt hq).trans_le hle) hmem

/-- The permutation expansion bounds an integer minor of order `q` by
`q! * L^q` when all entries have absolute value at most `L`. -/
theorem natAbs_compound_le (M : Matrix (Fin n) (Fin m) ℤ) (L : ℕ)
    (hL : ∀ i j, (M i j).natAbs ≤ L) (I : powersetCard (Fin n) q)
    (J : powersetCard (Fin m) q) :
    (compound q M I J).natAbs ≤ q.factorial * L ^ q := by
  let N := M.submatrix (powersetCard.ofFinEmbEquiv.symm I) (powersetCard.ofFinEmbEquiv.symm J)
  have hn (i j : Fin q) : AbsoluteValue.abs (N i j) ≤ (L : ℤ) := by
    rw [AbsoluteValue.abs_apply, Int.abs_eq_natAbs]
    exact_mod_cast hL _ _
  have h := Matrix.det_le hn
  simp only [AbsoluteValue.abs_apply, Int.abs_eq_natAbs, Fintype.card_fin, nsmul_eq_mul] at h
  change N.det.natAbs ≤ q.factorial * L ^ q
  exact_mod_cast h

/-- With at most `2^a` columns and entries bounded by `2^b`, a prime of at
most `2 * (a + clog 2 (a+b+2)) + 2` bits preserves the obstruction.
No restriction on the number of rows is needed. -/
theorem exists_bounded_good_prime (M : Matrix (Fin n) (Fin m) ℤ) (v : Fin m → ℤ)
    (a b : ℕ) (hm : m ≤ 2 ^ a) (hentry : ∀ i j, (augment M v i j).natAbs ≤ 2 ^ b)
    (h : (castMatrix ℚ M).rank < (castMatrix ℚ (augment M v)).rank) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 ^ (2 * (a + Nat.clog 2 (a + b + 2)) + 1) ∧
      (fun j => (v j : ZMod p)) ∉ Submodule.span (ZMod p) (range (castMatrix (ZMod p) M).row) := by
  let q := (castMatrix ℚ (augment M v)).rank
  have hq : q ≤ 2 ^ a := (by simpa [q] using (castMatrix ℚ (augment M v)).rank_le_card_width :
    q ≤ m).trans hm
  obtain ⟨I, J, hn⟩ := exists_nonzero_minor (castMatrix ℚ (augment M v))
  let D := compound q (augment M v) I J
  have hD : D ≠ 0 := by
    intro hz
    apply hn
    rw [cast_compound]
    change (D : ℚ) = 0
    rw [hz, Int.cast_zero]
  have hsize : D.natAbs ≤ 2 ^ ((a + b) * q) := calc
    D.natAbs ≤ q.factorial * (2 ^ b) ^ q := natAbs_compound_le _ _ hentry I J
    _ ≤ (2 ^ a) ^ q * (2 ^ b) ^ q := Nat.mul_le_mul_right _
      (q.factorial_le_pow.trans (Nat.pow_le_pow_left hq q))
    _ = 2 ^ ((a + b) * q) := by rw [← mul_pow, ← pow_add, pow_mul]
  obtain ⟨p, prime, hp, hndvd⟩ := exists_small_prime_not_dvd_int hD hsize
  let : Fact p.Prime := ⟨prime⟩
  refine ⟨p, prime, hp.trans ?_, notMem_rowSpan_of_not_dvd_minor M v h I J p hndvd⟩
  have hbase : (a + b) * q + 2 ≤ 2 ^ (a + Nat.clog 2 (a + b + 2)) := calc
    (a + b) * q + 2 ≤ (a + b) * 2 ^ a + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hq) 2
    _ ≤ (a + b + 2) * 2 ^ a := by
      rw [Nat.add_mul (a + b) 2]; exact Nat.add_le_add_left (Nat.le_mul_of_pos_right 2 (by positivity)) _
    _ ≤ 2 ^ Nat.clog 2 (a + b + 2) * 2 ^ a :=
      Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
    _ = _ := by rw [← pow_add, Nat.add_comm]
  calc
    2 * ((a + b) * q + 2) ^ 2 ≤ 2 * (2 ^ (a + Nat.clog 2 (a + b + 2))) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 2)
    _ = _ := by rw [← pow_mul, Nat.mul_comm (a + _), pow_succ, Nat.mul_comm]

/-- Every rational rank-raising target remains outside the certificate row span
in some prime characteristic. -/
theorem exists_good_prime (M : Matrix (Fin n) (Fin m) ℤ) (v : Fin m → ℤ)
    (h : (castMatrix ℚ M).rank < (castMatrix ℚ (augment M v)).rank) :
    ∃ p : ℕ, p.Prime ∧ (fun j => (v j : ZMod p)) ∉
      Submodule.span (ZMod p) (range (castMatrix (ZMod p) M).row) := by
  let b := Finset.univ.sup (fun ij : Fin (n + 1) × Fin m => (augment M v ij.1 ij.2).natAbs)
  have hb (i : Fin (n + 1)) (j : Fin m) : (augment M v i j).natAbs ≤ 2 ^ b :=
    (Finset.le_sup (f := fun ij : Fin (n + 1) × Fin m => (augment M v ij.1 ij.2).natAbs)
      (Finset.mem_univ (i, j))).trans Nat.lt_two_pow_self.le
  obtain ⟨p, hp, _, hspan⟩ := exists_bounded_good_prime M v m b Nat.lt_two_pow_self.le hb h
  exact ⟨p, hp, hspan⟩

private theorem row_mem_reindex_iff {K : Type*} [CommRing K] {I J I' J' : Type*}
    (M : Matrix I J K) (v : J → K) (rows : I' ≃ I) (cols : J' ≃ J) :
    v ∘ cols ∈ Submodule.span K (range (M.submatrix rows cols).row) ↔
      v ∈ Submodule.span K (range M.row) := by
  let e := LinearEquiv.funCongrLeft K K cols
  change e v ∈ Submodule.span K (range ((e ∘ M.row) ∘ rows)) ↔ _
  rw [rows.surjective.range_comp, range_comp]
  change e v ∈ Submodule.span K (e.toLinearMap '' range M.row) ↔ _
  rw [← Submodule.map_span]
  constructor
  · rintro ⟨w, hw, he⟩
    exact e.injective he ▸ hw
  · exact fun hv => ⟨v, hv, rfl⟩

/-- The bounded good-prime criterion on arbitrary finite index types, with the
rational hypothesis expressed directly as nonmembership in the row span. -/
theorem exists_bounded_good_prime_of_notMem {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℤ) (v : J → ℤ) (a b : ℕ) (hJ : Fintype.card J ≤ 2 ^ a)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ b) (hv : ∀ j, (v j).natAbs ≤ 2 ^ b)
    (h : (fun j => (v j : ℚ)) ∉ Submodule.span ℚ (range (M.map (Int.castRingHom ℚ)).row)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 ^ (2 * (a + Nat.clog 2 (a + b + 2)) + 1) ∧
      (fun j => (v j : ZMod p)) ∉
        Submodule.span (ZMod p) (range (M.map (Int.castRingHom (ZMod p))).row) := by
  classical
  let rows := (Fintype.equivFin I).symm
  let cols := (Fintype.equivFin J).symm
  let N := M.submatrix rows cols
  let w := v ∘ cols
  have h' : (castMatrix ℚ N).rank < (castMatrix ℚ (augment N w)).rank := by
    rw [cast_augment, rank_lt_augment_iff]
    exact fun hmem => h ((row_mem_reindex_iff (M.map (Int.castRingHom ℚ)) (fun j => (v j : ℚ)) rows cols).mp hmem)
  have hentry (i) (j) : (augment N w i j).natAbs ≤ 2 ^ b :=
    Fin.cases (hv _) (fun k => hM (rows k) (cols j)) i
  obtain ⟨p, hp, hsize, hspan⟩ := exists_bounded_good_prime N w a b hJ hentry h'
  exact ⟨p, hp, hsize, fun hm => hspan ((row_mem_reindex_iff (M.map (Int.castRingHom (ZMod p))) (fun j => (v j : ZMod p)) rows cols).mpr hm)⟩

end CertificateReduction

end VPVNP
end Computability
end OAI

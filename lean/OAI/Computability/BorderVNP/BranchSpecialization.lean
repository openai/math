import OAI.Computability.VPVNP.CertificateReduction

/-!
# Preserving a rational row relation in small prime characteristic

The coefficient matrix in Lemma 9.1 of *An explicit VNP family requires
superpolynomial border circuit size over every field* has many more columns
than rows. A maximal minor of the original matrix preserves the rank on
reduction. Since adjoining the target row did not increase the rational rank,
it cannot increase the rank modulo the chosen prime either.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Specialization

open Set VPVNP VPVNP.CertificateReduction VPVNP.Crossing VPVNP.RankQuery

private theorem cast_augment {n m : ℕ} (R : Type*) [CommRing R]
    (M : Matrix (Fin n) (Fin m) ℤ) (v : Fin m → ℤ) :
    castMatrix R (augment M v) = augment (castMatrix R M) (fun j => (v j : R)) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

/-- Any prime preserving a maximal minor of the coefficient matrix preserves
membership of the target in its row span. -/
theorem rowSpan_of_not_dvd_minor {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℤ)
    (v : Fin m → ℤ)
    (hv : (fun j => (v j : ℚ)) ∈ Submodule.span ℚ (range (castMatrix ℚ M).row))
    (I : powersetCard (Fin n) (castMatrix ℚ M).rank)
    (J : powersetCard (Fin m) (castMatrix ℚ M).rank)
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ compound _ M I J) :
    (fun j => (v j : ZMod p)) ∈ Submodule.span (ZMod p) (range (castMatrix (ZMod p) M).row) := by
  have hr : (castMatrix ℚ (augment M v)).rank ≤ (castMatrix ℚ M).rank := by
    rw [cast_augment, ← not_lt, rank_lt_augment_iff]
    exact not_not_intro hv
  have hn : compound _ (castMatrix (ZMod p) M) I J ≠ 0 := by
    rw [cast_compound]
    exact fun h => hp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hle : (castMatrix ℚ M).rank ≤ (castMatrix (ZMod p) M).rank :=
    le_of_not_gt (fun hlt => hn (compound_eq_zero_of_rank_lt _ hlt I J))
  by_contra h
  have hlt := (rank_lt_augment_iff _ _).mpr h
  rw [← cast_augment] at hlt
  exact hlt.not_ge ((rank_mod_le_rat (augment M v) p).trans (hr.trans hle))

private theorem prime_size {a b e q p : ℕ} (hq : q ≤ 2 ^ a)
    (hp : p ≤ 2 * ((a+b)*q + e + 2)^2) :
    p ≤ 2 ^ (2*(a + Nat.clog 2 (a+b+e+2)) + 1) := by
  have hbase : (a+b)*q + e + 2 ≤ 2 ^ (a + Nat.clog 2 (a+b+e+2)) := calc
    (a+b)*q + e + 2 ≤ (a+b)*2^a + (e+2)*2^a := by
      have h := Nat.mul_le_mul_left (a+b) hq
      have h' := Nat.le_mul_of_pos_right (e+2) (by positivity : 0 < 2^a)
      omega
    _ = (a+b+e+2)*2^a := by ring
    _ ≤ 2 ^ Nat.clog 2 (a+b+e+2) * 2^a :=
      Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
    _ = _ := by rw [← pow_add, Nat.add_comm]
  refine hp.trans ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase 2)).trans ?_)
  rw [← pow_mul, Nat.mul_comm (a + _), pow_succ, Nat.mul_comm]

private theorem good_prime_fin {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℤ)
    (v : Fin m → ℤ) (exclusion : ℤ) (a b e : ℕ)
    (hn : n ≤ 2 ^ a) (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ b)
    (hex : exclusion ≠ 0) (he : exclusion.natAbs ≤ 2 ^ e)
    (hv : (fun j => (v j : ℚ)) ∈ Submodule.span ℚ (range (castMatrix ℚ M).row)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 ^ (2*(a + Nat.clog 2 (a+b+e+2)) + 1) ∧
      ¬ (p : ℤ) ∣ exclusion ∧
      (fun j => (v j : ZMod p)) ∈ Submodule.span (ZMod p) (range (castMatrix (ZMod p) M).row) := by
  let N := castMatrix ℚ M
  let q := N.rank
  have hq : q ≤ 2 ^ a := (by simpa [q] using N.rank_le_card_height : q ≤ n).trans hn
  obtain ⟨I, hI, _⟩ := exists_isolatedBasis ℚ N.row N.rank_eq_finrank_span_row
  obtain ⟨J, hJ, _⟩ := exists_isolatedBasis ℚ N.col N.rank_eq_finrank_span_cols
  have hIJ := (compound_ne_zero_iff N rfl I J).mpr ⟨hI, hJ⟩
  let D := compound q M I J
  have hD : D ≠ 0 := by
    intro h
    apply hIJ
    rw [cast_compound]
    change (D : ℚ) = 0
    rw [h, Int.cast_zero]
  have hsize : D.natAbs ≤ 2 ^ ((a+b)*q) := calc
    D.natAbs ≤ q.factorial * (2 ^ b)^q := natAbs_compound_le M _ hM I J
    _ ≤ (2 ^ a)^q * (2 ^ b)^q :=
      Nat.mul_le_mul_right _ (q.factorial_le_pow.trans (Nat.pow_le_pow_left hq q))
    _ = 2 ^ ((a+b)*q) := by rw [← mul_pow, ← pow_add, pow_mul]
  have hprod : (D * exclusion).natAbs ≤ 2 ^ ((a+b)*q + e) := by
    rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_le_mul hsize he
  obtain ⟨p, hp, hbound, havoid⟩ :=
    exists_small_prime_not_dvd_int (mul_ne_zero hD hex) hprod
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, prime_size hq hbound, fun h => havoid (dvd_mul_of_dvd_right h _),
    rowSpan_of_not_dvd_minor M v hv I J p (fun h => havoid (dvd_mul_of_dvd_left h _))⟩

private theorem rowSpan_reindex {K I J I' J' : Type*} [Field K]
    (M : Matrix I J K) (v : J → K) (rows : I' ≃ I) (cols : J' ≃ J) :
    v ∘ cols ∈ Submodule.span K (range (M.submatrix rows cols).row) ↔
      v ∈ Submodule.span K (range M.row) := by
  let E := LinearEquiv.funCongrLeft K K cols
  change E v ∈ Submodule.span K (range ((E ∘ M.row) ∘ rows)) ↔ _
  rw [rows.surjective.range_comp, range_comp]
  change E v ∈ Submodule.span K (E.toLinearMap '' range M.row) ↔ _
  rw [← Submodule.map_span]
  constructor
  · rintro ⟨w, hw, he⟩
    exact E.injective he ▸ hw
  · exact fun hv => ⟨v, hv, rfl⟩

/-- Row relations survive scalar extension along any ring homomorphism. -/
theorem rowSpan_map {I J R S : Type*} [Fintype I] [CommRing R] [CommRing S]
    (M : Matrix I J R) (v : J → R) (f : R →+* S)
    (hv : v ∈ Submodule.span R (range M.row)) :
    f ∘ v ∈ Submodule.span S (range (M.map f).row) := by
  rw [← range_vecMulLinear] at hv ⊢
  obtain ⟨w, rfl⟩ := hv
  refine ⟨f ∘ w, ?_⟩
  funext j
  simp [Matrix.vecMul, dotProduct, Matrix.map_apply]

/-- With at most `2^a` rows, `b` bits per entry and a fixed exclusion integer
of absolute value at most `2^e`, one prime of the displayed size preserves
the target row relation over every field of that characteristic. -/
theorem exists_bounded_rowSpan_prime {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℤ) (v : J → ℤ) (exclusion : ℤ) (a b e : ℕ)
    (hn : Fintype.card I ≤ 2 ^ a) (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ b)
    (hex : exclusion ≠ 0) (he : exclusion.natAbs ≤ 2 ^ e)
    (hv : (fun j => (v j : ℚ)) ∈ Submodule.span ℚ (range (M.map (Int.castRingHom ℚ)).row)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 ^ (2*(a + Nat.clog 2 (a+b+e+2)) + 1) ∧
      ¬ (p : ℤ) ∣ exclusion ∧ ∀ (K : Type*) [Field K] [CharP K p],
      (fun j => (v j : K)) ∈ Submodule.span K (range (M.map (Int.castRingHom K)).row) := by
  classical
  let rows := (Fintype.equivFin I).symm
  let cols := (Fintype.equivFin J).symm
  obtain ⟨p, hp, hsize, hnot, hm⟩ := good_prime_fin (M.submatrix rows cols) (v ∘ cols)
    exclusion a b e hn (fun i j => hM _ _) hex he
    ((rowSpan_reindex (M.map (Int.castRingHom ℚ)) (fun j => (v j : ℚ)) rows cols).mpr hv)
  refine ⟨p, hp, hsize, hnot, ?_⟩
  intro K _ _
  let : Fact p.Prime := ⟨hp⟩
  have h := (rowSpan_reindex (M.map (Int.castRingHom (ZMod p))) (fun j => (v j : ZMod p))
    rows cols).mp hm
  have hh := rowSpan_map _ _ (ZMod.castHom (dvd_refl p) K) h
  simpa only [Function.comp_def, map_intCast, Int.coe_castRingHom,
    Matrix.map, Matrix.of_apply] using hh

end Specialization

end BorderVNP
end Computability
end OAI

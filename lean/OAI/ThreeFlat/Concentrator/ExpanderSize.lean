import OAI.ThreeFlat.RouteExpanders

namespace OAI
/-! # Regular graphs at the two concentrator scales

The greedy pass chooses a dyadic order covering its slots. The reserve pass
chooses a dyadic order whose directed edges cover its slots. In both cases
the first admissible order loses at most a factor of two.
-/

namespace ThreeFlat.Concentrator

open BinPackingGames.Foundations.PCP PoweringWalks SpectralReturn

/-- The first dyadic multiple of `d` reaching `N` is at most `2 * N`. -/
theorem exists_dyadic_multiple {d N : ℕ} (hd : 0 < d) (hN : d ≤ N) :
    ∃ k : ℕ, N ≤ 2 ^ k * d ∧ 2 ^ k * d ≤ 2 * N := by
  have existsLevel : ∃ k : ℕ, N ≤ 2 ^ k * d :=
    ⟨N, N.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ hd)⟩
  refine ⟨Nat.find existsLevel, Nat.find_spec existsLevel, ?_⟩
  cases hk : Nat.find existsLevel with
  | zero => simpa using hN.trans (Nat.le_mul_of_pos_left N (by decide : 0 < 2))
  | succ j =>
    have before : j < Nat.find existsLevel := by omega
    have hprev : 2 ^ j * d < N := lt_of_not_ge (Nat.find_min existsLevel before)
    rw [pow_succ]
    calc
      2 ^ j * 2 * d = 2 * (2 ^ j * d) := by ring
      _ ≤ 2 * N := Nat.mul_le_mul_left _ hprev.le

/-- A fixed degree and spectral bound work simultaneously for both passes
at every scale. Small instances of the reserve pass use the complete graph. -/
theorem exists_concentrator_expanders (minDegree : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, 0 < d ∧ minDegree ≤ d ∧ ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ ε ∧
      (∀ N : ℕ, 0 < N → ∃ k : ℕ, N ≤ 2 ^ k ∧ 2 ^ k ≤ 2 * N ∧
        ∃ G : PortGraph (Fin (2 ^ k)) (Fin d), SpectralCertificate G lam) ∧
      (∀ N : ℕ, d ≤ N → ∃ k : ℕ, N ≤ 2 ^ k * d ∧ 2 ^ k * d ≤ 2 * N ∧
        ∃ G : PortGraph (Fin (2 ^ k)) (Fin d), SpectralCertificate G lam) := by
  obtain ⟨h, hh, hmin, lam, hsq, graphs⟩ :=
    RouteUnits.exists_routing_graphs minDegree (sq_pos_of_pos hε)
  obtain ⟨_, cert⟩ := graphs 0
  refine ⟨2 * h, by omega, by omega, lam, cert.nonnegative,
    le_of_sq_le_sq hsq hε.le, ?_, ?_⟩
  · intro N hN
    obtain ⟨k, hlow, hhigh⟩ := exists_dyadic_multiple (d := 1) (by decide) hN
    exact ⟨k, by simpa using hlow, by simpa using hhigh, graphs k⟩
  · intro N hN
    obtain ⟨k, hlow, hhigh⟩ := exists_dyadic_multiple (by omega : 0 < 2 * h) hN
    exact ⟨k, hlow, hhigh, graphs k⟩

end ThreeFlat.Concentrator

end OAI

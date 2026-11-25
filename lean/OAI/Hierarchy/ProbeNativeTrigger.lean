import OAI.Hierarchy.ProbeExcess
import OAI.Hierarchy.ProbeSortedPayload

namespace OAI
/-! # The two actual excess branches imply the native signed-motion energy test -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
universe v
noncomputable section

variable {P : Type*} [Fintype P] [Nonempty P] {N k : ℕ}

omit [Nonempty P] in
/-- Exactly the statistic on the true `Commodity` stock plane required by
`ProtocolRAMPurchaseDensity.acquire`. Summing the two normalized scalings here
permits the native mark loop to use individual price words without a division by n. -/
theorem physical_motion (s M T : ℝ) (x : Commodity P N k → ℝ) (_positive : 0<T) :
    ∑ v : P × Fin N, ∑ a : Fin k × Bool, s*(rise M (x (.inr (v,a)))/T)^2 = (s/T^2)*readings M x := by
  simp only [readings,Finset.mul_sum,div_pow]
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro a _; ring

private theorem normalized_score {a M T W : ℝ} (x : Commodity P N k → ℝ) (positive : 0<T) (stages : 0<N) :
    score a M (bonus (W⁻¹^4/(N*T^2))) x/Fintype.card P =
     a*(∑ i, (x i)^2)/Fintype.card P+W⁻¹^4*(readings M x/(Fintype.card P*N*T^2)) := by
  rw [score_actual]; field_simp

/-- The native score board, or the independent injection-time payload board, forces
one unit of normalized signed-motion energy. The payload alternative uses only the
commodity strip's `total_readout`, its actual discrepancy charge, and its printed cap. -/
theorem trigger_motion {s r W M T a : ℝ} (x : Commodity P N k → ℝ)
    (hs : 0<s) (s1 : s≤1) (hr : 0<r) (pos : 0<T) (stages : 0<N)
    (quadratic : a*(∑ i, (x i)^2)/Fintype.card P ≤ W⁻¹^4)
    (scale : 2*W⁻¹^4 ≤ W⁻¹^2) (bound : ∀ i : (P×Fin N)×(Fin k×Bool), rise M (x (.inr i))≤1)
    (early : W⁻¹^4*(1+(2*k)/T^2)*r ≤ W⁻¹^2)
    (transfer : readings M x ≤ Fintype.card P*N*T^2 → (∑ p, x (.inl p)) ≤ Fintype.card P)
    (high : envelope W r s < score a M (bonus (W⁻¹^4/(N*T^2))) x/Fintype.card P ∨
      (s=1 ∧ (Fintype.card P:ℝ)<∑ p, x (.inl p))) :
    (Fintype.card (P×Fin N):ℝ) ≤ ∑ v : P × Fin N, ∑ j : Fin k × Bool, s*(rise M (x (.inr (v,j)))/T)^2 := by
  rw [physical_motion s M T x pos]
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  let n := (Fintype.card P:ℝ)
  have npos : 0<n := by dsimp [n]; exact_mod_cast Fintype.card_pos (α:=P)
  have Npos : 0<(N:ℝ) := by exact_mod_cast stages
  have denom : 0<n*N*T^2 := by positivity
  have expansion := normalized_score (a:=a) (M:=M) (W:=W) x pos stages
  rcases high with score | ⟨rfl,payload⟩
  · let energy := readings M x/(n*N*T^2)
    have cap : energy≤(2*k)/T^2 := by
      have one (v : P×Fin N) (j : Fin k×Bool) : (rise M (x (.inr (v,j))))^2 ≤ 1 := by
        have nonneg : 0 ≤ rise M (x (.inr (v,j))) := le_max_right _ _
        nlinarith only [sq_nonneg (1-rise M (x (.inr (v,j)))),mul_self_le_mul_self nonneg (bound (v,j))]
      have all := Finset.sum_le_sum (s:=Finset.univ) fun v _ => Finset.sum_le_sum (s:=Finset.univ) fun j _ => one v j
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_prod,Fintype.card_bool,
        Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at all
      apply (div_le_iff₀ denom).2
      have eq : ((2*k)/T^2)*(n*N*T^2)=n*N*(k*2) := by field_simp
      rw [eq]; exact all
    by_cases after : r≤ s
    · have motion := score_triggers hs s1 hr after scale quadratic expansion score
      have cross : n*N*T^2 < s*readings M x := by
        rw [← mul_div_assoc,lt_div_iff₀ denom,one_mul] at motion
        exact motion
      calc n*N ≤ (s*readings M x)/T^2 := (le_div_iff₀ (sq_pos_of_pos pos)).2 cross.le
           _ = _ := by ring
    · exact False.elim ((not_lt_of_ge (no_small_time_excess hs hr (le_of_not_ge after) quadratic cap early expansion)) score)
  · have mass : n*N*T^2 < readings M x := lt_of_not_ge (fun le => (not_le_of_gt payload) (transfer le))
    calc n*N ≤ readings M x/T^2 := (le_div_iff₀ (sq_pos_of_pos pos)).2 mass.le
         _ = _ := by ring

/-- Uniform early high-excess detection using the actual path price test, sorted by the
physical site names separately on each routed record. The result is the precise unrounded
energy premise for the genuine word-level H-purchase controller. -/
theorem actual_trigger {F : Type*} [Field F] (L k : ℕ) (hk : 0<k) (no : ¬HasSpectralFlat F (k+1))
    {T η : ℝ} (pos : 0<T) (res : 0<η) (bias : ∀ N≤L, η+N*(Real.sqrt (2*k)*η)+N*T≤1/2) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∃ ε : ℝ, 0<ε ∧ ∀ N≤L, 0<N →
    ∀ (P : Type v) [Fintype P] [Nonempty P] (name : P → PayloadStrip.Naming N k) (x : Commodity P N k → ℝ) (a s r W : ℝ),
    0<s → s≤1 → 0<r → (a*(∑ i,(x i)^2)/Fintype.card P ≤ W⁻¹^4) →
    2*W⁻¹^4 ≤ W⁻¹^2 → W⁻¹^4*(1+(2*k)/T^2)*r ≤ W⁻¹^2 →
    (∀ p,PayloadStrip.rowQuotes x p ∈ Set.Icc (0:PayloadStrip.Quotes N k → ℝ) (PayloadStrip.ceiling N k M)) →
    (∑ p,PayloadStrip.namedError F N k (name p) M (PayloadStrip.rowQuotes x p))≤Fintype.card P*ε/(2*(N+1)) →
    (envelope W r s < score a M (bonus (W⁻¹^4/(N*T^2))) x/Fintype.card P ∨ (s=1 ∧ (Fintype.card P:ℝ)<∑ p,x (.inl p))) →
    (Fintype.card (P×Fin N):ℝ) ≤ ∑ v : P×Fin N, ∑ j : Fin k×Bool, s*(rise M (x (.inr (v,j)))/T)^2 := by
  obtain ⟨K,all⟩ := PayloadStrip.all_payload_lengths (F:=F) L k hk no pos.le res bias
  refine ⟨K,?_⟩; intro M large; obtain ⟨ε,he,trans⟩ := all M large
  refine ⟨ε,he,?_⟩; intro N within stages P _ _ name x a s r W hs s1 hr quad wide early box close high
  apply trigger_motion x hs s1 hr pos stages quad wide _ early _ high
  · rintro ⟨⟨p,t⟩,j⟩
    have bounded := (box p).2 (.inr (t,j))
    change x (.inr ((p,t),j))≤M+1 at bounded
    exact max_le (by linarith) zero_le_one
  · exact fun E => trans N within P name x box E close

end
end Hierarchy.AdaptiveProbe

end OAI

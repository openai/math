import OAI.Hierarchy.ProbeSortedActivation

namespace OAI
/-! # Strict reserve activation from real named post-purchase discrepancy readings -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe ChainStrip
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F]

/-- One finite discrepancy cutoff handles every paid root. The nonnegative post-test
charges in the hypothesis are exactly the local ordered wire systems later fed to
histogram replacement when they fail. The conclusion is the signed saving used in
the reserve feed; every bought slot, including every exceptional one, is paid in full. -/
def StrictPayment (F : Type*) [Field F] (depth k : ℕ) (M η ε : ℝ) : Prop :=
    ∀ {h d J : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))
    (global : ColumnSite (StageColumns h d) k ↪ Fin J) (a s B u δ fee ρ : ℝ)
    (old post : Commodity (Fin (2^h)) (permutationFabric h d).shapes.length k → ℝ),
    0≤a → 0≤ s → s≤1 → 0<B → 0<u → 0<ρ → 4*δ^2≤u → η<δ → 1+η<(depth+1:ℕ)*(δ-η) →
    (∀ t c r, r∈marked t c → u ≤ s*(rise M (old (.inr ((r,t),c))))^2) →
    (∀ path j, 0≤postQuote S π depth marked path post j ∧ postQuote S π depth marked path post j≤(M:ℝ)+1) →
    let n : ℕ := 2^h
    let count := Fintype.card (LiveChains S π depth marked)
    let reward := B*u/8
    ρ*n≤count → fee≤reward/2 →
    (∑ path, namedError F depth k (namedStrip S π depth marked global path).name M (postQuote S π depth marked path post))≤(ρ*n/4)*ε →
    0<(n:ℝ)*ρ*reward/4 ∧ 2*(count*fee+n*ρ*reward/4)≤ s*divergence a M (bonus B) old post

/-- Use the particular tolerance already fixed together with the common payload
calibration, before any population, matching or marked path has been selected. -/
theorem strict_activation_of_reads (depth k : ℕ) {M η ε : ℝ} (ep : 0<ε)
    (reads : ∀ ord : Naming depth k, ∀ y ∈ Set.Icc (0:Axes depth k→ℝ) (fun _ => M+1),
      namedError F depth k ord M y≤ε → Reads depth k M η y) : StrictPayment F depth k M η ε := by
  classical
  intro h d J S π marked global a s B u δ fee ρ old post ha hs upper hB hu hρ cal res long markedOld box n count reward many unit total
  let disc (p : LiveChains S π depth marked) := namedError F depth k (namedStrip S π depth marked global p).name M (postQuote S π depth marked p post)
  let bad := Finset.univ.filter (fun p => ε<disc p)
  let accepted := Finset.univ.filter (fun p => ¬ε<disc p)
  have pos (p : LiveChains S π depth marked) : 0≤disc p := by
    apply Real.sInf_nonneg
    rintro _ ⟨q,rfl⟩; exact Probe.testError_nonneg _ _ _ _ _ _
  have markov := exceptional_test_mass disc pos ε
  have badBound : (bad.card:ℝ)≤ρ*n/4 := (le_of_mul_le_mul_right (markov.trans total) ep)
  have cover : bad.card+accepted.card=count := by
    simpa [bad,accepted,count] using (Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun p => ε<disc p))
  have few : (count:ℝ)-accepted.card ≤ ρ*n/4 := by
    have add : (bad.card:ℝ)+(accepted.card:ℝ)=count := by exact_mod_cast cover
    linarith
  have good (p : ↥accepted) : Nonempty (ChainFrame S π depth marked p.val M η post) := by
    have near : disc p.val ≤ ε := le_of_not_gt (Finset.mem_filter.mp p.property).2
    obtain ⟨zi,zo,join,tileRead,probe⟩ := reads (namedStrip S π depth marked global p.val).name _
      ⟨fun j => (box p.val j).1,fun j => (box p.val j).2⟩ near
    exact ⟨⟨zi,zo,join,fun j => (tileRead (j,p.val.2.1)).le,probe.le⟩⟩
  have pay := live_activation S π depth marked (fee:=fee) ha hs upper hB.le cal res long old post markedOld accepted (fun g => (good g).some)
  exact activation_cash (by dsimp [reward]; positivity) (Nat.two_pow_pos h) hρ many few unit pay


theorem strict_activation (depth k : ℕ) (hk : 0<k) (no : ¬HasSpectralFlat F (k+1)) {η : ℝ} (tol : 0<η) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∃ ε : ℝ, 0<ε ∧ StrictPayment F depth k M η ε := by
  obtain ⟨N,uniform⟩ := sorted_reads (F:=F) depth k hk no tol
  refine ⟨N,?_⟩; intro M large; obtain ⟨ε,ep,reads⟩ := uniform M large
  exact ⟨ε,ep,strict_activation_of_reads depth k ep reads⟩

end
end Hierarchy.ProbeStage

end OAI

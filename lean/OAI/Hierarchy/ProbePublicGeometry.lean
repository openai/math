import OAI.Hierarchy.ProbeAdvisedCost
import OAI.Hierarchy.ProbeSortedPayload
import OAI.Hierarchy.ProbeNamedChainReads
import OAI.Hierarchy.ProbePublicTimes

namespace OAI
/-! # One public finite strip calibration before any input size, matching or selector -/

namespace Hierarchy.AdaptiveProbe
open ProbeStage Filter
open scoped BigOperators Classical
noncomputable section

/-- All the advised matching layouts at this scale have precisely this layer count. -/
def publicStages (W : ℕ) := 18*(2^W-1)+1

/-- H is the actual integer number of tiles. The walk enumerator uses H−1 steps. -/
def publicTiles (k W : ℕ) := ⌈32*(k:ℝ)/(dyadicScale W)^2⌉₊

/-- A single height, tolerance and geometric price box work at that public scale
for every row and every purchased strip, including all their different physical
site orderings. Only the affordable geometric scale is chosen cofinally. -/
theorem public_geometry {F : Type*} [Field F] (k : ℕ) (hk : 0<k)
    (no : ¬HasSpectralFlat F (k+1)) {p σ Λ : ℝ} (hp : 1<p) (hσ : 0<σ) (hΛ : 0<Λ) :
    ∀ᶠ W : ℕ in atTop,
    let t := dyadicScale W
    let T := t^2
    let η := T/(100*k)
    let L := publicStages W
    let H := publicTiles k W
    0<H ∧ Λ*t^σ≤1 ∧ Λ*(1+2*k)*(L:ℝ)*t^p≤1 ∧ 64*k*Λ*(W:ℝ)^4*(L:ℝ)*t^p≤1 ∧
    ∃ M₀ : ℕ, ∀ M≥M₀, ∃ ε : ℝ, 0<ε ∧
      (∀ (P : Type) [Fintype P] (name : P→PayloadStrip.Naming L k) (x : Commodity P L k → ℝ),
        (∀ i,PayloadStrip.rowQuotes x i ∈ Set.Icc (0:PayloadStrip.Quotes L k → ℝ) (PayloadStrip.ceiling L k M)) →
        readings M x ≤ Fintype.card P*(L:ℝ)*T^2 →
        (∑ i,PayloadStrip.namedError F L k (name i) M (PayloadStrip.rowQuotes x i)) ≤ Fintype.card P*ε/(2*(L+1)) →
        (∑ i,x (.inl i))≤Fintype.card P) ∧
      ∀ (ord : ChainStrip.Naming (H-1) k) (y : ChainStrip.Axes (H-1) k → ℝ),
        y ∈ Set.Icc 0 (fun _ => (M:ℝ)+1) → ChainStrip.namedError F (H-1) k ord M y≤ε →
        ChainStrip.Reads (H-1) k M η y := by
  filter_upwards [affordable_advised hp hσ hΛ (by norm_num : (0:ℝ)<1/4) k] with W cheap
  let t := dyadicScale W
  let T := t^2
  let η := T/(100*k)
  let L := publicStages W
  let H := publicTiles k W
  have charges := cheap 0 (Equiv.refl (Fin (2^0)))
  simp only [advised_length] at charges
  have nt : (L:ℝ)*T≤1/4 := charges.2.2.2
  have tpos : 0<t := by dsimp [t,dyadicScale]; positivity
  have small : t≤1 := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num)
  have tcap : T≤1 := pow_le_one₀ tpos.le small
  have pos : 0<T := by dsimp [T]; positivity
  have rk : 0<(k:ℝ) := by exact_mod_cast hk
  have eta : 0<η := by dsimp [η]; positivity
  have Hpos : 0<H := Nat.ceil_pos.mpr (by dsimp [T,t] at pos; change 0<32*(k:ℝ)/(dyadicScale W)^2; positivity)
  have bias := payload_resolution L k hk pos.le tcap nt
  obtain ⟨a,abase⟩ := PayloadStrip.payload_mean_le_one (F:=F) L k hk no pos.le eta bias
  obtain ⟨b,bbase⟩ := ChainStrip.sorted_reads (F:=F) (H-1) k hk no eta
  refine ⟨Hpos,charges.1,charges.2.1,charges.2.2.1,max a b,?_⟩
  intro M lower
  obtain ⟨u,hu,au⟩ := abase M ((le_max_left ..).trans lower)
  obtain ⟨v,hv,bv⟩ := bbase M ((le_max_right ..).trans lower)
  refine ⟨min u v,lt_min hu hv,?_,?_⟩
  · intro P _ name x box E sum
    apply au P name x box E (sum.trans ?_)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (min_le_left u v) (Nat.cast_nonneg _)
  · intro ord y box close; exact bv ord y box (close.trans (min_le_right u v))

end
end Hierarchy.AdaptiveProbe

end OAI

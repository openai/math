import OAI.Hierarchy.ProbePublicStageCount
import OAI.Hierarchy.ProbeObservedReplay
import OAI.Hierarchy.ProbePublicCalibration
import OAI.Hierarchy.ProbeMarkedQuotes

namespace OAI
/-! # Payment on the actual frozen shelf and the later replay score at the printed constants -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open scoped BigOperators Classical
noncomputable section

/-- All cutoff, fee, eligibility and geometric curvature data in an inner advance
come from the public calibration and the actual frozen signed-stock purchase. -/
theorem physical_payment {F : Type*} [Field F] {z d k W M J Q q e : ℕ} {p σ Λ ε : ℝ}
    (cfg : PublicCalibration F k p σ Λ W M ε) (hk : 0<k) (hd : d=2^W)
    (a s s' : ℝ) (ha : 0<a) (hs : 0<s) (s₁ : s≤1) (later : 0<s')
    (width precision : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (frozen post : Shelf.Mem z d) (postBase : ℕ)
    (global : ColumnSite (StageColumns z d) k ↪ Fin J)
    (C : Chart (wordBits z d copies) q e) (mem : Shelf.Mem z d) (phase trial slice bid : ℕ)
    (room : 2^z≤2^(wordBits z d copies))
    (fit : ∀ (v : Σ _ : StageAt z d, Fin (2^z)) (axis : Fin k×Bool),
      PurchaseInventory.stock sh.stockBase frozen (.inr ((v.2,stageNumber v.1),axis))<sh.table.size)
    (hQ : 0<Q) (space : TestRoom (repair C (.inner phase trial slice bid)) (wordBits z d copies))
    (advance : observedInnerMode C mem phase trial slice bid=1) :
    let N := publicStages W
    let T := probeHeat W
    let H := publicTiles k W
    let ρ := probeDensity k W
    let oldPhase := publicPhase (2*rounds d+1) a M W T s width precision
    let laterPhase := publicPhase (2*rounds d+1) a M W T s' width precision
    let marks := StripDirectory.actualMarks sh oldPhase T 1 frozen (k:=k)
    let old := stageQuotes oldPhase 0 1 sh.stockBase frozen
    let after := stageQuotes laterPhase 0 1 postBase post
    let check := replayCheck C phase trial slice bid
    let n := 2^z
    let live := Fintype.card (LiveChains S π (H-1) marks)
    ρ*n≤live → check.bound=⌈4*failureTolerance N ε ρ*n*Q⌉₊ →
    ∀pick : LiveChains S π (H-1) marks ↪ Fin check.rows,
    (∀path, ChainStrip.namedError F (H-1) k (namedStrip S π (H-1) marks global path).name M
      (postQuote S π (H-1) marks path after) ≤ (check.score (replayScoreMemory C mem phase trial slice bid) (pick path):ℝ)/Q+failureTolerance N ε ρ) →
    2*((live:ℝ)*(Λ*(dyadicScale W)^p)+(n:ℝ)*ρ*(probeBonus W*probeMotion k W/8)/4) ≤
      s*divergence a M (bonus (probeBonus W)) old after := by
  intro N T H ρ oldPhase laterPhase marks old after check n live many bound pick measured
  have population : n = ((2^z : ℕ) : ℝ) := by simp [n]
  rw [population] at many bound ⊢
  have stageN : (permutationFabric z d).shapes.length=N := by rw [hd]; exact fixed_stage_count z W
  have dyadic : 0<dyadicScale W := by unfold dyadicScale; positivity
  have temp : 0<T := pow_pos dyadic 2
  have tcap : T≤1 := pow_le_one₀ dyadic.le
    (pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num))
  have kp : 0<(k:ℝ) := Nat.cast_pos.mpr hk
  have np : 0<(N:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have wp : 0<(W:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<9) ((le_max_left ..).trans cfg.wide))
  have hp : 0<H := cfg.tiles
  have size : H-1+1=H := by omega
  have counts : (permutationFabric z d).shapes.length≤H-1+1 := by rw [stageN,size]; exact stages_le_purchase N k hk temp cfg.motion_mass
  have bb : 0<probeBonus W := by unfold probeBonus; positivity
  have uu : 0<probeMotion k W := by unfold probeMotion; positivity
  have rr : 0<ρ := by dsimp [ρ,probeDensity]; positivity
  obtain ⟨compare,near,long⟩ := purchase_constants k hk temp tcap
  refine acquired_payment C mem phase trial slice bid cfg.purchase S π marks
    (StripDirectory.actualMarks_unique sh oldPhase T 1 frozen) counts global a s (probeBonus W) (probeMotion k W)
    (T/(4*k)) _ ρ old after ha.le hs.le s₁ bb uu rr compare near ?_ ?_ ?_ many cfg.acquisition_fee
    cfg.accurate hQ space advance bound pick measured
  · rw [size]; exact long
  · intro t c r hit
    exact StripDirectory.actualMarks_paid sh oldPhase T 0 1 frozen temp room fit t c r hit
  · intro path j
    have box := public_post_quotes (M:=(M:ℝ)) (W:=(W:ℝ)) (T:=T) ha (Nat.cast_nonneg M) later width precision postBase post S π (H-1) marks path
    exact ⟨box.1 j,box.2 j⟩

end
end Hierarchy.ProtocolRAM.Calendar

end OAI

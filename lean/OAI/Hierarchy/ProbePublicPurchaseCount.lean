import OAI.Hierarchy.ProbePhysicalMotion
import OAI.Hierarchy.ProbePublicStageCount
import OAI.Hierarchy.ProbePublicPrices
import OAI.Hierarchy.ProbePublicCalibration
import OAI.Hierarchy.ProtocolRAMPurchaseLiveCount

namespace OAI
/-! # A common sampler and the exact live-chain mass of the measured outer decision -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open scoped Fin.CommRing BigOperators Classical
noncomputable section

/-- The typed set on the right is the very source of the opposite-end divergence
and the native purchase count. Its linear size follows directly from the actual
frozen price-bank energy, with one sampler for all heights and all permutations. -/
theorem live_density_of_advised {F : Type*} [Field F] {k W M : ℕ} {p σ Λ ε : ℝ}
    (cfg : PublicCalibration F k p σ Λ W M ε) (hk : 0<k) (S : PurchaseSampler)
    (enough : AdvisedCoverage S (2^W) k (publicTiles k W-1) (probeHeat W)) :
    let d := 2^W
    let T := probeHeat W
    let depth := publicTiles k W-1
    ∀ᶠ z : ℕ in Filter.atTop, ∀ (π : Equiv.Perm (Fin (2^z))) (sh : Shelf)
      (a s : ℝ) (width precision : ℕ) (raw fixture : Shelf.Mem z d),
      let phase := publicPhase (2*rounds d+1) a M W T s width precision
      let marked := StripDirectory.actualMarks sh phase T 1 raw (k:=k)
      let x := stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 sh.stockBase raw
      0<a → 0<s → s≤1 → sh.Incoming (k:=k) S π depth phase T 1 raw →
      (∀ i : Key z d k,sh.Prepared S depth fixture i raw) →
      sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies →
      (∀ v j,stockBits sh.stockBase k raw v j<sh.table.size) →
      ((Fintype.card (Fin (2^z) × Fin (2*rounds d+1)):ℝ) ≤ ∑v,∑j : Fin k×Bool,s*(rise M (x (.inr (v,j)))/T)^2) →
      (sh.program S z d k depth).Exec raw (sh.result S k depth raw) (sh.clock S z d k depth) ∧
      sh.packedCount S k depth (sh.result S k depth raw)=Fintype.card (LiveChains S π depth marked) ∧
      probeDensity k W*(2^z:ℕ)≤Fintype.card (LiveChains S π depth marked) := by
  intro d T depth
  have scale : 0<T := by dsimp [T,probeHeat,dyadicScale]; positivity
  have hd : 1≤d := Nat.two_pow_pos W
  have all:=PurchaseFrozen.Shelf.acquire_of_advised d k depth hd hk T scale S enough
  filter_upwards [all] with z good
  intro π sh a s width precision raw fixture phase marked x ha hs early incoming initial room stock energy
  have native := (measured_motion (z:=z) (d:=d) (k:=k) phase 0 1 sh.stockBase raw T).mp energy
  have cap (v : Tile z d) (j : Fin k×Bool) : rise phase.M (phase.quote 1 (stockBits sh.stockBase k raw v j))≤1 := by
    have quoted := (public_quote_mem (W:=(W:ℝ)) (T:=T) ha (Nat.cast_nonneg M) hs (2*rounds d+1) width precision 1 (stockBits sh.stockBase k raw v j)).2
    have priced : phase.quote 1 (stockBits sh.stockBase k raw v j)≤(M:ℝ)+1 := by simpa [phase] using quoted
    change max (_-(M:ℝ)) 0≤1
    exact max_le (by linarith) (by norm_num)
  obtain ⟨run,_,many⟩ := good π sh phase 1 raw fixture incoming initial room hs.le early stock cap native
  have counted := sh.packedCount_liveChains_result S π depth hd phase T 1 raw fixture incoming initial room
  refine ⟨run,counted,?_⟩
  have size : depth+1=publicTiles k W := by dsimp [depth]; have := cfg.tiles; omega
  calc
    _ = T^2/(4*k)*((publicStages W:ℝ)*(2:ℝ)^z)/(2*(publicTiles k W:ℝ)) := by
      dsimp [probeDensity,probeMotion,T]; push_cast; ring
    _ = T^2/(4*k)*(((permutationFabric z d).shapes.length:ℝ)*(2:ℝ)^z)/
        (2*((depth+1:ℕ):ℝ)) := by rw [fixed_stage_count z W, size]
    _ ≤ _ := many.trans_eq (congrArg (fun i : ℕ => (i : ℝ)) counted)

theorem live_density_positive {F : Type*} [Field F] {k W M : ℕ} {p σ Λ ε : ℝ}
    (cfg : PublicCalibration F k p σ Λ W M ε) (hk : 0<k) :
    let d := 2^W
    let T := probeHeat W
    let depth := publicTiles k W-1
    ∃ S : PurchaseSampler, 0<S.degree ∧ ∀ᶠ z : ℕ in Filter.atTop, ∀ (π : Equiv.Perm (Fin (2^z))) (sh : Shelf)
      (a s : ℝ) (width precision : ℕ) (raw fixture : Shelf.Mem z d),
      let phase := publicPhase (2*rounds d+1) a M W T s width precision
      let marked := StripDirectory.actualMarks sh phase T 1 raw (k:=k)
      let x := stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 sh.stockBase raw
      0<a → 0<s → s≤1 → sh.Incoming (k:=k) S π depth phase T 1 raw →
      (∀ i : Key z d k,sh.Prepared S depth fixture i raw) →
      sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies →
      (∀ v j,stockBits sh.stockBase k raw v j<sh.table.size) →
      ((Fintype.card (Fin (2^z) × Fin (2*rounds d+1)):ℝ) ≤ ∑v,∑j : Fin k×Bool,s*(rise M (x (.inr (v,j)))/T)^2) →
      (sh.program S z d k depth).Exec raw (sh.result S k depth raw) (sh.clock S z d k depth) ∧
      sh.packedCount S k depth (sh.result S k depth raw)=Fintype.card (LiveChains S π depth marked) ∧
      probeDensity k W*(2^z:ℕ)≤Fintype.card (LiveChains S π depth marked) := by
  intro d T depth
  have scale : 0<T := by dsimp [T,probeHeat,dyadicScale]; positivity
  have hd : 1≤d := Nat.two_pow_pos W
  let : Nonempty (Fin (2*k)) := ⟨⟨0,by omega⟩⟩
  have kp : 0<(k:ℝ) := by exact_mod_cast hk
  obtain ⟨S,deg,enough⟩ := advised_purchases_linear_positive (C:=Fin (2*k)) hd depth (β:=T^2/(4*k)) (by positivity)
  exact ⟨S,deg,live_density_of_advised cfg hk S enough⟩

theorem live_density {F : Type*} [Field F] {k W M : ℕ} {p σ Λ ε : ℝ}
    (cfg : PublicCalibration F k p σ Λ W M ε) (hk : 0<k) :
    let d := 2^W
    let T := probeHeat W
    let depth := publicTiles k W-1
    ∃ S : PurchaseSampler, ∀ᶠ z : ℕ in Filter.atTop, ∀ (π : Equiv.Perm (Fin (2^z))) (sh : Shelf)
      (a s : ℝ) (width precision : ℕ) (raw fixture : Shelf.Mem z d),
      let phase := publicPhase (2*rounds d+1) a M W T s width precision
      let marked := StripDirectory.actualMarks sh phase T 1 raw (k:=k)
      let x := stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 sh.stockBase raw
      0<a → 0<s → s≤1 → sh.Incoming (k:=k) S π depth phase T 1 raw →
      (∀ i : Key z d k,sh.Prepared S depth fixture i raw) →
      sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies →
      (∀ v j,stockBits sh.stockBase k raw v j<sh.table.size) →
      ((Fintype.card (Fin (2^z) × Fin (2*rounds d+1)):ℝ) ≤ ∑v,∑j : Fin k×Bool,s*(rise M (x (.inr (v,j)))/T)^2) →
      (sh.program S z d k depth).Exec raw (sh.result S k depth raw) (sh.clock S z d k depth) ∧
      sh.packedCount S k depth (sh.result S k depth raw)=Fintype.card (LiveChains S π depth marked) ∧
      probeDensity k W*(2^z:ℕ)≤Fintype.card (LiveChains S π depth marked) := by
  intro d T depth
  obtain ⟨S,_,proper⟩ := live_density_positive cfg hk
  exact ⟨S,proper⟩

end
end Hierarchy.ProtocolRAM.Calendar

end OAI

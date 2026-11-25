import OAI.Hierarchy.ProbeFixedFormatCore
import OAI.Hierarchy.ProbePublicPurchaseCount

namespace OAI
/-! # The original public format on the actual native shelf and price memories -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen StripDirectory
open scoped BigOperators Classical
noncomputable section

def SamplerCoverage (k W M : ℕ) (S : PurchaseSampler) : Prop :=
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
      probeDensity k W*(2^z:ℕ)≤Fintype.card (LiveChains S π depth marked)
namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

theorem path_coverage : SamplerCoverage k v.W v.radius v.sampler :=
  live_density_of_advised v.geometry v.positive v.sampler v.advised

theorem small_score :
    ∀ z d w : ℕ,2*rounds d+1=publicStages v.W → ∀ T s : ℝ,0<s → ∀ bits precision base : ℕ,∀mem : Memory w,
      let phase := publicPhase (publicStages v.W) v.a v.radius v.W T s bits precision
      let x := stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 base mem
      (v.a:ℝ)*(∑i,x i^2)/(2:ℝ)^z ≤ (v.W:ℝ)⁻¹^4 :=
  public_quadratic_receipt (publicStages v.W) k (Nat.cast_nonneg _) v.a v.quadratic_pos v.quadratic_box

end FixedProtocolFormat
end
end Hierarchy.ProtocolRAM.Calendar

end OAI

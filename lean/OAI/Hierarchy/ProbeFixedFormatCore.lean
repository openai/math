import OAI.Hierarchy.ProbePositiveSampler
import OAI.Hierarchy.ProbePublicStageCount
import OAI.Hierarchy.ProbePublicCalibration
import OAI.Hierarchy.ProbeNativeMesh
import OAI.Hierarchy.ProbeShapeMenus
import OAI.Hierarchy.TaggedShorterChoice

namespace OAI
/-! # A fixed public format for all widths and all private selectors -/

namespace Hierarchy.ProtocolRAM.Calendar
open AdaptiveProbe ProbeStage StripDirectory
open scoped BigOperators Classical
noncomputable section

/-- The actual tree used for a selector consists of the horizontal spine and
all of its signed radial links, with price at most `max M 1` each. -/
def boardCost (N depth k M : ℕ) : StripChart.TreeCosts where
  payload := (Fintype.card (Strip.TreeLink (PayloadStrip.edgeCount N) k):ℝ)*max (M:ℝ) 1
  purchase := (Fintype.card (Strip.TreeLink (ChainStrip.edgeCount depth) k):ℝ)*max (M:ℝ) 1
  payload_nonneg := by positivity
  purchase_nonneg := by positivity

def menuOfShape (F : Type*) [Field F] (N depth k : ℕ) (hk : 0<k) (M : ℕ) (cut : ℝ) (hc : 0<cut) :=
  letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,hk⟩⟩
  letI : Nonempty (PurchasedRole depth k) := ⟨.catalyst (ChainStrip.inlet depth 0) ⟨0,hk⟩⟩
  let cost := boardCost N depth k M
  let a := payloadMenu F N k hk M (Nat.cast_nonneg M) cut hc cost.payload cost.payload_nonneg 0
  let b := purchasedMenu F depth k hk M (Nat.cast_nonneg M) cut hc cost.purchase cost.purchase_nonneg 0
  (PacketWidths.ofMenu a).either (PacketWidths.ofMenu b)

def upperBox (N M : ℕ) : ℝ := max (N:ℝ) ((M:ℝ)+1)
def repairShare (N M : ℕ) (cut : ℝ) : ℝ := cut/(wallCap M (upperBox N M)+1)
def purchaseReward (k W : ℕ) := probeBonus W*probeMotion k W/8

/-- Independent of any permutation, width, private selector or height. Both
catalogues, all fixed time meshes and the positive sampler are selected at once.
The same sampler supplies the true bought path count on every foreign history. -/
structure FixedProtocolFormat (F : Type*) [Field F] (k : ℕ) (p q Q σ Λ : ℝ) where
  positive : 0<k
  power : 1<p
  exponents : 0<q ∧ q<Q
  scaleExponent : 0<σ
  capacityPrice : 0<Λ
  W : ℕ
  radius : ℕ
  tolerance : ℝ
  geometry : PublicCalibration F k p σ Λ W radius tolerance
  sampler : PurchaseSampler
  sampler_live : 0<sampler.degree
  advised : AdvisedCoverage sampler (2^W) k (publicTiles k W-1) (probeHeat W)
  a : ℚ
  quadratic_pos : 0<a
  quadratic_box : (a:ℝ)*(1+2*(publicStages W)*k:ℕ)*(upperBox (publicStages W) radius)^2≤(W:ℝ)⁻¹^4
  finish : ℚ
  mesh : Mesh
  precision : ℕ
  copyScale : ℕ
  widthFloor : ℕ
  clock : let N := publicStages W
    let cut := failureTolerance N tolerance (probeDensity k W)
    let menu := menuOfShape F N (publicTiles k W-1) k positive radius cut geometry.cutoff.1
    ClockCalibration.{0} menu N k a (probeBonus W) (upperBox N radius) cut (repairShare N radius cut)
      (probeDensity k W) (purchaseReward k W) (Λ*(dyadicScale W)^p) finish mesh precision copyScale widthFloor

/-- Construct one literal fixed format for every tuple in the paper, with the
actual named packet menus for the two sorts of local price test. -/
theorem fixed_format (F : Type*) [Field F] (k : ℕ) (hk : 0<k) (missing : ¬HasSpectralFlat F (k+1))
    {p q Q σ Λ : ℝ} (hp : 1<p) (hq : 0<q) (hQ : q<Q) (hσ : 0<σ) (hΛ : 0<Λ) :
    Nonempty (FixedProtocolFormat F k p q Q σ Λ) := by
  obtain ⟨W,M₀,scope⟩ := (public_calibration (F:=F) k hk missing hp hσ hΛ).exists
  obtain ⟨ε,cfg⟩ := scope M₀ le_rfl
  have hw : 0<(W:ℝ) := by exact_mod_cast (show 0<W from (by have := cfg.wide;omega))
  obtain ⟨a,ha,small⟩ := small_quadratic_price (R:=(1+2*(publicStages W)*k:ℕ))
    (A:=upperBox (publicStages W) M₀) hw (by positivity)
  let N := publicStages W
  let cut := failureTolerance N ε (probeDensity k W)
  have hc : 0<cut := cfg.cutoff.1
  have time : 0<dyadicScale W := by unfold dyadicScale; positivity
  have hot : 0<probeHeat W := pow_pos time 2
  have kp : 0<(k:ℝ) := Nat.cast_pos.mpr hk
  have np : 0<(publicStages W:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have H : 0<(publicTiles k W:ℝ) := Nat.cast_pos.mpr cfg.tiles
  have motion : 0<probeMotion k W := by unfold probeMotion; positivity
  have β : 0<probeBonus W := by unfold probeBonus; positivity
  let : Nonempty (Fin (2*k)) := ⟨⟨0,by omega⟩⟩
  have ratio : 0<(probeHeat W)^2/(4*k) := by positivity
  obtain ⟨S,real,coverage⟩ := advised_purchases_linear_positive (C:=Fin (2*k)) (d:=2^W) (Nat.two_pow_pos W)
    (publicTiles k W-1) ratio
  have dens : 0<probeDensity k W := by unfold probeDensity; positivity
  let U := upperBox N M₀
  have u : 0≤U := (Nat.cast_nonneg N).trans (le_max_left ..)
  have wall : 0<wallCap M₀ U+1 := by unfold wallCap; positivity
  have frac : 0<repairShare N M₀ cut := div_pos hc wall
  have reward : 0<purchaseReward k W := by unfold purchaseReward; positivity
  let menu := menuOfShape F N (publicTiles k W-1) k hk M₀ cut hc
  obtain ⟨s,c,Q₀,K,floor,clocks⟩ := clock_calibration.{0} menu N k a (probeBonus W) U cut (repairShare N M₀ cut)
    (probeDensity k W) (purchaseReward k W) (Λ*(dyadicScale W)^p) (by exact_mod_cast ha) β.le u hc frac dens reward
  exact ⟨⟨hk,hp,⟨hq,hQ⟩,hσ,hΛ,W,M₀,ε,cfg,S,real,coverage,a,ha,small,s,c,Q₀,K,floor,clocks⟩⟩

theorem cofinal_formats (F : Type*) [Field F] (k : ℕ) (hk : 0<k) (missing : ¬HasSpectralFlat F (k+1)) :
    TaggedShorterBudget.Cofinal (fun p q Q σ Λ=>Nonempty (FixedProtocolFormat F k p q Q σ Λ)) :=
  TaggedShorterBudget.Cofinal.of_all (fun _ _ _ _ _ hp hq hQ hσ hΛ=>fixed_format F k hk missing hp hq hQ hσ hΛ)


end
end Hierarchy.ProtocolRAM.Calendar

end OAI

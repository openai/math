import OAI.Computability.BorderVNP.PackedSignedSeedDecay
import OAI.Computability.BorderVNP.DiagonalJointPlacement
import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedLayout

/-! # The signed shortening processor fits the cube's full crossing budget

Each paired interval is one cable. Counting its two incidences gives twice its width,
so the complete exterior adds at most half the total per-team exterior allowance.
The reduced-cell crossings of the internal network are exactly the active terminal
width measured along the same compiled history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch Shortening Adaptive Packing PhysicalEpochs DeckGrid
open Diagonal Diagonal.ExternalSew TeamContraction TeamScales Filter EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
    {n r d T copies headerFactor Q R ell : ℕ}
local notation "axes" => Fintype.card (Cube D)
local notation "seedBits" => fun _ : Fin (GridHosts.tileCount axes d) => copies*GridHosts.inputBlockWidth r n axes d
local notation "admit" => Boundary.Good (S := S) (start := d+1) (bits := seedBits)
  (shape := boundaryShape S (d+1)) (w := 60*logWidth r n) (boundaryBudget S (initialMass (D := D) n r d copies headerFactor))

namespace SeedPlan

variable (plan : SeedPlan S n r d T copies headerFactor Q)

/-- Widths of both the actual flattened and the sewn terminal at the exact signed seed state.
The public words, factor tables, admissibility witness and selected history may all vary. -/
def SewnWidths (count : (fan S)^T*copies = R+1) (ell X : ℕ) (δ : ℝ) : Prop :=
  ∀ {t pins inner : ℕ} {Edge : Type} (G : Wiring R r t pins ell inner n Edge)
    (order : Fin (GridHosts.tileCount axes d) ≃ (Fin axes → Deck (d+2)))
    (pos : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (table : (seedBundle G axes d order pos copies).Tables K)
    (words : Boundary.Pins S (d+1) (boundaryShape S (d+1)) (60*logWidth r n) 0 → Bool)
    (ready : admit 0 (Boundary.seedState S G d order pos copies table words)),
    let bottom : Admissible admit 0 := ⟨_,ready⟩
    let M := plan.compiled.machine
    ∀ q : (packHistory bottom M.epoch T).Index,
    let state := ((packHistory bottom M.epoch T).term q).val
    let cell (v : state.pack.layout.Site) := reduceMove (depth S (d+1) T) (state.route.origin v)
    let sewn := enrichedSewnLayout G axes d order pos count M bottom rfl q
    (intercellWidth (flattenPack T state.pack).layout cell : ℝ) ≤ δ*(R+1:ℕ)*X ∧
      (intercellWidth sewn cell : ℝ) ≤ (δ+1/2)*(R+1:ℕ)*X ∧
      (δ ≤ 1/2 → intercellWidth sewn cell ≤ (R+1)*X)

/-- The total prewiring bound, the true initial cover and the scalar decay estimate pay
for all crossing widths on every history of this signed plan. -/
theorem sewnWidths_of_decay {τ δ : ℝ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hc : 0 < copies) (hτ : 0 ≤ τ)
    (count : (fan S)^T*copies = R+1) (X : ℕ) (linkFit : r*R*ell ≤ X)
    (parse : (batchVolume n r:ℝ) ≤ volume τ r n)
    (site : (CoverScale.sites (Cube D) (d+1):ℝ) ≤ r*(n:ℝ)^(9/10:ℝ))
    (decay : let A := ((1+2*S.weight)*Fintype.card (Direction axes)*(96*(4*axes+1)+1):ℝ)
      A*volume τ r n*(logWidth r n:ℝ)^3/2^T + 2*S.error*r*(n:ℝ)^(9/10:ℝ) ≤ δ*X) :
    plan.SewnWidths count ell X δ := by
  intro t pins inner Edge G order pos table words ready bottom M q state cell sewn
  let L := (flattenPack T state.pack).layout
  have seed := Boundary.seed_exactCrossings S G order pos copies table
  have raw := plan.compiled.history_intercellWidth bottom seed T q
  have start := Boundary.seed_initialPotential S G order pos copies hn hr hc hτ site parse table
  have cap := M.normalizedPotential bottom hc T q
  have measured : state.route.nonlocalWidth ≤ state.route.potential S.weight :=
    le_add_of_nonneg_right (mul_nonneg S.weight_pos.le state.route.nonneg_width_concentration.2)
  have inside : state.route.nonlocalWidth / ((copies:ℝ)*(fan S:ℝ)^T) ≤ δ*X := by
    apply (div_le_div_of_nonneg_right measured (by positivity)).trans (cap.trans _)
    apply le_trans _ decay
    refine add_le_add (div_le_div_of_nonneg_right start (by positivity)) ?_
    have h := mul_le_mul_of_nonneg_left site (show 0 ≤ 2*S.error by linarith [S.error_pos])
    simpa only [mul_assoc] using h
  have denom : (copies:ℝ)*(fan S:ℝ)^T = (R+1:ℕ) := by exact_mod_cast (Nat.mul_comm copies ((fan S)^T)).trans count
  rw [denom] at inside
  have before : (intercellWidth L cell : ℝ) ≤ δ*(R+1:ℕ)*X := by
    calc
      _ = state.route.nonlocalWidth := raw
      _ ≤ δ*X*(R+1:ℕ) := (div_le_iff₀ (by positivity)).mp inside
      _ = _ := by ring
  let hosts := enrichedBlockHosts G axes d order pos count M bottom rfl q
  let w := G.program.length+t
  let g := GridHosts.inputBlockWidth r n axes d
  have total : 2*(∑ c : Cables R r w ell g, cableWidth c) = (R+1)*(r*R*ell) :=
    twice_physical_width (R := R) (r := r) w (2*w+R*ell) ell g
  have twice : 2*intercellWidth sewn cell ≤ 2*intercellWidth L cell+(R+1)*X := by
    have physical : intercellWidth sewn cell ≤ intercellWidth L cell+∑ c : Cables R r w ell g, cableWidth c :=
      hosts.bundle.intercell_le cell
    have ext := Nat.mul_le_mul_left (R+1) linkFit
    omega
  have final : (intercellWidth sewn cell:ℝ) ≤ (δ+1/2)*(R+1:ℕ)*X := by
    have cap' := (Nat.cast_le (α := ℝ)).mpr twice
    push_cast at cap' before ⊢
    linarith only [cap',before]
  refine ⟨before,final,fun hd => ?_⟩
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_mul]
  exact final.trans (by
    calc
      _ ≤ (1:ℝ)*(R+1:ℕ)*X := by gcongr; linarith
      _ = _ := by rw [one_mul])

end SeedPlan
end PackedHistoryCircuit.Normalized.SelectedSchedule

namespace Diagonal

open Crossing Cover BorderVNP.Epoch Shortening Packing DeckGrid TeamScales Filter ExternalSew
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {scales : EpochScales S a extra}

/-- Every signed processor plan at the joint schedule's already chosen length has the full
cube crossing budget. The threshold precedes the private verifier, its table, and the native
histogram. Taking δ at most one half gives the integral allowance without an additional factor. -/
theorem JointSchedule.eventually_signedSewnWidths (b : JointSchedule.{u} scales E deg Q A B j) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
    let r := stretch b.ρ n
    let d := CoverScale.initialDepth (Cube D) r n-1
    let T := epochs scales.τ n
    let copies := TeamScales.width n scales.α
    let R := b.physical.teamsPred n
    ∀ header work : ℕ, ∀ plan : SeedPlan S n r d T copies header work,
      ∃ count : (fan S)^T*copies = R+1,
        plan.SewnWidths count (b.physical.link n) (exterior ((scales.τ:ℝ)/5) r n) δ := by
  have tau : 0 < (scales.τ:ℝ) := by exact_mod_cast scales.tau_pos
  let axes := Fintype.card (Cube D)
  let C := ((1+2*S.weight)*Fintype.card (Direction axes)*(96*(4*axes+1)+1):ℝ)
  have hC : 0 ≤ C := by
    have hw : 0 ≤ 1+2*S.weight := by linarith [S.weight_pos]
    dsimp only [C]
    positivity
  have ht : (scales.τ:ℝ) < 1/2 := by linarith [scales.alpha_small,scales.tau_small]
  filter_upwards [b.eventually_lengths 0,Boundary.eventually_seed_decay tau ht C S.error δ hC hδ,
    eventually_ge_atTop 1] with n length decay hn
  intro r d T copies R header work plan
  have hr : 1 ≤ r := stretch_one ..
  have count : (fan S)^T*copies = R+1 := (Nat.mul_comm ..).trans (b.sizes hn).1.symm
  have linkFit : r*R*b.physical.link n ≤ exterior ((scales.τ:ℝ)/5) r n := by
    rw [(b.sizes hn).2.1,← (b.sizes hn).1]
    exact physical_exterior_le _ R r n
  have hd : d+1 = CoverScale.initialDepth (Cube D) r n := by
    have pos : 1 ≤ CoverScale.initialDepth (Cube D) r n := Nat.succ_pos _
    dsimp only [d]
    omega
  have copies_pos : 0 < copies := by
    by_contra! hc
    simp [Nat.eq_zero_of_le_zero hc] at count
  refine ⟨count,plan.sewnWidths_of_decay hn hr copies_pos tau.le count _ linkFit length.parse ?_
    (decay r hr length.parse)⟩
  rw [hd]
  exact length.cover.2.2.2.1

end Diagonal

end BorderVNP
end Computability
end OAI

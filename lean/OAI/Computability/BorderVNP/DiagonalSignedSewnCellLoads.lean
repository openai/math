import OAI.Computability.BorderVNP.DiagonalExternalSewSeedBounds
import OAI.Computability.BorderVNP.PackedHistoryNormalizedGridBirth
import OAI.Computability.BorderVNP.DiagonalJointSeedStorage
import OAI.Computability.BorderVNP.DiagonalExternalSewScale

/-! # The two per-cell record thresholds on the selected signed seed history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch Shortening Shortening.Adaptive Packing PhysicalEpochs DeckGrid
open Diagonal Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction TeamScales EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP Shortening.PreparedBins
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
    {n r d T copies headerFactor Q R : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "g₀" => GridHosts.inputBlockWidth r n axes d
local notation "seedBits" => fun _ : Fin tiles => copies*g₀
local notation "admit" => Boundary.Good (S := S) (start := d+1) (bits := seedBits)
  (shape := boundaryShape S (d+1)) (w := 60*logWidth r n) (boundaryBudget S (initialMass (D := D) n r d copies headerFactor))
local notation "degree" => Fintype.card (DeckGrid.Direction axes)
local notation "cap" => seedBoxCapacity n r axes d degree
local notation "dB" => seedDescriptionWidth n r axes d (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)

/-- On every reachable signed branch, the public records and expanded work of its wired
birth metadata meet the two prescribed thresholds on each final reduced tile after sewing. -/
def SewnCellLoads (count : (fan S)^T*copies = R+1) (ell : ℕ) : Prop :=
  ∀ {t pins inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring R r t pins ell inner n Edge)
    (order : Fin tiles ≃ (Fin axes → Deck (d+2)))
    (pos : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {g : ℕ} {len : Fin n} {state : Fin g} (W : WiredWitness G len D axes d order state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G axes d order pos copies).Tables K)
    (words : Boundary.Pins S (d+1) (boundaryShape S (d+1)) (60*logWidth r n) 0 → Bool)
    (ready : admit 0 (Boundary.seedState S G d order pos copies table words)),
    let bottom : Admissible admit 0 := ⟨_,ready⟩
    let M := plan.compiled.machine
    ∀ q : (packHistory bottom M.epoch T).Index, ∀ tile : Cube D → Deck (depth S (d+1) T+1),
    let output := ((packHistory bottom M.epoch T).term q).val
    let data := Boundary.seedBirthFields W pos tag sites edges ports copies dB
    let records := fun ex => M.historyFields bottom (data ex) T q
    let sewn := enrichedSewnLayout G axes d order pos count M bottom rfl q
    let load := fun ex => localRecords sewn ex (records ex).prior (records ex).payload
      (fun v => reduceMove (depth S (d+1) T) (output.route.origin v) = tile)
    load false ≤ TeamScales.width n (1/100) ∧ load true ≤ TeamScales.width n (1/5)

/-- The two numerical bounds on the common batch apply to the actual initialized wired
program, its own private descriptors and the terminal obtained from that same word assignment. -/
theorem sewnCellLoads_of_seedStorage {α : ℝ} (count : (fan S)^T*copies = R+1) (ell : ℕ)
    (positive : 0 < g₀) (small : g₀ ≤ ell)
    (storage : SeedStorage axes n r d copies T (fan S) S.recordFactor headerFactor α) :
    plan.SewnCellLoads count ell := by
  intro t pins inner Edge finite G order pos g len state W tag ns ne np sites edges ports table words ready
    bottom M q tile output data records sewn load
  let channels := (groupedGridRows G axes d order pos copies).edge
  let groups := (Equiv.refl (Fin tiles)).toEmbedding
  let coord := GridShape.coordinate (d := d+1) (factorEnum D).symm
  exact enrichedSewn_seedThresholds G axes d order pos count M bottom rfl W tag sites edges ports
    channels groups dB coord (Boundary.seed_origin S G d order pos copies table) positive small
    storage.1 storage.2.1 q tile

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

namespace Diagonal

open Crossing Cover BorderVNP.Epoch Shortening Packing DeckGrid TeamScales Filter ExternalSew
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The row-major team enumeration and the occupied exterior blocks of the
selected grid fit the very same physical link for every later wiring. -/
theorem JointSchedule.eventually_signed_grid (b : JointSchedule.{u} s E deg Q A B j) :
    ∀ᶠ n : ℕ in atTop,
    let r := stretch b.ρ n
    let d := CoverScale.initialDepth (Cube D) r n-1
    let T := epochs s.τ n
    let copies := TeamScales.width n s.α
    let R := b.physical.teamsPred n
    (fan S)^T*copies = R+1 ∧ 0 < GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d ∧
      GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d ≤ b.physical.link n := by
  have hα : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have hτ : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have fields := eventually_block_fields (Cube D) hα s.alpha_small hτ.le s.tau_small (epochCopies_pos S) s.copy_rate
  filter_upwards [fields,eventually_ge_atTop 1] with n bounds hn
  intro r d T copies R
  have hr : 1 ≤ r := stretch_one ..
  have count : (fan S)^T*copies = R+1 := (Nat.mul_comm ..).trans (b.sizes hn).1.symm
  have hd : d+1 = CoverScale.initialDepth (Cube D) r n := by
    have pos : 1 ≤ CoverScale.initialDepth (Cube D) r n := Nat.succ_pos _
    dsimp only [d]
    omega
  have tile : GridHosts.tileCount (Fintype.card (Cube D)) d = CoverScale.sites (Cube D) (CoverScale.initialDepth (Cube D) r n) := by
    rw [←hd]
    simp only [GridHosts.tileCount,CoverScale.sites,Fintype.card_fun,Fintype.card_fin]
  have fit := bounds r hr (r*n) (Nat.mul_pos hr hn) le_rfl
  rw [←tile] at fit
  exact ⟨count,fit.1,fit.2.2.2⟩

/-- On the same stretched processor sequence and selected depth, the word-block bounds
and both sewn record thresholds hold before the private witness or branch is chosen. -/
theorem JointSchedule.eventually_signedSewnCellLoads (b : JointSchedule.{u} s E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop,
    let r := stretch b.ρ n
    let d := CoverScale.initialDepth (Cube D) r n-1
    let T := epochs s.τ n
    let copies := TeamScales.width n s.α
    let R := b.physical.teamsPred n
    ∀ work : ℕ, ∀ plan : SeedPlan S n r d T copies header work,
      ∃ count : (fan S)^T*copies = R+1, plan.SewnCellLoads count (b.physical.link n) := by
  filter_upwards [b.eventually_geometricSeedStorage header,b.eventually_signed_grid] with n store grid
  intro r d T copies R work plan
  exact ⟨grid.1,plan.sewnCellLoads_of_seedStorage grid.1 _ grid.2.1 grid.2.2 store⟩

end Diagonal

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalCubeStartupWorkspace
import OAI.Computability.BorderVNP.DiagonalRouteHeaderCapacity
import OAI.Computability.BorderVNP.CubeRouteWriterReadback
import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups

/-! # Cutoffs and ordered route tables in the actual signed packet allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule RoutingISA.CubeArena
open TeamContraction.ProcessorSlots _root_.OAI.Computability.BorderVNP.Cube.Physical
open RoutingISA RoutingISA.Evaluator
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {a extra E dlog Q A B j : ℕ}

/-- Address and throughput guarantees for the complete signed cube arena, including
the exact number of newly published data rows at any placement. -/
structure RouteTableInputs (arena : RoutingISA.CubeArena.Layout) (dir : Directory.Layout)
    (α ξ : ℝ) (n w frame link : ℕ) : Prop where
  /-- The paper's calibrated per-link traffic estimate. -/
  links : Cube.RouteRecords.FitsLinksAt α ξ n
  /-- At least three distinct teams can take the three routing roles. -/
  teams : 2 < arena.teams
  /-- The final public processor count at the selected scale. -/
  teamBound : (arena.teams:ℝ) ≤ (n:ℝ)^(2*α)
  /-- Actual exterior link width in processor words. -/
  physicalLink : link = TeamScales.link ξ arena.teams n
  /-- No router interval overwrites the bootstrap frame. -/
  frameBefore : frame+112 ≤ arena.header.header
  /-- The end sentinel is representable at the selected word width. -/
  ceiling : arena.stop < 2^w
  /-- Ordered table, ordinal and receiving array bounds on all demanded rows. -/
  tables : ∀ pp lp, let count := (dir.directory pp lp).length+arena.header.d.choose 2
    let tab := arena.table frame count
    count ≤ arena.maxRows ∧ tab.Allocated w ∧ tab.Ordered ∧
      tab.ordinals+tab.count ≤ arena.pairBase ∧ tab.ordinals+tab.count ≤ arena.cellBank

/-- One common threshold gives the real processor frame, separated storage for all
returned route tables, and link budgets for every admitted signed header. The
placement and live delivery counts are chosen after that threshold. -/
theorem JointSchedule.eventually_selected_route_table {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let w := b.physical.word n
      let ξ := (s.τ:ℝ)/5
      let X := R*exterior ξ r n
      let symbols := Cube.alphabet s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let cables := (boundary S start T).edges+4*(R*V)
      ∀ (dir : Directory.Layout) (len copied slots profile gates outputs width : ℕ),
        (len:ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) → copied ≤ r → 0 < slots → r*literal s.α n ≤ slots →
        slots ≤ r*n → dir.teams = R → dir.processors = r → dir.entries = (epochCopies S)^T*V →
        dir.fields ≤ 2 → dir.block = blockWidth slots V → dir.literal = literal s.α n → 1 ≤ width →
        GeometryAdviceRate.packetWords gates profile outputs width*w ≤ r*TeamScales.width n (95/100:ℝ) →
        let initial : StartupArena := ⟨R,r,literal s.α n,b.physical.link n,len,copied⟩
        let base := GeometryAdvice.Allocation.stop (initial.next+7*dir.candidates) profile gates outputs width w
        let sizes := selectedSizes base symbols X cells cables dir.candidates R r n profile
        let arena := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
        RouteTableInputs arena dir s.α ξ n w initial.frame (b.physical.link n) := by
  filter_upwards [b.eventually_cube_startup_workspace cube,s.eventually_routed_headers,
    b.eventually_lengths 0,eventually_ge_atTop 1] with n workspace capacity length hn
  intro r R w ξ X symbols start V T cells cables dir len copied slots profile gates outputs width headRoom
    packetRoom slotsPos slotsLo slotsHi nt nr ne nf nb nl widthPos charged initial base sizes arena
  obtain ⟨frame,_,_,_,_,_,arenaFit,rowFit⟩ := workspace dir len copied slots profile gates outputs width
    headRoom packetRoom slotsPos slotsLo slotsHi nt nr ne nf nb nl widthPos charged
  have fresh : initial.next ≤ base := by
    dsimp only [base,GeometryAdvice.Allocation.stop,GeometryAdvice.Allocation.packed,
      GeometryAdvice.Allocation.dense,GeometryAdvice.Allocation.dest,GeometryAdvice.Allocation.temp]
    omega
  have low : initial.frame+112 ≤ arena.header.header := frame.trans fresh
  have enough : 2 < arena.teams := length.teams.1
  have link : b.physical.link n=TeamScales.link ξ arena.teams n := by
    change b.physical.link n=TeamScales.link ξ R n
    dsimp only [R]
    rw [(b.sizes hn).1]
    rfl
  refine ⟨capacity.2,enough,length.teams.2,link,low,arenaFit,?_⟩
  intro pp lp count tab
  have room : count ≤ arena.maxRows := rowFit pp lp
  have fr : initial.frame+31 ≤ arena.records := (show initial.frame+31 ≤ arena.header.header by omega).trans
    (secondary_le_records arena)
  have full := arena.table_allocated enough fr room arenaFit
  exact ⟨room,full.1,TableLayout.reserve_ordered fr room,full.2,
    full.2.trans (Nat.le_add_right _ _)⟩

/-- Use the true two-field external encoding and every original processor slot.
The only variable description parameter is its immutable per-site word length. -/
theorem JointSchedule.eventually_signed_free_table {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let w := b.physical.word n
      let ξ := (s.τ:ℝ)/5
      let symbols := Cube.alphabet s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let cables := (boundary S start T).edges+4*(R*V)
      ∀ (desc len copied profile gates outputs width : ℕ),
        (len:ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) → copied ≤ r → 1 ≤ width →
        GeometryAdviceRate.packetWords gates profile outputs width*w ≤ r*TeamScales.width n (95/100:ℝ) →
        let dir := ExternalSew.freeDirectory (b.physical.teamsPred n) r (literal s.α n) (b.physical.link n)
          V (blockWidth (r*n) V) ((epochCopies S)^T*V) desc
        let initial : StartupArena := ⟨R,r,literal s.α n,b.physical.link n,len,copied⟩
        let base := GeometryAdvice.Allocation.stop (initial.next+7*dir.candidates) profile gates outputs width w
        let sizes := selectedSizes base symbols (R*exterior ξ r n) cells cables dir.candidates R r n profile
        let arena := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
        RouteTableInputs arena dir s.α ξ n w initial.frame (b.physical.link n) := by
  filter_upwards [b.eventually_selected_route_table cube,eventually_ge_atTop 1] with n chosen hn
  intro r R w ξ symbols start V T cells cables desc len copied profile gates outputs width headRoom copiedFit widthPos charge
    dir initial base sizes arena
  have hr : 1 ≤ r := stretch_one ..
  have pos : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have short : literal s.α n ≤ n := Nat.floor_le_of_le (by
    have h := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1 ≤ (n:ℝ))
      (show 1-(s.α:ℝ)/3 ≤ 1 by linarith)
    simpa only [Real.rpow_one] using h)
  exact chosen dir len copied (r*n) profile gates outputs width headRoom copiedFit (Nat.mul_pos hr hn)
    (Nat.mul_le_mul_left _ short) le_rfl rfl rfl rfl le_rfl rfl rfl widthPos charge

end Diagonal

end BorderVNP
end Computability
end OAI

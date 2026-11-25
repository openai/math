import OAI.Computability.BorderVNP.PackedLocatedFrozenRoutingShape
import OAI.Computability.BorderVNP.DiagonalFrozenRawLabelEnvelope
import OAI.Computability.BorderVNP.DiagonalSignedLocatedWriterRoom
import OAI.Computability.BorderVNP.DiagonalSelectedRouteTable
import OAI.Computability.BorderVNP.DiagonalChargedFrozenOutput

/-! # Routing the located signed table on the chosen schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP Filter Branch Crossing Cover Packing TeamScales ExternalSew
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule EnrichedOuter
open TeamContraction TeamContraction.JointHeader TeamContraction.ProcessorSlots RoutingISA
open GeometryAdvice GeometryAdviceRate _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 6500
set_option maxHeartbeats 1500000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {e : PaidIdentity F D m}
    {S : SiteSchedule e} (cube : FixedCube K) {extra E deg Q A B j : ℕ}
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) deg Q A B j)
    (φ : K →+* F) (q : ℕ) (adv : ℕ → ℕ) (c k n : ℕ)

local notation "r" => stretch b.ρ n
local notation "R" => b.physical.teamsPred n
local notation "W" => b.physical.word n
local notation "ξ" => (s.τ:ℝ)/5
local notation "X" => exterior ξ r n
local notation "lim" => adv (adviceScale b.σ b.ρ n)
local notation "reserve" => SeedPlan.profileReserve r n
local notation "start" => CoverScale.initialDepth (Epoch.Cube D) r n
local notation "T" => epochs s.τ n
local notation "V" => CoverScale.sites (Epoch.Cube D) start
local notation "symbols" => alphabet s.α n
local notation "cap" => declarationCap cube.pred symbols (blocksFor ((R+1)*X : ℕ)
  (cube.h*cube.b) (symbols^(cube.pred+1))) cube.b cube.h cube.width
local notation "entries" => _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width

/-- At this batch the original sewn paths and the concrete located table use the same
per-link exterior budget. Table allocation precedes both the live placement and route rows. -/
structure LocatedFrozenRoutingAt : Prop where
  /-- Every history on a selected signed plan uses the calibrated crossing width. -/
  sewn : ∀ header work, ∀ plan : SeedPlan S n r (start-1) T (width n s.α) header work,
    ∃ count : (fan S)^T*width n s.α=R+1, plan.SewnWidths count (b.physical.link n) X (1/2)
  /-- The actual reserved table and the task built from its directory accept every ordered route table. -/
  table : ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField e (φ ∘ cube.table) q l size ord} (chart : AdvisedBranch common)
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (R+1) r (b.physical.multBits n) (b.physical.tally n) W (lim+6)),
    reader.charge≤c*(lim+1)^k →
    let len := PositiveFields.width reserve cube.pred symbols cap (R+1)
      (pairedTableParameters (l+1) size+Fintype.card (e.Entry ⊕ entries)) (b.physical.tally n)
    let initial : StartupArena := ⟨R+1,r,literal s.α n,b.physical.link n,len,reader.packetBitCount⟩
    ∀ (header desc ceiling factor tiles origins : ℕ)
      (t : SeedPlan.LocatedFrozenTable reserve W ceiling n r (R+1) tiles origins (fun raw o =>
        SignedTableStartupAt (aux:=φ ∘ cube.table) (q:=q) cube b (cube.signedSiteProgram e)
          adv c k factor n raw ceiling ceiling o W desc)),
    let gates := (t.raw.reserve ceiling).size
    let dir := b.signedStartupDirectory n desc
    let task := b.frozenSignedTask cube n l size header initial dir reserve ceiling t.outputs W t.directories
    SelectedRawWriterRoom task.cube dir W X initial.next reserve gates t.outputs W ∧
      RouteTableInputs task.cube dir s.α ξ n W initial.frame (b.physical.link n)

/-- The original packet's startup receipt supplies the reader copy bound. Its measured serialization
pays the selected row table and checked raw writer on the very same frozen task. -/
theorem JointSchedule.eventually_located_frozen_routing (poly : PolynomiallyBounded adv) :
    ∀ᶠ n : ℕ in atTop, LocatedFrozenRoutingAt cube b φ q adv c k n := by
  filter_upwards [b.eventually_signedSewnWidths (1/2) (by norm_num),
    b.eventually_common_route_header (aux:=φ ∘ cube.table) (q:=q) cube adv poly c k,
    b.eventually_signed_free_table cube,b.eventually_cube_startup_workspace cube,
    b.eventually_selected_raw_writer_room cube,b.eventually_word_capacity 1 0,eventually_ge_atTop 1]
    with n sewn headerFits route workspace raw words hn
  refine ⟨sewn,?_⟩
  intro l size ord common chart _ _ reader cost len initial head desc ceiling factor tiles origins
    t gates dir task
  let batch := stretch b.ρ n
  let word := b.physical.word n
  let profile := SeedPlan.profileReserve batch n
  let traffic := exterior ((s.τ:ℝ)/5) batch n
  have lenFit := (headerFits.2 chart reader cost).2.1
  have copied := (t.startup chart reader cost).2.2.1
  have packet : packetWords ceiling profile t.outputs word*word ≤ batch*width n (95/100:ℝ) :=
    (Nat.le_add_left ..).trans t.packet_bound
  have positive : 1 ≤ word := by
    have h := words.2.2.1
    by_contra! bad
    have zero : word = 0 := by omega
    change 1*(batch*n+1)^0 < 2^word at h
    simp [zero] at h
  have hr := stretch_one b.ρ n
  have hα : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have literal_le : literal s.α n ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n)
      (show 1-(s.α:ℝ)/3 ≤ 1 by linarith)).trans_eq (Real.rpow_one _))
  have high := workspace dir len reader.packetBitCount (batch*n) profile ceiling t.outputs word lenFit copied
    (Nat.mul_pos hr hn) (Nat.mul_le_mul_left batch literal_le) le_rfl rfl rfl rfl (le_refl _) rfl rfl positive packet
  change SelectedRawWriterRoom task.cube dir word traffic initial.next profile (t.raw.reserve ceiling).size t.outputs word ∧ _
  rw [t.reserved_size]
  exact ⟨raw desc initial.next profile ceiling t.outputs word high.2.1,
    route desc len reader.packetBitCount profile ceiling t.outputs word lenFit copied positive packet⟩

variable {cube b φ q adv c k n}

/-- Instantiating the physical startup and the true grid directory by their
registered equalities preserves both admissions on the same gate instructions. -/
theorem LocatedFrozenRoutingAt.table_at (h : LocatedFrozenRoutingAt cube b φ q adv c k n) :
    ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField e (φ ∘ cube.table) q l size ord} (chart : AdvisedBranch common)
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (R+1) r (b.physical.multBits n) (b.physical.tally n) W (lim+6)),
    reader.charge≤c*(lim+1)^k →
    let len := PositiveFields.width reserve cube.pred symbols cap (R+1)
      (pairedTableParameters (l+1) size+Fintype.card (e.Entry ⊕ entries)) (b.physical.tally n)
    let canonical : StartupArena := ⟨R+1,r,literal s.α n,b.physical.link n,len,reader.packetBitCount⟩
    ∀ (header desc ceiling factor tiles origins : ℕ)
      (t : SeedPlan.LocatedFrozenTable reserve W ceiling n r (R+1) tiles origins (fun raw o =>
        SignedTableStartupAt (aux:=φ ∘ cube.table) (q:=q) cube b (cube.signedSiteProgram e)
          adv c k factor n raw ceiling ceiling o W desc)),
    ∀ (initial : StartupArena) (dir : Directory.Layout) (link : ℕ),
    initial = canonical → dir = b.signedStartupDirectory n desc → link = b.physical.link n →
    let gates := (t.raw.reserve ceiling).size
    let task := b.frozenSignedTask cube n l size header initial dir reserve ceiling t.outputs W t.directories
    SelectedRawWriterRoom task.cube dir W X initial.next reserve gates t.outputs W ∧
      RouteTableInputs task.cube dir s.α ξ n W initial.frame link := by
  intro l size ord common chart _ _ reader cost len canonical header desc ceiling factor tiles origins
    t initial dir link initialEq dirEq linkEq
  subst initial dir link
  exact h.table chart reader cost header desc ceiling factor tiles origins t

end Diagonal

end BorderVNP
end Computability
end OAI

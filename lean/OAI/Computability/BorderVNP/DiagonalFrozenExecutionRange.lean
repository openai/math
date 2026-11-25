import OAI.Computability.BorderVNP.DiagonalLocatedSignedGrid
import OAI.Computability.BorderVNP.DiagonalSignedDictionaryRoom
import OAI.Computability.BorderVNP.DiagonalFrozenPrivateFunding
import OAI.Computability.BorderVNP.DiagonalFrozenReportScannerRoom
import OAI.Computability.BorderVNP.DiagonalSignedBundleSortRoom
import OAI.Computability.BorderVNP.DiagonalLocatedFrozenRouting
import OAI.Computability.BorderVNP.DiagonalLocatedTableFront
import OAI.Computability.BorderVNP.DiagonalLocatedTableArgument
import OAI.Computability.BorderVNP.DiagonalCalendarPostRate
import OAI.Computability.BorderVNP.DiagonalCalendarFrontRates

/-! # A common length threshold for the signed processor's public and private runs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Branch Cover ExternalSew PackedHistoryCircuit.Normalized SelectedSchedule VPVNP TeamScales
open Packing.DeckGrid Packing.Inherited
open RoutingISA RoutingISA.Evaluator RoutingISA.SignedTaskArena Packing TeamContraction.ProcessorSlots
open scoped Classical

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {G : PaidIdentity F D m}
    {S : SiteSchedule G} (cube : FixedCube K) {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1))
    (φ : K →+* F) (q : ℕ) (adv : ℕ → ℕ) (c k header : ℕ) {hm : 0 < m}

local notation3 (prettyPrint := false) "slots₁" => (CubeConstants.install (cube.cubeID G)).slots
local notation3 (prettyPrint := false) "arguments₁" =>
  Cube.Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "finish₁" =>
  ScheduleClock.cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width arguments₁
local notation3 (prettyPrint := false) "reader₁" =>
  Cube.TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width

/-- The same length serves the original signed grid, the two marked sort
banks, the actual argument construction and every charged residue reader. -/
structure FrozenExecutionAt (n : ℕ) : Prop where
  grid : LocatedSignedGridAt cube b header n
  front : LocatedTableFrontAt cube b (E+2) slots₁ finish₁ reader₁ n
  routing : LocatedFrozenRoutingAt cube b φ q adv c k n
  arguments : LocatedTableArgumentAt cube b n
  startup : CalendarPrefixRatesAt cube b φ q (hm:=hm) (adv:=adv) c k n
  post : CalendarPostRateAt cube b φ q adv c k n
  dictionary : CubeConstants.valueBound (cube.cubeID G) < 2^(b.physical.word n)
  funding : FrozenPrivateFundingAt cube b header n
  scanner : ∀ l size (initial : StartupArena) (dir : Directory.Layout)
        (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories),
      let task := b.frozenSignedTask cube n l size header initial dir profile ceiling outputs field dirs
      task.p.siteWidth ≤ b.physical.word n ∧ task.p.siteWidth + task.p.bodyCap < 2^b.physical.word n

  bundleSortRoom : let r := stretch b.ρ n
      let T := epochs scales.τ n
      let d := CoverScale.initialDepth (Epoch.Cube D) r n-1
      let axes := Fintype.card (Epoch.Cube D)
      let J := (epochCopies S)^T*GridHosts.tileCount axes d
      let copies := width n scales.α
      let cap := seedBoxCapacity n r axes d (Fintype.card (Direction axes))
      let desc := seedDescriptionWidth n r axes d (header*logWidth r n) (BottomGridBank.bodyBudget cap)
      ∀ w ≥ 60*logWidth r n, ∀ cells ≤ r*n,
        copies < 2^w ∧ cap < 2^w ∧ desc < 2^w ∧ 2^Nat.clog 2 J*desc < 2^w ∧
          cells < 2^(60*logWidth r n) ∧ 2^Nat.clog 2 (cells+6*J+cells) ≤ 2^w

/-- Choose the common threshold before the field chart, team, residue input
or returned history. The phase coefficients are those of the signed calendar. -/
theorem JointSchedule.eventually_frozen_execution_windows (poly : PolynomiallyBounded adv) :
    ∀ᶠ n : ℕ in atTop, FrozenExecutionAt cube b φ q adv c k header (hm:=hm) n := by
  filter_upwards [b.eventually_located_signed_grid cube header,
    b.eventually_located_table_front cube (E+2) slots₁ finish₁ reader₁ le_rfl,
    b.eventually_located_frozen_routing cube φ q adv c k poly,b.eventually_located_table_argument cube,
    b.eventually_calendar_prefix_rates cube φ q (hm:=hm) poly c k,
    b.eventually_calendar_post_rate cube φ q adv c k poly,b.eventually_signed_dictionary_values G cube,
    b.eventually_frozen_private_funding cube header ((show E+2 ≤ 5*(E+2) by omega).trans (le_max_left _ _)),
    b.eventually_frozen_report_scanner_room cube header,b.eventually_signed_bundle_sort_room header]
    with n grid front routing arguments prefixRate postRate dictionary funding scanner bundleSort
  exact ⟨grid,front,routing,arguments,prefixRate,postRate,dictionary,funding,scanner,bundleSort⟩

/-- For one fixed shortening, select the cube, the actual word and gate
budgets, and a single batch before the field reader. After the advice bound
is given, one length threshold provides the numbered source and the measured
execution windows together. -/
theorem exists_frozen_execution_calendar (G : PaidIdentity F D m) (φ : K →+* F) (q : ℕ) [CharP F q]
    (hm : 0 < m) :
    ∃ cube : FixedCube K, 1 ≤ cube.h*cube.b ∧
    ∃ S : SiteSchedule G, (∀ z ≥ S.floor, S.FitsLevels z ∧ S.HasLeaves z ∧ S.RunsEnriched.{1} z) ∧
    ∃ scales : EpochScales S (cube.pred+1) 1, ∃ C p coeff A₀ a B₀ b₀ J j : ℕ,
    let g := Fintype.card (G.Entry ⊕ Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    let breadth := max ((g-1).size+1) 0
    ∃ b : JointSchedule.{0} scales 2 (max (5*3) p) 1 3076 (breadth+10) 1,
      ∀ cut : ℕ, ∀ f : ℕ → ℕ, PolynomiallyBounded f → ∀ c k factor : ℕ,
      ∃ addr pow : ℕ, ∀ᶠ n : ℕ in atTop,
        SignedCalendarAt cube b φ q hm 8 C A₀ a B₀ b₀ J j coeff addr pow cut f c k factor n ∧
        FrozenExecutionAt cube b φ q f c k 8 (hm:=hm) n := by
  obtain ⟨_,cube,dimension,S,source,chooseScale⟩ := exists_chosen_signed_calendar G φ q hm 1
  obtain ⟨scales,C,p,chooseCoefficient⟩ := chooseScale 1
  obtain ⟨coeff,chooseBatch⟩ := chooseCoefficient 1
  obtain ⟨A₀,a,B₀,b₀,J,j,select⟩ := chooseBatch 0 0 0 0
  obtain ⟨b,_,lengths⟩ := select 1 zero_lt_one
  refine ⟨cube,dimension,S,source,scales,C,p,coeff,A₀,a,B₀,b₀,J,j,b,?_⟩
  intro cut f hf c k factor
  obtain ⟨addr,pow,selected⟩ := lengths cut f hf c k factor
  refine ⟨addr,pow,?_⟩
  filter_upwards [selected,b.eventually_frozen_execution_windows cube φ q f c k 8 (hm:=hm) hf]
    with n calendar windows
  exact ⟨calendar,windows⟩

end Diagonal

end BorderVNP
end Computability
end OAI

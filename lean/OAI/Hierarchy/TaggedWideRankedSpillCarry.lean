import OAI.Hierarchy.TaggedWideSelectedSpillSource
import OAI.Hierarchy.ProbeFixedWideRankedSpillCarry
import OAI.Hierarchy.TaggedWideBranchRoleHeight

namespace OAI
/-! # Physical transfer at the selected original rank -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open TaggedPrune Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12288
set_option maxHeartbeats 6000000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unitCost g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
    (v.wide_dated_sites h width ell unitCost) (v.wide_dated_edges h width ell unitCost) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
variable (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
variable {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)
local notation "report" => v.wide_reported_path h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
    Sfit support.size.late support.size.words j
local notation "bought" => v.wide_selected_local_return m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "rootROM" => v.wideInstalledRoot x
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
local notation "rankEnd" => v.wideSpillRankEnd h width v.maxBits first
local notation "issued" => (bought).2.2.2.choose_spec.1
local notation "atPrune" => (issued).choose
local notation "saved" => (issued).choose_spec.choose_spec

local notation "file" => v.wide_selected_spill_registers m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j
local notation "table" => v.wide_selected_spill_operands m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j
local notation "raw" => (reader).format.windows.header es (CalendarTape.encode sl es base j) seed
local notation "native" => v.wide_reported_path_native h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
local notation "degree" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "sites" => siteLast h d k+1
local notation "word" => Native.wordBits h d Native.copies
local notation "cash" => v.wideHistoryUnit unitCost
local notation "lim" => max v.menu.maximum (v.keepLimit+1)
local notation "budget" => max cash (max lim (v.overflowFactor lim))

-- Use the physical register specification already computed on the selected path.
open Lean Meta Elab Term in
local elab "rankedAtSelected% " reg:term:max date:term:max : term => do
  let fileTerm ← elabTerm reg none
  let dateTerm ← elabTerm date none
  let some evidence ← whnfUntil (← inferType fileTerm) ``NativeSpillRegisters.Evidence
    | throwError "expected the physical register evidence"
  let shared := evidence.getAppArgs.back!
  let spec ← if shared.getAppFn.constName?.any (fun n => n.getString! == "selectedSpillRegisterSpecification") then
      let some unfolded ← unfoldDefinition? shared true
        | throwError "the selected physical register specification is unavailable"
      pure unfolded.headBeta
    else pure shared
  let args := spec.getAppArgs
  unless args.size == 39 && spec.getAppFn.constName?.any (fun n => n.getString! == "nativeRegisterFieldTypes") do
    throwError "expected the original funded register specification"
  -- Eight type and instance parameters precede the paid run through its old work bank.
  -- The register specification ends in the input family, after the four memory states.
  -- The row reader places that family before the terminal addresses and the date.
  let head ← mkConstWithFreshMVarLevels ``rankedSpillAt
  return mkAppN head (args.extract 0 32 ++ #[args[38]!, args[32]!, args[33]!, dateTerm] ++
    args.extract 34 38 ++ #[fileTerm])

/-- Evaluate the two sides of any spill row using the registers of this original
selected run. Its sole state-dependent data are the two local port families. -/
abbrev wide_ranked_spill_carry (height : v.BranchRoleHeight h width) (t : Fin (es).length) :=
  let duration:=support.size.spill cpu.room
  have cashAge : max (2*budget) (degree*budget)≤h := (max_le_iff.mp support.size.spillRead).1
  have other := (max_le_iff.mp ((max_le_iff.mp support.size.spillRead).2))
  have overflowAge : v.wideSpillOverflowHeight≤h := by
    have both:=support.size.spillAge
    simp only [wideSpillSheetHeight,max_le_iff] at both
    exact both.2.2
  have digitAge : degree*cash≤h := (Nat.mul_le_mul_left degree (le_max_left _ _)).trans
    (le_trans (le_max_right _ _) cashAge)
  have firstRank : first≤rankEnd := by
    change first≤first+_+_;omega
  have rankWord : rankEnd≤2^word := by
    have full:=duration.room
    have le : rankEnd ≤ (v.wideSpillDates h width ell unitCost v.maxBits first).endAt rankEnd := by
      simp only [WideCPU.SpillDates.endAt,WideCPU.Dated.maskStart,WideCPU.Dated.controlStart,
        WideCPU.Dated.rolesEnd,WideCPU.SpillDates.roleRoot,WideCPU.endOf]
      omega
    exact le.trans full.le
  have firstWord := firstRank.trans rankWord
  have seatRoom : 2*degree≤2^word := other.1.trans
    ((show h≤word from by unfold Native.wordBits ProbeStage.roomBits; omega).trans Nat.lt_two_pow_self.le)
  have roleEnd : (g).rolesEnd S≤(g).workEnd S := by
    dsimp only [WideCPU.Dated.workEnd,WideCPU.Dated.slotStart,WideCPU.Dated.maskStart,
      WideCPU.Dated.controlStart,WideCPU.endOf]; omega
  have oldEnd : (g).workEnd S+2≤(lay).floor := v.wide_window_after_terminal x _
  have layFloor : (lay).floor≤(lay).pruneScratch := Nat.le_add_right _ _
  have beforeRank : (g).rolesEnd S≤rankEnd := le_trans (by omega : (g).rolesEnd S≤first) firstRank
  have romEnd : rootROM+sites≤(g).romEnd rootROM := by
    unfold WideCPU.Dated.romEnd WideCPU.Dated.maskROM WideCPU.Dated.controlROMStart
      WideCPU.Dated.firstROM WideCPU.Dated.siteROM WideCPU.endOf
    change rootROM+sites≤rootROM+sites+_+_+_+_;omega
  have romFloor : rootROM+sites≤first :=by have gap:=duration.gap; have endOld:=duration.oldBefore;omega
  have siteRoom : sites≤2^word :=(Nat.le_add_left ..).trans (romFloor.trans firstWord)
  have physical : sites*degree≤(g).rolesEnd S := by
    have mul : 3*(g).roleSpan≤((es).length+1)*(3*(g).roleSpan) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have span : sites*degree≤(g).roleSpan :=by change sites*degree≤1+sites*degree+_;omega
    change _≤S+((es).length+1)*(3*(g).roleSpan);omega
  have passed:=(native).choose_spec.choose_spec.choose_spec.1
  let fit := height.funded_aperture S unitCost Sfit rate perm.symm
    (v.wideFundedRaw h width v.maxBits raw) passed
  fun {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (board : Tagged.WideControlJoin.Gate) =>
    (rankedAtSelected% file t) (X:=X) (Y:=Y) (Z:=Z) rate overflowAge cashAge digitAge duration.archiveFloor
      siteRoom seatRoom (physical.trans (beforeRank.trans rankWord)) height.floor
      (other.2.trans Nat.lt_two_pow_self.le) passed (fun atDate i=>
        (fit _ atDate.val (Nat.le_of_lt_succ atDate.isLt) i false).trans
          (HistoryRoles.ceiling_le v.sampler v.mesh unitCost v.keepLimit (fuel v.mesh) width _))
      (table).2.2.2.1 (table).2.1 beforeRank (romFloor.trans firstRank) board

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

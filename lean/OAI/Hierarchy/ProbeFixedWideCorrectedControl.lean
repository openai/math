import OAI.Hierarchy.TaggedWideDenseRetention
import OAI.Hierarchy.TaggedWideSpillControlResident
import OAI.Hierarchy.ProbeFixedWideEarlyBanks
import OAI.Hierarchy.ProbeFixedWideSpillDates

namespace OAI
/-! # All signed and spill comparison words of the actual corrected controller -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard HistoryRoles WideCPU SiteControls
open scoped Classical Fin.CommRing BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width ell unitCost bits first rom old start : ℕ)
set_option quotPrecheck false
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "T" => (events v.mesh).length
local notation "g" => v.wideDated h width ell unitCost
local notation "z" => v.wideSpillDates h width ell unitCost bits first
local notation "root" => (z).roleRoot start 2
local notation "D" => (g).roleCount
local notation "sz" => (g).sites
local notation "cnt" => (fun j:Fin T=>(rfl: (g).controlColumns j=fieldCount D))
variable (j : Fin (events v.mesh).length) (side : Bool)
local notation "control" => (g).control j
def wideCorrectedControlStart := if side then (z).spillStart start j else (g).controlBase root j
def wideCorrectedControlFields : Fields control :=
  if side then spillControls sz (g).physical D (z).cap ((g).siteStride rom) ((z).preClip old start j)
    ((g).roleStart old j.succ) ((z).dateRole start j 1) ((z).dateRole start j 2)
  else (g).controls j ((g).siteStride rom) ((g).roleStart old j.castSucc) ((z).dateRole start j 0) ((g).ballotStart root j+1)

local notation "a" => v.wideCorrectedControlStart h width ell unitCost bits first start j side
local notation "x" => v.wideCorrectedControlFields h width ell unitCost bits first rom old start j side
local notation "window" => (control).sheet sz ((g).controlROM rom j) a x
def wideCorrectedControlResult (prior : Memory W→Prop) : PageResult W window :=
  denseResult ((g).controlROM rom j) a x prior

/-- The native input to the selected dense scatter is still readable on its
entire earlier memory interval, in addition to the control fields it wrote. -/
def wideCorrectedControlRetained (prior : Memory W→Prop) (out : Memory W) : Prop :=
  ∃before,prior before ∧ (∀addr,addr<a → out addr=before addr) ∧
    ∀site : Fin sz,∀field : Fin (fieldCount D),
      out (a+1+(SiteScatter.pos site field).val)=((x).value (0 : Fin 1) field).eval before (site.val:Word W)

theorem wideCorrectedControlRetained.localize (prior : Memory W→Prop) (early later : Memory W)
    (same : ∀addr,addr<(window).stop→later addr=early addr)
    (held : v.wideCorrectedControlRetained h width ell unitCost bits first rom old start j side prior early) :
    v.wideCorrectedControlRetained h width ell unitCost bits first rom old start j side prior later := by
  obtain ⟨before,ready,frame,words⟩:=held
  refine ⟨before,ready,fun addr small=>(same addr ?_).trans (frame addr small),fun site field=>?_⟩
  · change addr<a+1+sz*(control).columns+2*(control).count
    exact small.trans_le ((Nat.le_add_right a 1).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  · have bound:=(SiteScatter.pos site field).isLt
    change (SiteScatter.pos site field).val<sz*fieldCount D at bound
    have index := Nat.add_lt_add_left bound (a+1)
    exact (same _ (index.trans_le (Nat.le_add_right _ (2*(control).count)))).trans (words site field)

set_option cleanup.letToHave false in
set_option maxHeartbeats 1600000 in
theorem wide_corrected_control_step (prior : Memory W→Prop) (source : Memory W) (seen : prior source)
    (siteROM : Fin (g).siteDirectorySize→ℕ) (live : Fin (g).rawEdges→Bool) (input : Memory W)
    (mounted : ∀i,(g).controlROM rom j≤ i→i<(g).controlROM rom j+(control).advice sz→
      source i=(g).words rom siteROM live input i)
    (earlier : old≤ start) (gap : 3*(g).romEnd rom+2≤old) (room : (z).endAt start<2^W) :
    ∃out,((window).code W).Exec source out (window).ticks ∧
      (v.wideCorrectedControlResult h width ell unitCost bits first rom old start j side prior).holds out ∧
      ∀i,i<(window).floor → out i=source i := by
  have firstRoot : start≤root:=Nat.le_add_right ..
  have pre : root≤(g).rolesEnd root:=Nat.le_add_right ..
  have ballots : (g).rolesEnd root≤(g).controlStart root:=Nat.le_add_right ..
  have packet : (g).controlStart root≤(g).controlBase root j:=Nat.le_add_right ..
  have orig:=extent ((g).controlStart root) (fun i=>((g).control i).span sz) j
  change (g).controlBase root j+(control).span sz≤(g).maskStart root at orig
  have after:=extent ((g).maskStart root) (fun i=>((g).control i).span sz) j
  change (z).spillStart start j+(control).span sz≤(z).endAt start at after
  have mid : (g).maskStart root≤(z).spillStart start j:=Nat.le_add_right ..
  have late : (g).controlBase root j≤a:=by cases side <;> simp [wideCorrectedControlStart]; omega
  have space : a+(control).span sz<2^W:=by
    cases side <;> simp only [wideCorrectedControlStart,Bool.false_eq_true,ite_false,ite_true] <;> omega
  have fit : a+1<2^W:=by dsimp only [WideCPU.Shape.span] at space;omega
  have oldPaid : old≤a:=earlier.trans (firstRoot.trans (pre.trans (ballots.trans (packet.trans late))))
  have baseRoom : (g).controlBase root j+1<2^W:=by omega
  have src : ((g).siteStride rom).Fits W (a+1):=((g).global_banks (gap.trans oldPaid) (by omega)).2
  have fullBank (r : ℕ) (below : r≤root) (t : Fin (T+1)) (f : Fin 3) :
      (DatedRoleSheets.bank (g).physical ((g).roleStart r t) (g).roleWords
        (ProtocolRAMPurchaseSampler.bits (g).roleWords) f).Fits W (a+1) := by
    have H:=v.wide_role_bank_before_control h width ell unitCost r root below j t f baseRoom
    exact ⟨H.1,H.2.1,H.2.2.trans (by omega)⟩
  have rootSide (f : Fin 3) : (z).roleRoot start f≤root := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (show f.val≤2 by omega)) start
  have originalRoot : old≤root:=earlier.trans firstRoot
  have ballotFit (present : ((g).ballot j).columns ≠ 0) :
      (RoleROM.bank ((g).ballotStart root j+1) (sz*((g).ballot j).columns)).Fits W (a+1) := by
    have attempt_of_columns (e : Event) (active : (v.widePacketShape h width e).columns ≠ 0) :
        ∃ evt : Attempt, e = .attempt evt := by
      cases e with
      | attempt evt => exact ⟨evt, rfl⟩
      | feed _ => exact (active rfl).elim
    obtain ⟨evt, hit⟩ := attempt_of_columns ((events v.mesh).get j) present
    have fitBank := v.wide_ballot_bank_before_control h width ell unitCost root j evt hit baseRoom
    exact ⟨fitBank.1,fitBank.2.1,fitBank.2.2.trans (Nat.add_le_add_right late 1)⟩
  have signedFields := SiteControls.fixed_fits sz (g).physical D (v.wideNeighborCap width unitCost)
    ((g).siteStride rom) ((g).roleStart old j.castSucc) ((z).dateRole start j 0)
    ((g).ballotStart root j+1) ((g).ballot j).columns
    (v.widePacketLowStart h width ((events v.mesh).get j)) src
    (fun branch field => by
      cases branch with
      | false => exact fullBank old originalRoot j.castSucc field
      | true => exact fullBank _ (rootSide 0) j.succ field) ballotFit
  have spillFields := spill_fits sz (g).physical D (z).cap ((g).siteStride rom)
    ((z).preClip old start j) ((g).roleStart old j.succ) ((z).dateRole start j 1) ((z).dateRole start j 2)
    src (fun branch field => by
      cases branch with
      | true => exact fullBank old originalRoot j.succ field
      | false =>
        change (DatedRoleSheets.bank _ ((z).preClip old start j) _ _ field).Fits W (a+1)
        unfold SpillDates.preClip
        split
        · exact fullBank _ (rootSide 0) j.succ field
        · exact fullBank old originalRoot j.castSucc field)
    (fun branch field => by
      cases branch with
      | false => exact fullBank _ (rootSide 1) j.succ field
      | true => exact fullBank _ (rootSide 2) j.succ field)
  have fields : ∀i,((x).selected i).Fits W (a+1) ∧ ((x).site i).Fits W (a+1) ∧
      ∀c,((x).value i c).Fits W (a+1) := by
    cases side with
    | false => exact signedFields
    | true => exact spillFields
  have endROM:=extent ((g).controlROMStart rom) (fun t=>((g).control t).advice sz) j
  change (g).controlROM rom j+(control).advice sz≤(g).maskROM rom at endROM
  have hrom : (g).maskROM rom≤(g).romEnd rom:=Nat.le_add_right ..
  have one : 1<2^W:=by omega
  have fee : (control).columns≤2^W:=by
    have:=Nat.le_mul_of_pos_left (control).columns (show 0<sz from Nat.zero_lt_succ _)
    dsimp only [WideCPU.Shape.span] at space;omega
  have pub:=PublicSheet.of_placement control x source
    (WideCPU.Shape.Origin.copy_low _ ((g).control_origin rom siteROM live input j) mounted)
    (endROM.trans hrom) (gap.trans oldPaid) space fields one.le fee
  apply dense_run _ _ x prior source seen pub one
  · intro i;cases side <;> rfl
  · intro i;cases side <;> rfl

theorem wide_corrected_control_retained_step (prior : Memory W→Prop) (source : Memory W) (seen : prior source)
    (siteROM : Fin (g).siteDirectorySize→ℕ) (live : Fin (g).rawEdges→Bool) (input : Memory W)
    (mounted : ∀i,(g).controlROM rom j≤ i→i<(g).controlROM rom j+(control).advice sz→
      source i=(g).words rom siteROM live input i)
    (earlier : old≤ start) (gap : 3*(g).romEnd rom+2≤old) (room : (z).endAt start<2^W) :
    ∃out,((window).code W).Exec source out (window).ticks ∧
      v.wideCorrectedControlRetained h width ell unitCost bits first rom old start j side prior out ∧
      ∀i,i<(window).floor → out i=source i := by
  obtain ⟨out,run,reported,frame⟩:=v.wide_corrected_control_step h width ell unitCost bits first rom
    old start j side (fun snapshot=>snapshot=source) source rfl siteROM live input mounted earlier gap room
  obtain ⟨before,exactSource,words⟩:=reported
  subst before
  exact ⟨out,run,⟨source,seen,frame,words⟩,frame⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

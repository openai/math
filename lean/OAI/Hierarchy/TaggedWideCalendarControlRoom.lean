import OAI.Hierarchy.TaggedWideOriginalCalendarPrice
import OAI.Hierarchy.TaggedWideCalendarControlBounds

namespace OAI
/-! # The physical control addresses and digits of the corrected calendar -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.SignedSites
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Tagged
open WideStack TaggedPrune TaggedShorterBudget TaggedShorterSupergroups WireTelescope.PassMatrix WideCPU Filter
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short unitCost : ℕ) {x : WideParent κ A}
local notation "g" => v.wideDated x.h x.w ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "root" => v.wideInstalledRoot x
local notation "L" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "U" => (L).pruneScratch+(L).pruneRows+1
local notation "Z" => v.wideSpillDates x.h x.w ell unitCost v.maxBits U
local notation "rank" => v.wideSpillRankEnd x.h x.w v.maxBits U
local notation "endAll" => v.wideCorrectedSpillEnd x.h x.w ell unitCost v.maxBits root S ((g).romEnd root) ((g).workEnd S) U

private theorem controls_fit {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (tagWord : v.signedTagCeiling≤ (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2.W+1)
    (laneWord : v.wideNeighborDigits x.w unitCost≤ (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2.W+1) :
    CalendarControlRoom (cpu:=cpu) := by
  let G:=(v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
  have through : (Z).endAt rank≤ endAll:=Nat.le_add_right ..
  have installed : endAll≤ G.u:=le_max_right ..
  have all:=through.trans installed
  refine ⟨fun s j f=>?_,fun s j f=>?_,fun s j=>?_,tagWord,laneWord⟩
  · exact (((Z).calendar_control_addresses rank j s (deg:=v.widePacketDegree) rfl).1 f).trans_le all
  · exact (((Z).calendar_control_addresses rank j s (deg:=v.widePacketDegree) rfl).2.1 f).trans_le all
  · exact (((Z).calendar_control_addresses rank j s (deg:=v.widePacketDegree) rfl).2.2).trans_le all

/-- All fields of the selected ballot and all middle guard words are on
the original corrected full CPU, including every single native date and site. -/
theorem calendar_words {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) :
    let G:=(v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
    (∀ (s : Fin (g).sites) (j : Fin (events v.mesh).length) (f : Fin ((g).ballot j).columns),
      ballotAddress g ((Z).roleRoot rank 2) j s f.val<G.u) ∧
    (∀ (s : Fin (g).sites) (j : Fin (events v.mesh).length) (q : Fin v.widePacketDegree),
      v.calendarMidAddress x.h x.w ell unitCost v.maxBits U s j q<G.u) := by
  intro G
  have through : (Z).endAt rank≤ endAll:=Nat.le_add_right ..
  have installed : endAll≤ G.u:=le_max_right ..
  refine ⟨fun s j f=>((Z).calendar_ballot_address rank j s f).trans_le (through.trans installed),?_⟩
  intro s j q
  exact ((Z).calendar_middle_address rank j (finProdFinEquiv (s,q))).trans_le (through.trans installed)

/-- The guard parameters of the installed signed calendar are paid by its
native corrected-spill extent and by the physical word, uniformly at every date. -/
theorem cofinal_calendar_room : ∀ᶠ x : WideParent κ A in WideParent.large κ A,
    ∀ N (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x),CalendarControlRoom (cpu:=cpu) := by
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  let K:=v.widePacketDegree*v.wideHistoryUnit unitCost
  filter_upwards [high.eventually (eventually_ge_atTop v.signedTagCeiling),
    WideParent.fixed_mul_width (κ:=κ) (A:=A) K] with x tagged neighbor
  intro N cpu
  have fitsHeight : v.wideNeighborDigits x.w unitCost≤ x.h:=
    (Nat.clog_le_iff_le_pow (by decide:1<2)).mpr neighbor
  have within : x.h≤ wordBits x.h (2^v.W) copies+1:=by rw [wordBits_linear];omega
  exact controls_fit v m ell short unitCost cpu (tagged.trans within) (fitsHeight.trans within)

/-- One height threshold supplies both the actual indexed read proofs and
the cost of the exact native installation for every terminal aperture operand. -/
theorem cofinal_priced_calendar (terminalWidth : ℕ) (positive : 0<terminalWidth) :
    ∃C:ℝ,0≤ C ∧ ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      ∀ N (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x),
      ∃ reads : CalendarControlRoom (cpu:=cpu),∀ (bounds : cpu.SiteRoom) schedule operand,
        let a:=ofCalendar schedule reads terminalWidth operand
        (((a.installed bounds).frame.site.cells+(a.installed bounds).frame.site.internal:ℕ):ℝ)≤
          C*((2:ℝ)^x.h*x.w*(Real.log (x.h:ℝ))^(3:ℝ)) := by
  obtain ⟨C,pos,prices⟩:=price_ofCalendar (v:=v) (κ:=κ) (A:=A) (m:=m) (ell:=ell) (short:=short)
    (u:=u) (δ:=δ) (ξ:=ξ) (unitCost:=unitCost) terminalWidth positive
  refine ⟨C,pos,?_⟩
  filter_upwards [prices,cofinal_calendar_room (κ:=κ) (A:=A) (u:=u) (δ:=δ) (ξ:=ξ) v m ell short unitCost]
    with x price room
  intro N cpu
  exact ⟨room N cpu,fun bounds schedule operand=>price N cpu bounds schedule (room N cpu) operand⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.SignedSites
end

end OAI

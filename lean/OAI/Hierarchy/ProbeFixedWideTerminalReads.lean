import OAI.Hierarchy.ProbeFixedWideTerminalFits
import OAI.Hierarchy.ProtocolRAMTurnAuthenticatedChart

namespace OAI
/-! # What the fitted fixed chronological program reads from its role and rank memory -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open CoreRoute HistoryRoles RoleProgram ProtocolRAMTurnChart
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits rom work : ℕ)
local notation "T" => v.wideTerminal h width bits rom work
local notation "L" => v.wideTurnWindow h width bits work
local notation "B" => v.wideTerminalBoard h width bits work
local notation "D" => 2^v.W
local notation "P" => v.widePlacement h width
local notation "r" => WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder (P).catalogue.rows h D k).symm
local notation "u" => ProtocolRAMTurnGeometry.header (wideRouteOrder h D k) r names
local notation "port" => Public v.sampler h v.W k v.wideJobs

theorem wide_terminal_reads {w : ℕ} (raw m : Memory w)
    {old : Fin (B).old→ℕ} {report : Fin (B).edges→ℕ}
    {before : ∀i,0<old i→Bool→port} {after : ∀i,0<report i→Bool→port}
    (live : (B).LiveReads v.sampler old report before after m)
    (keep : ∀a,rom≤a→a<v.wideTerminalROMEnd h width bits rom work→
      m a=v.wideTerminalWords h width bits rom work raw a)
    (small : v.wideTerminalROMEnd h width bits rom work≤2^w) :
    let words:=captured (T).columns m
    Loaded (T).header (T).headerBits u m ∧
    (∀(j:Fin 4) (t:ℕ),t<2^(T).romBits →
      (ProtocolRAMTurnDirectory.bank (T).rom (T).romBits j).read m (t:Word w)=
        ProtocolRAMTurnDirectory.words (T).turns (T).sites (T).seats (T).base j t) ∧
    (∀i,0<words.width (u i).item → (T).columns.At words m (u i)) ∧
    (∀i,(T).columns.oldWidth.read m ((u i).item:Word w)=(words.width (u i).item:Word w)) ∧
      ∀i:Fin (B).old,words.width i.val=old i := by
  intro words
  obtain ⟨held,dir,half⟩:=(L).retained rom r u raw m small keep
  have roleRoom : 2*r≤2^w := by
    have span := ProtocolRAMSupergroupDirectory.slotFits (2*r)
    change (L).halfBase rom+ProtocolRAMSupergroupDirectory.span (2*r)≤2^w at small
    omega
  have chart : (T).columns=ProtocolRAMTurnSnapshot.chartData B (L).site (T).columns.half := rfl
  refine ⟨held,dir,?_,fun i=>captured_width _ m _,fun i=>live.width i⟩
  intro i active
  have pos : (u i).item<(B).old :=
    (ProtocolRAMTurnGeometry.sourceOrder (P).catalogue.rows h D k (names (ProtocolRAMTurnOrder.raw (ProtocolRAMTurnGeometry.length ∘ names) i).1)).isLt
  exact ProtocolRAMTurnSnapshot.captured_live v.sampler B live (L).site (T).columns.half roleRoom half (u i) pos active

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

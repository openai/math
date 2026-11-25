import OAI.Hierarchy.ProbeFixedSourceGeometry
import OAI.Hierarchy.ProbeFixedOriginalSocketBounds
import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.ProtocolRAMCatalystTerminalLayout

namespace OAI
/-! # All seven geometry operands of the fixed wide placement fit at settlement -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage CoreBoard ReportSockets CatalystArchive TaggedShorterSupergroups
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "w" => Native.wordBits h (2^v.W) Native.copies
local notation "r" => Fintype.card (CoreRoute.Slots h (2^v.W) k)

theorem wide_catalogue_sources (routes : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (word : (A).endAddress v.mesh<2^w) :
    (P).catalogue.core.All (Expr.Fits w ((A).endAddress v.mesh)) ∧ (P).catalogue.bought.All (Expr.Fits w ((A).endAddress v.mesh)) := by
  have core := (v.wideGeometryPrefix h width).2.2
  apply v.public_sources_of_dates h width (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
    (WideMemory.R v.sampler h v.W k) 0 (v.wideJoint h width) r routes src tab dst owners core word
  intro phase trial
  exact v.catalyst_original_socket_bounds P h width phase.val trial.val (dated_outer_occurs v.mesh phase trial)

theorem wide_geometry (routes : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (word : (A).endAddress v.mesh<2^w) (i : Fin 7) :
    ((P).catalogue.geometry i).Fits w ((A).endAddress v.mesh) := by
  obtain ⟨core,bought⟩:=v.wide_catalogue_sources h width routes src tab dst owners word
  exact (P).catalogue.geometry_fits i core bought

/-- This is the page size already required to encode the terminal machine.
It discharges the catalogue operand premise at every height at which the
actual fixed terminal machine can be encoded. -/
theorem wide_geometry_at_page (stock : Bank) (stride start accounts records : ℕ)
    (height : 28*2^(TerminalLayout.pageBits v.mesh A stock stride (P).catalogue.rows r accounts records)<2^w)
    (i : Fin 7) : ((P).catalogue.geometry i).Fits w ((A).endAddress v.mesh) := by
  let bits:=TerminalLayout.pageBits v.mesh A stock stride (P).catalogue.rows r accounts records
  have enough : TerminalLayout.footprint v.mesh A stock stride (P).catalogue.rows r accounts records<2^bits := Nat.lt_log2_self
  unfold TerminalLayout.footprint at enough
  have fits : (A).endAddress v.mesh<2^w := by change 28*2^bits<2^w at height;omega
  exact v.wide_geometry h width (TerminalLayout.settlement bits stock) (TerminalLayout.source bits)
    (TerminalLayout.table bits) (TerminalLayout.destination bits)
    (CatalystArchive.sinkBank start records r (P).catalogue.rows) fits i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI

import OAI.Computability.BorderVNP.DiagonalNativeTimedModes
import OAI.Computability.BorderVNP.TeamSiteTimedScaleData

/-! # Broadcast-mode decomposition at the diagonal's actual resource scales -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamScales TeamSite Filter
open FieldProcessor (Scale freeWidth)
open scoped Classical BigOperators

/-- At one true physical geometry, all installed packet and literal assignments
have the reference contribution and the charged evaluator contribution. The initial
RAM ticks, burst bound and private cutoff are the manuscript's actual rounded values. -/
def PacketModesAtScale {Q Γ : Type} [Fintype Q] {m g r n R w e : ℕ} {α ξ : ℝ}
    (eval : Code) (lib : Fin 8 → Macro Q Γ m g) (mark : Fin 8 → Γ)
    (geo : Scale (TimedProcessor.machine (withStartup eval).program lib mark)
      ((withStartup eval).slots+1) 64 32 α ξ r n R w e) : Prop :=
  let P := (withStartup eval).program
  let physical := TimedProcessor.machine P lib mark
  ∀ (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (advice : Fin (R+1) → Fin r → Bool)
    (free : Fin (R+1) → Fin r → Fin (freeWidth physical α 32 64 r w n) → Bool)
    {d : ℕ} (pack : Fin (R+1) → ReferencePacket w d) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool),
    let S := TimedProcessor.scaleData P lib mark geo pub reg advice free
    let G := wiringWith physical P (S.withPacket pack) d (link ξ (R+1) n) n e geo.fits
    (∀ u, (args u).Fitted G u (pack u) (pub u) (adviceOffsetWith physical r 32 64 w n)) →
    Diagonal.signedContraction G.slot pin =
      (if pin=(pack 0).reference then 1 else 0) +
      ∑ ext, ∏ u, positiveMaskedNativeValue G eval (TeamSiteEvents.macros lib (n^25+1))
        pub reg args pin (ticks ξ r n) (width n (1/2)) (n^25) ext u

/-- Any calibrated geometry for this timed executable gives the packet identity,
using a threshold independent of its team counts, word width and sorter depth. -/
theorem eventually_modes_of_geometry {Q Γ : Type} [Fintype Q] {m g : ℕ} {ξ η : ℝ}
    (hξ : 0 < ξ) (small : ξ ≤ 1) (eta : η ≤ 1-ξ) (eval : Code) (he : eval.withoutAccept = true)
    (lib : Fin 8 → Macro Q Γ m g) (mark : Fin 8 → Γ) (distinct : ∀ j, (lib j).alphabet.blank ≠ mark j) :
    ∀ᶠ t : ℕ in atTop, ∀ (α : ℝ) (R r w e : ℕ), 0 < r → R+1 ≤ width (t+1) η →
    ∀ geo : Scale (TimedProcessor.machine (withStartup eval).program lib mark)
      ((withStartup eval).slots+1) 64 32 α ξ r (t+1) R w e, PacketModesAtScale eval lib mark geo := by
  filter_upwards [eventually_sewn_packet_modes hξ small eta eval he lib mark distinct] with t modes
  intro α R r w e hr exterior geo pub reg advice free d pack args pin S G fitted
  have hH : block ξ (t+1) ≤ t+1 := by
    have localCap := geo.baseline.rowCapacity
    have fit := geo.baseline.localSort
    omega
  exact modes R r w _ d e S pack geo.fits hr geo.baseline geo.widened geo.dimensions
    geo.comparators hH exterior le_rfl args pin fitted (fun ext u j =>
      TimedProcessor.scaleInput (withStartup eval).program lib mark geo (S.withPacket pack) u j pin ext
        (args u).ibase (args u).hbase (args u).starbase)

/-- The common admissible exponent is chosen before the evaluator and the native
library. Every sufficiently large dimension simultaneously supports the actual timed
program, sorter and signed mode decomposition for all admitted team geometries. -/
theorem eventually_packetModesAtScale (D : ℕ) {α ξ η : ℝ}
    (hα : α < 3) (hξ : 0 < ξ) (small : ξ ≤ 1) (order : ξ ≤ α) (eta : η ≤ 1-ξ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ {Q Γ : Type} [Fintype Q] {m g : ℕ} (eval : Code),
      eval.withoutAccept = true → ∀ (lib : Fin 8 → Macro Q Γ m g) (mark : Fin 8 → Γ),
      (∀ j, (lib j).alphabet.blank ≠ mark j) → ∀ᶠ t : ℕ in atTop, ∀ r : ℕ,
      0 < r → (r : ℝ) ≤ (2 : ℝ)^(((t+1 : ℕ) : ℝ)^ω) → ∀ R : ℕ, R+1 ≤ width (t+1) η →
      let P := (withStartup eval).program
      let w := logWidth r (t+1)^(D+1)
      let e := Wires.sortExponent (block ξ (t+1))
      ∃ geo : Scale (TimedProcessor.machine P lib mark) ((withStartup eval).slots+1) 64 32 α ξ r (t+1) R w e,
        PacketModesAtScale eval lib mark geo := by
  obtain ⟨ω,positive,scale⟩ := FieldProcessor.eventually_programGeometry D hα hξ (by linarith) order
  refine ⟨ω,positive,?_⟩
  intro Q Γ inst m g eval he lib mark distinct
  let P := (withStartup eval).program
  let physical := TimedProcessor.machine P lib mark
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (scale P lib physical),
    eventually_modes_of_geometry hξ small eta eval he lib mark distinct] with t geometry modes
  intro r hr admissible R exterior _ w e
  have geo := geometry r hr admissible R
  exact ⟨geo,modes α R r w e hr exterior geo⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI

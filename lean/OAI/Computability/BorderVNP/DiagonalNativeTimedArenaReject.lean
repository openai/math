import OAI.Computability.BorderVNP.DiagonalJointExterior
import OAI.Computability.BorderVNP.DiagonalNativeTimedArena

/-! # Rejection and local readiness on the allocated timed packet arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamScales TeamSite Filter
open FieldProcessor (Scale freeWidth)
open scoped Classical BigOperators

set_option maxRecDepth 4000

variable {Q Γ : Type} [Fintype Q] {m g r n R w e d : ℕ} {α ξ : ℝ}
variable (eval : Code) (lib : Fin 8 → Macro Q Γ m g) (mark : Fin 8 → Γ)
local notation "P" => Code.program (withStartup eval)
local notation "physical" => TimedProcessor.machine P lib mark
local notation "a" => freeWidth physical α 32 64 r w n
local notation "l" => link ξ (R+1) n
local notation "off" => adviceOffsetWith physical r 32 64 w n
variable (geo : Scale (TimedProcessor.machine (withStartup eval).program lib mark) ((withStartup eval).slots+1) 64 32 α ξ r n R w e)
variable (header copied : ℕ) (pack : Fin (R+1) → ReferencePacket w d)
local notation "arena" => programArena physical R r w n a l header copied
local notation "args" => fun u : Fin (R+1) => StartupArena.unitAddresses arena off (pack u)
local notation "encoded" => fun (extra : Fin (R+1) → Arg → Word w) u =>
  PacketOperands.bank (StartupArena.operands arena u off (pack u)) (extra u)

/-- The actual encoded operands and runtime allowance for every site on the same
chosen geometry. Both assertions apply before choosing a live pin or exterior. -/
def AllocatedPacketReady : Prop :=
  ∀ (S : SiteData R r 64 32 w a) (extra : Fin (R+1) → Arg → Word w) (u : Fin (R+1)),
    let G := wiringWith physical P (S.withPacket pack) d l n e geo.fits
    let addr := args u
    addr.Fitted G u (pack u) (encoded extra u) off ∧
      packetUnitBudget addr.advice.count w (G.transferFrame u addr.header addr.dst)
        (G.pinLayout u addr.ibase addr.hbase addr.starbase) ≤ ticks ξ r n

/-- A malformed assignment to the actual shared exterior contributes zero for
every external pin and every installed private literal, at the original tick cutoff. -/
def AllocatedPacketRejects : Prop :=
  ∀ (S : SiteData R r 64 32 w a) (extra : Fin (R+1) → Arg → Word w),
    S.publicWords = encoded extra → S.limit.val = ticks ξ r n → ∀ (pin : Fin d → Bool),
    let G := wiringWith physical P (S.withPacket pack) d l n e geo.fits
    ∀ ext, ¬ PositiveExterior G args pin w ext →
      (∏ u, positiveMaskedNativeValue G eval (TeamSiteEvents.macros lib (n^25+1))
        S.publicWords S.registers args pin S.limit.val S.burst.val (n^25) ext u) = 0

theorem AllocatedPacketReady.rejects (he : eval.withoutAccept = true)
    (ready : AllocatedPacketReady eval lib mark geo header copied pack) :
    AllocatedPacketRejects eval lib mark geo header copied pack := by
  intro S extra words ticksEq pin G
  apply positive_mask_reject physical eval (TeamSiteEvents.macros lib (n^25+1)) S pack geo.fits args pin he
  · intro u
    rw [words]
    exact (ready S extra u).1
  · intro u
    rw [ticksEq]
    exact (ready S extra u).2

/-- A single length threshold gives local readiness of every fitted packet arena.
The time estimate uses the full measured startup, broadcast and unit path. -/
theorem eventually_allocatedPacketReady {ξ η : ℝ} (hξ : 0 < ξ) (small : ξ ≤ 1) (eta : η ≤ 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ {α : ℝ} {R r w e d : ℕ} (geo : Scale physical ((withStartup eval).slots+1)
      64 32 α ξ r n R w e) (header copied : ℕ) (pack : Fin (R+1) → ReferencePacket w d),
      2 < R+1 → (R+1:ℕ) ≤ (n:ℝ)^η → 0 < header → header ≤ r*link ξ (R+1) n →
      (∀ u, (pack u).bits.length ≤ copied) → copied ≤ r →
      let free := freeWidth physical α 32 64 r w n
      let A := programArena physical R r w n free (link ξ (R+1) n) header copied
      A.next < 2^w → AllocatedPacketReady eval lib mark geo header copied pack := by
  filter_upwards [eventually_packetUnitBudget_le_ticks hξ small eta] with n budget
  intro α R r w e d geo header copied pack three teams hdr cap length copies free A ceiling S extra u G addr
  have h := fitted_programArena physical P (S.withPacket pack) geo.fits header copied u (pack u) (extra u)
    three hdr cap (length u) copies ceiling
  exact ⟨h,budget w d _ (pack u) addr.advice (G.transferFrame u addr.header addr.dst)
    (G.pinLayout u addr.ibase addr.hbase addr.starbase) h.physical rfl teams h.packet h.gather.count rfl⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI

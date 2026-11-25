import OAI.Computability.BorderVNP.DiagonalNativeTimedArenaReject

/-! # Site-independent length of the transmitted packet unit check -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator TeamScales TeamSite Filter
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


/-- The physical unit check inspects all partner blocks, the common header
and every pin. Its cost is independent of any literal, numeric pin value,
or address of the stored reader program. -/
def lengthUnitBudget (teams processors ell hdr pins bits copied : ℕ) :=
  packetUnitBudget copied bits (⟨0,teams,processors,0,ell,hdr,0⟩ : BroadcastFrame)
    (⟨0,teams,processors,0,ell,pins,0,0,0⟩ : Layout)

/-- Extract the numerical budget from the actual readiness certificate on
the chosen geometry, reserving the same tick for every team and exterior. -/
theorem AllocatedPacketReady.lengthClock (ready : AllocatedPacketReady eval lib mark geo header copied pack) :
    lengthUnitBudget (R+1) r l header d w copied ≤ ticks ξ r n := by
  let S := TimedProcessor.scaleData P lib mark geo (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => false) (fun _ _ _ => false)
  exact (ready S (fun _ _ => 0) 0).2

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI

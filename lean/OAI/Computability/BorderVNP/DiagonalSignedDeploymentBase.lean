import OAI.Computability.BorderVNP.DiagonalFixedSignedSites
import OAI.Computability.BorderVNP.RoutingISASignedSiteOperands
import OAI.Computability.BorderVNP.CubeRoutePinnedFrame
import OAI.Computability.BorderVNP.PackedRoutingDemandHeader

/-! # The signed processor's initial ordinary operands before any public profile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP BurstRAM Crossing TeamScales TeamContraction TeamContraction.ProcessorSlots
open RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine TeamSite Packing.RoutingOutputs
open PackedHistoryCircuit
open FieldProcessor (Scale freeWidth)
open scoped Classical
set_option maxHeartbeats 600000
set_option maxRecDepth 4000

variable {D m : ℕ} {F K : Type} [Field F] [Field K] (paid : PaidIdentity F D m) (cube : FixedCube K)
    {n R r w ec : ℕ} {α ξ : ℝ}
    (geo : Scale (cube.signedSiteProgram paid) ((withStartup (signedBody (cube.cubeID paid))).slots+1)
      64 32 α ξ r n R w ec)
    (A : StartupArena) (task : SignedTaskArena.Layout) (origin inputs guesses gates : ℕ)
local notation "siteProgram" => Code.program (signedProgram (cube.cubeID paid))
local notation "lib" => siteLibrary SparseExterior.driver
local notation "clockMark" => fun _ : Fin 8 => some false

/-- Every team starts with the original fixed timed program, its true input
and gate ranges, empty registers, and the same reserved geometry output.
The startup literal subsequently supplies each team's field and reference packet. -/
noncomputable def FixedCube.signedTaskData :
    SiteData R r 64 32 w (freeWidth (cube.signedSiteProgram paid) α 32 64 r w n) :=
  TimedProcessor.scaleData siteProgram lib clockMark geo
    (fun _ => task.ordinary A origin 0 inputs guesses gates (fun _ => 0))
    (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)

local notation "data" => cube.signedTaskData paid geo A task origin inputs guesses gates
local notation "blank" => TimedProcessor.scaleData siteProgram lib clockMark geo
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)

/-- This is the signed task overlay used by the lead reader and private calls.
The time and private burst limits are the selected physical integers. -/
theorem FixedCube.signedTaskData_actual :
    data = SignedTaskArena.withOrdinary blank (fun _ => task) A (fun _ => origin) (fun _ => 0)
      (fun _ => inputs) (fun _ => guesses) (fun _ => gates) ∧
    (data).limit.val = ticks ξ r n ∧ (data).burst.val = TeamScales.width n (1/2:ℝ) :=
  ⟨rfl,rfl,rfl⟩

/-- The same ordinary boot operands select the actual geometry's cable array
and its demand stream, as well as the residue circuit's entry word. -/
theorem FixedCube.signedTaskData_publication (u : Fin (R+1)) :
    (data).publicWords u = core (withDemandBase
      (task.routeBank A.frame (fun j : Arg => if j = 20 then TeamTapeInputEmit.word w (task.entry w inputs guesses gates) else 0)) A.next)
      origin task.cube.cables task.cube.cells := by
  funext j
  fin_cases j <;> rfl

end Diagonal

end BorderVNP
end Computability
end OAI

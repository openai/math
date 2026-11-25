import OAI.Computability.BorderVNP.CubeRoutePublishedPointers
import OAI.Computability.BorderVNP.CubeRouteChosenPins
import OAI.Computability.BorderVNP.PackedRoutingDemandHeader

/-! # All scheduler input banks on a physically published signed profile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing RoutingOutputs LocalRow

variable {w d : ℕ} (task : SignedTaskArena.Layout) (a : StartupArena) (u : Fin a.teams)
    (slot : ℕ) (p : ReferencePacket w d)

/-- Updating ordinary operand nine to the seven-word demand stream commutes
with installing the cube's allocator controls. -/
theorem withDemandBase_routeBank (other : Arg → Word w) (next : ℕ) :
    withDemandBase (task.routeBank a.frame other) next = task.routeBank a.frame (withDemandBase other next) := by
  funext j
  by_cases h : j=9
  · subst j
    simp [withDemandBase,SignedTaskArena.Layout.routeBank,SignedTaskArena.Layout.bootOperand,CubeArena.Layout.bootOperand]
  · simp only [withDemandBase,Function.update_of_ne h,SignedTaskArena.Layout.routeBank]

variable {k : ℕ} {f : BroadcastFrame} {advice : AdviceLayout} {mac : TeamOpcode.Macros w 8}
    {bits : List Bool} {bank : Bank w} {initial prof placed : Memory w} {g : Fin k → Bool}

set_option maxHeartbeats 1200000 in
/-- The actual writer's demand-base update and directory publication preserve
the copied pin source, reference packet, raw header and all five table pointers.
The pointer count can be chosen later from the real published descriptors. -/
theorem BootResidence.signedPublishedInputs (other : Arg → Word w) (origin edges cells gap : ℕ)
    (dir : Directory.Layout) (dst : f.dst=a.broadcastBase) (len : bits.length=a.header)
    (room : task.cube.stop<2^w) (reserve : a.next+7*dir.candidates≤origin) :
    let B := a.operands u slot p
    let pub := B.bank (core (withDemandBase (task.routeBank a.frame other) a.next) origin edges cells)
    let pl := privateLayout a.frame origin edges cells dir.entries dir.description gap
    let tabs := bases origin edges cells dir.entries
    let rows := dir.directory (Directory.ISA.placement (readings placed) tabs.privatePairs)
      (Directory.ISA.placement (readings placed) tabs.livePairs)
    let out := Directory.ISA.publish placed a.frame a.next rows
    B.Fits w → ∀ (F : Pins.ProcessorFields B.layout),
    BootResidence (F:=F) a u slot p f advice pub mac bits initial bank g prof →
    pl.Image (readings prof) dir.entries (readings placed) →
    ProfileRouteInputs F f pub (Pins.extendGuess g) out ∧ BootPins pub f p.extension bits out ∧
      F.header.length=(pub 0).val ∧ ∀ count, TablePointers (task.cube.table a.frame count) (readings out) := by
  intro B pub pl tabs rows out fits F path img
  have base : (pub 0).val=a.frame := B.frameBase_word _ fits
  refine ⟨path.demandInputs a u slot p base dir img reserve,
    path.publishedPins a u slot p base dst len dir img ((Nat.le_add_right ..).trans reserve),
    (routeInput_room a u slot p F).1.trans base.symm,?_⟩
  have same : pub = B.bank (core (task.routeBank a.frame (withDemandBase other a.next)) origin edges cells) :=
    congrArg (fun reg => B.bank (core reg origin edges cells)) (withDemandBase_routeBank task a other a.next)
  rw [same] at path
  intro count
  exact path.demandPointers task a u slot p count (withDemandBase other a.next) origin edges cells room fits img
    ((Nat.le_add_right ..).trans reserve) rows

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI

import OAI.Computability.VPVNP.LiveProgramRouting

/-!
# Mode-dependent stage schedules of the native live group

The header emits zero, one or two. The same finite table serves every mode.
The following lists give the complete sequence of stage tags after ordinary
continuing calls within a stage are suppressed. The first tail group uses its
middle-cut exponents, later groups gather an incoming configuration, and the
last group installs the required accepting image instead of gathering an
outgoing configuration.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram
open BurstRAM BurstRAM.PrivateRAM

/-- The unit, pair, and evaluator-tail modes of the native live group. -/
inductive GroupMode where | unit | pair | tail deriving DecidableEq

/-- Encode unit, pair, and tail modes by the header flag ordinals zero, one, and two. -/
def GroupMode.flag : GroupMode → Fin 3
  | .unit => 0 | .pair => 1 | .tail => 2

/-- The seven stages that prepare a running evaluator's initial tape, from prefix-length
recovery through exponent scattering. -/
def prepareTail : List Stage := [Stage.prefixLength,Stage.adviceFrames,Stage.prefixPack,Stage.orderPack,
  Stage.prefixCopy,Stage.skeleton,Stage.scatter]

/-- Stage sequence for this group's mode and endpoint flags. A first tail group runs the tape
preparation only when the evaluator has extra states. -/
def schedule (p : UniversalMachine.Program) (mode : GroupMode) (first last : Bool) : List Stage :=
  [Stage.header,Stage.mode] ++ match mode with
  | .unit => []
  | .pair => [Stage.nominations,Stage.auxiliaryInit,Stage.auxiliaryCopy,Stage.pair,Stage.exponents]
  | .tail => [Stage.firstTail] ++
    (if first then [Stage.initialState] ++ (if p.extra = 0 then [] else prepareTail) else [Stage.oldGather]) ++
    [Stage.last,if last then Stage.finalState else Stage.newGather,Stage.transition]

/-- For a known checked header the three dynamic destinations are read from
exactly the same native router tables used by the complete instruction table. -/
def destination (t : Route.Target) : Option Stage := match t with
  | .reject | .accept => none
  | .jump j => if hj : j.val < 21 then some ⟨j.val,hj⟩ else none

/-- Select the next stage from the mode or endpoint flag at a router and from the program's
ordinary successor map elsewhere. -/
def successor (p : UniversalMachine.Program) (mode : GroupMode) (first last : Bool) (i : Stage) : Option Stage :=
  if i = Stage.mode then destination (modeTarget mode.flag)
  else if i = Stage.firstTail then destination (firstTarget (if first then 1 else 0))
  else if i = Stage.last then destination (lastTarget (if last then 1 else 0))
  else next p i

/-- The full stage list, including the exact terminal stage, follows the
successor function at each position. -/
def Follows (step : Stage → Option Stage) : List Stage → Prop
  | [] => True
  | [a] => step a = none
  | a :: b :: rest => step a = some b ∧ Follows step (b::rest)

theorem schedule_follows (p : UniversalMachine.Program) (mode : GroupMode) (first last : Bool) :
    Follows (successor p mode first last) (schedule p mode first last) := by
  cases mode <;> cases first <;> cases last <;> by_cases he : p.extra = 0 <;>
    simp (config := { decide := true }) [schedule,GroupMode.flag,prepareTail,Follows,successor,next,he,
      destination,modeTarget,firstTarget,lastTarget]

/-- Exact decomposition at any ordinary stage of the outer native program.
The source path has its original binary choices. The remaining path starts
with its specified transfer word and tag, retaining the cap on all reports. -/
noncomputable def stageEquiv (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (s : Stage) (fit : 21 ≤ 2^g.w) (f : ℕ) (st : Word g.w)
    (m : Memory g.w) (inv : Word g.w → Memory g.w → Prop) (cap : List (Report g.w) → Prop)
    (frame : LiveStageLink.TagFrame (Pieces.table (rows c p O))
      (Pieces.word g lit ∘ Pieces.bank (rows c p O)) (Pieces.word g lit (.geometry Layout.stageTag)) s f inv)
    (hi : inv st m) (tagged : m (Pieces.word g lit (.geometry Layout.stageTag)).val = LiveStageLink.tagWord g.w s) :
    let T := Pieces.table (rows c p O)
    let addr := Pieces.word g lit (.geometry Layout.stageTag)
    let pub := Pieces.word g lit ∘ Pieces.bank (rows c p O)
    (Σ a : LiveStageLink.Ordinary T (next p) pub addr s f st m, LiveStageLink.Remainder cap a) ≃
      ActualPaths (machine c p O g lit).program (f+(LiveStageLink.dispatchEvents addr s).length) st m cap := by
  dsimp only
  unfold machine Pieces.machine Pieces.program
  rw [Pieces.data_eq]
  exact LiveStageLink.ordinaryEquiv fit frame hi tagged

end LiveProgram

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.LiveProgramLayout
import OAI.Computability.VPVNP.LiveProgramPieces
import OAI.Computability.VPVNP.LiveRoute
import OAI.Computability.VPVNP.LiveAuxiliaryStages
import OAI.Computability.VPVNP.LiveExponentRows
import OAI.Computability.VPVNP.LiveEvaluatorAdviceFrames
import OAI.Computability.VPVNP.LiveEvaluatorAdvicePackStep
import OAI.Computability.VPVNP.LiveEvaluatorInitializeStages
import OAI.Computability.VPVNP.LiveEvaluatorReindexSkeleton
import OAI.Computability.VPVNP.LiveEvaluatorReindexNative
import OAI.Computability.VPVNP.LiveEvaluatorRAMSchedule
import OAI.Computability.VPVNP.LiveConfigGather
import OAI.Computability.VPVNP.CompressorRecordFrame

/-!
# The native control flow of the live group computation

The header program runs first and checks the incident cuts. Three short
routers read its mode, first-tail and last-group flags. Pair groups construct
the shadow of the auxiliary machine, execute the compressed pair routine,
and check the exponent update. Tail groups construct or read the incoming
configuration and check one evaluator transition against the required output.

The compressed pair computation is a separately supplied native instruction
table with eleven operands. Its two literal-prefix operands come from the
processor's own input. The other operands of the live program use the
length-only arithmetic expressions of `LiveProgramLayout`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram
open BurstRAM BurstRAM.PrivateRAM
open LiveHeaderDescriptors

/-- The twenty-one stage tags of the native live group program, covering header checks, the
pair counter and the evaluator tail. -/
abbrev Stage := Fin 21

namespace Stage
/-- Read and validate the incident header and cuts, and publish the mode and endpoint flags. -/
abbrev header : Stage := 0
/-- Read the checked mode tag to finish a unit group or enter its pair or evaluator-tail
computation. -/
abbrev mode : Stage := 1
/-- Guess the production counts for a primed pair and store one nominated word per grammar
label. -/
abbrev nominations : Stage := 2
/-- Prepare the copy descriptors for the primed pair counter's external header and nominated
histogram. -/
abbrev auxiliaryInit : Stage := 3
/-- Copy the recovered header fields and nominated counts into the pair counter's shadow
memory. -/
abbrev auxiliaryCopy : Stage := 4
/-- Execute the supplied compressed pair counter on its shadow header and workspace. -/
abbrev pair : Stage := 5
/-- Check that each outgoing exponent equals its incoming exponent plus the increments produced
by the pair path. -/
abbrev exponents : Stage := 6
/-- Test whether to initialize the evaluator at the first tail group or gather its incoming
configuration. -/
abbrev firstTail : Stage := 7
/-- Install the initial evaluator control state in the old configuration bank. -/
abbrev initialState : Stage := 8
/-- Pack the prefix length from the header's advice bits into a word for preparing the
evaluator input. -/
abbrev prefixLength : Stage := 9
/-- Check the packed prefix length and publish the operand frames for prefix packing, copying,
runtime initialization and exponent scatter. -/
abbrev adviceFrames : Stage := 10
/-- Pack the active prefix bits from the advice into words for the evaluator's input tape. -/
abbrev prefixPack : Stage := 11
/-- Pack the advised label ordering into the lookup table used to reindex exponents. -/
abbrev orderPack : Stage := 12
/-- Copy the packed program prefix into the evaluator's initial tape window. -/
abbrev prefixCopy : Stage := 13
/-- Write the evaluator runtime suffix with its width fields, delimiters and initially zero
exponent positions. -/
abbrev skeleton : Stage := 14
/-- Write the incoming exponent bits into the runtime tape using the advised label order. -/
abbrev scatter : Stage := 15
/-- Gather the incoming configuration from the left cut into the old evaluator state bank. -/
abbrev oldGather : Stage := 16
/-- Test whether the outgoing configuration must be the final accepting state or should be
gathered from the right cut. -/
abbrev last : Stage := 17
/-- Install the prescribed accepting evaluator endpoint in the new configuration bank. -/
abbrev finalState : Stage := 18
/-- Gather the outgoing configuration from the right cut into the new evaluator state bank. -/
abbrev newGather : Stage := 19
/-- Check one evaluator transition against the old and new configurations, including both tape
windows. -/
abbrev transition : Stage := 20
end Stage

private def jump (s : Stage) : Route.Target := .jump (s.castLE (by decide))

/-- Decode the mode flag. Zero accepts the unit group, one enters nominations and two enters
the first-tail test. -/
def modeTarget : Fin 3 → Route.Target := ![.accept,jump Stage.nominations,jump Stage.firstTail]
/-- Route flag zero to incoming-state gathering and flag one to evaluator initialization. Flag
two rejects. -/
def firstTarget : Fin 3 → Route.Target := ![jump Stage.oldGather,jump Stage.initialState,.reject]
/-- Route flag zero to outgoing-state gathering and flag one to the prescribed accepting state.
Flag two rejects. -/
def lastTarget : Fin 3 → Route.Target := ![jump Stage.newGather,jump Stage.finalState,.reject]

/-- A router selects its destination by writing the outer tag and returning
zero. Its accepting exit therefore finishes the whole group. The accepting
exit of an ordinary stage transfers to its specified successor. -/
def next (p : UniversalMachine.Program) : Stage → Option Stage :=
  ![some Stage.mode,none,some Stage.auxiliaryInit,some Stage.auxiliaryCopy,some Stage.pair,
    some Stage.exponents,none,none,if p.extra = 0 then some Stage.last else some Stage.prefixLength,
    some Stage.adviceFrames,some Stage.prefixPack,some Stage.orderPack,some Stage.prefixCopy,
    some Stage.skeleton,some Stage.scatter,some Stage.last,some Stage.last,none,
    some Stage.transition,some Stage.transition,none]

/-- The compressed pair's input ABI. The original processor's program prefix
is read from its literal input. Every group-specific value is obtained from
header or workspace addresses. -/
structure PairTable where
  /-- Number of instruction addresses in the supplied compressed pair counter. -/
  pcs : ℕ
  /-- Number of private registers used by the supplied compressed pair counter. -/
  regs : ℕ
  /-- Native instruction template of the compressed pair counter, with eleven public operand
  slots. -/
  table : Template pcs regs 11

namespace StageOperands

/-- Supply the router with the address of the flag to read and the outer stage-tag address to
update. -/
def router (flag : PublicExpr) : Fin 2 → PublicExpr := ![flag,Layout.stageTag]
/-- Supply the per-label guess width, the nomination counter base and the number of grammar
labels. -/
def nomination (c : Constants) : Fin 3 → PublicExpr := ![2*PublicExpr.d,Layout.counter c,c.grammarLabels]

/-- Fourteen operands describing header sizes, shadow and descriptor bases, and the physical
sources of the primed indices, advice, cuts and histogram. -/
def auxiliary (c : Constants) : Fin 14 → PublicExpr :=
  let s := c.lengths
  let b := Layout.header
  let lengths := HeaderLayout.width b .primedLeft
  ![s.h+2,s.advice,HeaderLayout.capacity s .exterior,c.grammarLabels,Layout.shadow c,Layout.descriptor c,
    lengths,lengths,HeaderLayout.leftIndex s b,HeaderLayout.rightIndex s b,HeaderLayout.advice s b,
    HeaderLayout.exterior s b .left,HeaderLayout.exterior s b .right,Layout.counter c]

/-- Supply the copy descriptor table base and the address of the final packed-end word in its
seventh descriptor. -/
def auxiliaryCopy (c : Constants) : Fin 2 → PublicExpr := ![Layout.descriptor c, Layout.descriptor c+18]

/-- Public operands of the compressed pair stage, including the original processor's literal
prefix word and length, workspace and shadow bases, counter and geometry. -/
def pair (c : Constants) : Fin 11 → InputOperand :=
  ![.prefixWord,.prefixLength,.geometry (Layout.pairWorkspace c),.geometry (Layout.shadow c),
    .geometry (Layout.counter c),.geometry c.grammarLabels,.geometry .n,.geometry .d,
    .geometry 0,.geometry (.lit c.motifLabels),.geometry (HeaderLayout.index Layout.header)]

/-- The left and right exponent bases, increment counter base, digit width and extent used to
check the exponent update. -/
def exponents (c : Constants) : Fin 5 → PublicExpr :=
  ![HeaderLayout.exponent c.lengths Layout.header .left,HeaderLayout.exponent c.lengths Layout.header .right,
    Layout.counter c,c.Z,c.lengths.e]

/-- Supply the evaluator control-state writer with its radius, destination bank, zero operand
and machine word width. -/
def control (c : Constants) (dest : PublicExpr) : Fin 4 → PublicExpr := ![c.radius,dest,0,PublicExpr.w]

/-- Five operands for reading one width-`w` prefix length from advice and storing it at offset
22 of the frame area. -/
def lengthPack (c : Constants) : Fin 5 → PublicExpr :=
  ![HeaderLayout.advice c.lengths Layout.header,Layout.adviceFrames c+22,PublicExpr.w,PublicExpr.w,1]

/-- Supply the frame publisher with the advice and prefix geometry, evaluator banks, exponent
dimensions and label-order map base. -/
def adviceFrames (c : Constants) : Fin 11 → PublicExpr :=
  ![HeaderLayout.advice c.lengths Layout.header,c.prefixCapacity,PublicExpr.w,Layout.adviceFrames c,
    Layout.packedPrefix c,c.radius,Layout.oldState c,c.Z,c.lengths.e,
    HeaderLayout.exponent c.lengths Layout.header .left,Layout.orderMap c]

/-- Operands for packing one order-map entry per label from the advice interval after the
prefix capacity, using the ceiling binary logarithm of the label count as its bit width. -/
def orderPack (c : Constants) : Fin 5 → PublicExpr :=
  let width := PublicExpr.clog2 c.labels
  ![HeaderLayout.advice c.lengths Layout.header + .w + c.prefixCapacity,Layout.orderMap c,width,c.labels*width,c.labels]

/-- Supply the selected cut's configuration address, destination state bank, word width and
number of configuration words. -/
def gather (c : Constants) (side : Side) (dest : PublicExpr) : Fin 4 → PublicExpr :=
  ![HeaderLayout.config c.lengths Layout.header side,dest,PublicExpr.w,c.configWords]

/-- Supply the evaluator step checker with the tape radius, old and new state bases and
transition scratch address. -/
def transition (c : Constants) : Fin 4 → PublicExpr :=
  ![c.radius,Layout.oldState c,Layout.newState c,Layout.transitionScratch c]

end StageOperands

private def framed {p r k : ℕ} (T : Template p r k) (b : PublicExpr) : Piece :=
  Piece.ofTable (CompressorRecords.Frame.compile T) (fun _ => b)

/-- Each row is a concrete native stage. `O` supplies the separate compressed
pair computation. Its input bank has the same fixed layout for every length. -/
def rows (c : Constants) (p : UniversalMachine.Program) (O : PairTable) : Stage → Piece :=
  let h := Layout.header
  let frame := Layout.adviceFrames c
  ![Piece.ofTable LiveHeaderProgram.program (HeaderLayout.operands c.lengths h),
    Piece.ofTable (Route.table modeTarget) (StageOperands.router (HeaderLayout.mode h)),
    Piece.ofTable LiveAuxiliaryStages.nomination (StageOperands.nomination c),
    Piece.ofTable LiveAuxiliaryStages.initialize (StageOperands.auxiliary c),
    Piece.ofTable LiveAuxiliaryStages.copy (StageOperands.auxiliaryCopy c),
    ⟨O.pcs,O.regs,11,O.table,StageOperands.pair c⟩,
    Piece.ofTable LiveExponent.digitTemplate (StageOperands.exponents c),
    Piece.ofTable (Route.table firstTarget) (StageOperands.router (HeaderLayout.firstTail h)),
    Piece.ofTable (LiveEvaluatorInitialize.putStage (LiveEvaluatorInitialize.controlTag p)) (StageOperands.control c (Layout.oldState c)),
    Piece.ofTable LiveEvaluatorAdviceBanks.stageTable (StageOperands.lengthPack c),
    Piece.ofTable LiveEvaluatorAdviceFrames.template (StageOperands.adviceFrames c),
    framed LiveEvaluatorAdviceBanks.stageTable frame,
    Piece.ofTable LiveEvaluatorAdviceBanks.stageTable (StageOperands.orderPack c),
    framed LiveEvaluatorInitialize.copyStage (frame+8),
    framed LiveEvaluatorReindexSkeleton.skeletonStage (frame+13),
    framed LiveEvaluatorReindex.scatterPhase (frame+17),
    Piece.ofTable LiveConfigGather.table (StageOperands.gather c .left (Layout.oldState c)),
    Piece.ofTable (Route.table lastTarget) (StageOperands.router (HeaderLayout.flag h .last)),
    Piece.ofTable LiveEvaluatorInitialize.finalStage (StageOperands.control c (Layout.newState c)),
    Piece.ofTable LiveConfigGather.table (StageOperands.gather c .right (Layout.newState c)),
    Piece.ofTable (LiveEvaluatorRAM.Schedule.program p) (StageOperands.transition c)]

/-- The fixed table is independent of input geometry, advice contents, and
own-prefix values. It can be compiled before choosing the eventual length. -/
def program (c : Constants) (p : UniversalMachine.Program) (O : PairTable) :=
  Pieces.program (rows c p O) (next p)

/-- Flatten the live stages' public operand expressions and append the outer stage-tag address. -/
def operand (c : Constants) (p : UniversalMachine.Program) (O : PairTable) :=
  Pieces.operand (rows c p O) Layout.stageTag

/-- Evaluate the flattened operands for the chosen geometry and literal processor prefix as
machine words. -/
def publicData (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) := Pieces.publicData (rows c p O) Layout.stageTag g lit

/-- Instantiate the linked live group program at the given word width with its evaluated public
operands. -/
def machine (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) := Pieces.machine (rows c p O) (next p) Layout.stageTag g lit

/-- Exact native all-path semantics at each length and clock, with choices
retained across all handoffs, including repeated equal evaluator outcomes. -/
theorem paths (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (hfit : 21 ≤ 2^g.w) (fuel : ℕ) (hf : 44 ≤ fuel)
    (st : Option (Word g.w)) (m : Memory g.w) (bs : List (List Bool)) :
    runSegment (machine c p O g lit).program fuel st m bs =
      LiveStageLink.stageSegment (Pieces.table (rows c p O)) (next p)
        (Pieces.word g lit ∘ Pieces.bank (rows c p O)) (Pieces.word g lit (.geometry Layout.stageTag)) fuel st m bs :=
  Pieces.paths_eq (rows c p O) (next p) Layout.stageTag g lit hfit fuel hf st m bs

end LiveProgram

end VPVNP
end Computability
end OAI

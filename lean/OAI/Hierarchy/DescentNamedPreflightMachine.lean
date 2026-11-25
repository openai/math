import OAI.Hierarchy.DescentNamedFundedPreflight
import OAI.Hierarchy.DescentNamedFixedBook
import OAI.Hierarchy.DescentTerminalOperandPadding
import OAI.Hierarchy.DescentTerminalPreflightPointerPages
import OAI.Hierarchy.DescentNamedTerminalPointerPins
import OAI.Hierarchy.DescentTerminalPrimitivePublicPair

namespace OAI
/-! # Fixed original terminal preprocessing, including every field and decoder -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler Catalyst DescentTerminalPointerDigits DescentTerminalCombinedRole
open DescentTerminalPrimitiveArena DescentTerminalPreflightSpace DescentTerminalLocalPortBook
open DescentStaticWordColumn DescentSIMDLookup ProtocolRAM DescentColonies.SplitRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Routing CallPool
noncomputable section
set_option quotPrecheck false
variable {F:Type} [Field F] {cp P:ℕ} (X:Approximation F cp P) (G:PoweredGadget F)
  (S:AtomSchedule) {k tail:ℕ} (baseGroups:S.baseGroups=2^tail) (radix:S.radix=2^k)
  (g p q drift:ℕ) (op:RotorSpec) (headerRows paidRows origin romBase:ℕ)
local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "nodes" => S.epochPower^S.localTokenExponent
local notation "maxArgs" => NativeBranch.privateSlotCapacity G S drift
local notation "s₀" => S.firstWidth G.b p
local notation "colors" => DescentPrimitivePalette.colors G s₀ (S.grainAt G.b p 0) op
local notation "groupLimit" => max 8 (2^S.capGain)
local notation "tagBits" => fun f:Fin 6=>DescentTerminalCombinedRole.width colors groupLimit maxArgs p drift f*nodes*(spec).groups
local notation "nodeBits" => Nat.clog 2 (nodes+1)
local notation "config" => (⟨nodeBits,Nat.clog 2 (maxArgs+1),fun _=>DescentOperandWidth.recordBits G S k tail drift 3 p,some nodes⟩:Widths)
local notation "index" => DescentExterior.terminalPin (S.groupWidth k tail 0+k) (S.groupWidth k tail S.length+k) (k*S.length)
local notation "psize" => poolBatchCount (s₀*1) p
local notation "f0" => publicCell (cap:=(spec).cap) (N:=nodes) (A:=maxArgs) (d:=(spec).scalar.pointerBits)
  3 q G.b psize (k*S.length) (spec).groups config
local notation "f7" => DescentTerminalPointerDigits.output (spec).cap nodes maxArgs 3 (spec).groups (spec).scalar.pointerBits
  (Nat.clog 2 (q+maxArgs+1)) q G.b psize config index
local notation "readBook" => decodeBook S G baseGroups radix p q 3 (spec).cap (spec).printBits (by decide)
local notation "fixedControl" => portTable (G:=4) (V:=(spec).vertices) (M:=(spec).vertices*(spec).arguments) (A:=(spec).arguments)
  (a:=Book.tokenBits ((spec).vertices*(spec).arguments)) q
local notation "shelf" => (spec).scanPages romBase q
local notation "blocks" => (spec).scalar.blocks
local notation "shops" => (spec).scalar.shops
variable (w:ℕ) (peer homes:Bank) (paid actor:Fin (2^k)→Bank) (signed:Fin (2^k)→Fin (2*((capCalendar G.b S.rounds g S.height).prod*256))→Bank)
    (matrix roleBase:ℕ) (rolePages:Fin 6→Bank) {Aphys:ℕ} (ptr:Fin 4→Fin Aphys→Fin (2^k)→Bank)
local notation "first" => DescentTerminalRoleTables.role tagBits rolePages roleBase
local notation "second" => DescentTerminalRoleTables.arity tagBits rolePages roleBase
local notation "previous" => DescentTerminalOperandRepack.padded (K:=maxArgs) ptr paid
local notation "raw" => (spec).pointerPages origin matrix previous signed
local notation "chart" => (raw).address (N:=nodes)
local notation "body" => (spec).purchasedProgram origin peer signed w q p nodeBits nodes maxArgs maxArgs paid actor
    first second chart f0 f7 readBook (shelf).total (shelf).modulo homes (shelf).boundaries fixedControl
/-- Every instruction and every lookup decoder is fixed by the original size,
gadget, and physical source-bank addresses; selection is read from RAM. -/
def fixedPreflight : Procedure w := ((shelf).program w).seq body
def fixedPreflightClocks :=
  4+10*(shelf).words+(spec).purchasedClocks origin peer signed q p paid actor chart
    (shelf).total (shelf).modulo homes (shelf).boundaries
def fixedPreflightMemory (m:Memory w) :=
  (spec).purchasedMem origin peer signed w q p nodeBits nodes maxArgs maxArgs paid actor
    first second chart f0 f7 readBook (shelf).total (shelf).modulo homes (shelf).boundaries fixedControl
    ((shelf).image m)

variable (m : Memory w)

local notation "run_" => fixedPreflight X G S baseGroups radix g p q drift op headerRows paidRows origin romBase w peer homes paid actor signed matrix roleBase rolePages ptr
local notation "end_" => fixedPreflightMemory X G S baseGroups radix g p q drift op headerRows paidRows origin romBase w peer homes paid actor signed matrix roleBase rolePages ptr m
local notation "clock_" => fixedPreflightClocks X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows origin romBase peer homes paid actor signed matrix ptr

theorem fixed_preflight_run
    (space:(shelf).stop≤origin)
  (before:(spec).Before origin paid actor signed peer (shelf).total (shelf).modulo homes (shelf).boundaries)
  (room:(spec).maskBase origin<2^w) (positive:0<w)
  (matrixEnd:matrix+1≤(spec).cohortEnd origin)
  (roleBefore:∀f,(rolePages f).base+(rolePages f).size≤(spec).cohortEnd origin)
  (roleEnd:roleBase+DescentTerminalRoleTables.count tagBits≤(spec).cohortEnd origin)
  (ptrEnd:∀f j b,(ptr f j b).base+(ptr f j b).size≤(spec).cohortEnd origin)
  (ptrRows:∀f j b,shops≤(ptr f j b).size)
  (paidRowsFit:∀b,shops≤(paid b).size) (signedRows:∀b j,shops≤(signed b j).size) : (run_).Exec m end_ clock_ ∧ CheapCode run_ ∧ (shelf).Reads end_ := by
  have roles:=(spec).role_fits origin room tagBits rolePages roleBase roleBefore roleEnd
  have ptrE:∀f j b,(previous f j b).base+(previous f j b).size≤(spec).cohortEnd origin:=by
    intro f j b;unfold DescentTerminalOperandRepack.padded;split
    · exact ptrEnd _ _ _
    · exact before.oldPaid _
  have ptrH:∀f j b,shops≤(previous f j b).size:=by
    intro f j b;unfold DescentTerminalOperandRepack.padded;split
    · exact ptrRows _ _ _
    · exact paidRowsFit _
  have strips:0<(spec).strips:=by change 0<3+_;omega
  have columns_:0<(spec).scalar.columns:=by
    change 0<3+nodes+4*(nodes*maxArgs)+2*(spec).cap
    omega
  exact (spec).funded_preflight romBase q origin peer signed w p nodeBits nodes maxArgs maxArgs paid actor first
    second chart f0 f7 readBook homes fixedControl m space before room positive strips columns_ roles.1 roles.2
    ((spec).pointer_fits origin matrix previous signed room matrixEnd ptrE ptrH before.oldCables signedRows nodes)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI

import OAI.Hierarchy.DescentTerminalPreflightProgramRoom

namespace OAI
/-! # Single clock and instruction bill for the original terminal address allocation -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentSIMDLookup DescentTerminalPreflightInvoice DescentTerminalLocalPortBook
open DescentTerminalCombinedRole DescentTerminalPointerDigits DescentTerminalHeaderDraft
open DescentStaticWordColumn DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false

private theorem invoice_names {w : ℕ}
    (population actors primitive shelves printer controls cables widths literals header : Procedure w) :
    names (((((population.seq actors).seq primitive).seq (shelves.seq printer)).seq controls).seq
      ((cables.seq widths).seq (literals.seq header))) =
    names (((((((((population.seq actors).seq primitive).seq shelves).seq printer).seq controls).seq
      cables).seq widths).seq literals).seq header) := by
  simp only [names_seq, Nat.add_assoc]

private theorem invoice_scale (u shops factor paid bw : ℕ) :
    6050000 * ((u + shops * (4 * factor)) * (bw + 1) + paid * (bw + 1)) ≤
      24200000 * ((u + shops * factor) * (bw + 1) + paid * (bw + 1)) := by
  ring_nf
  omega

variable (x:DescentTerminalPreflightSpace.Spec) (base:ℕ) (peer:Bank)
    (wing:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (w q p nd nodes hidden args:ℕ) (oldPaid actor:Fin x.scalar.blocks→Bank)
    (first second:Shelf) (chart:Fin x.scalar.columns→Fin x.scalar.blocks→Gather.Address)
    {out0 out7:ℕ} (f0:(Fin x.scalar.columns→Cell x.scalar.pointerBits)→Cell out0)
    (f7:(Fin x.scalar.columns→Cell x.scalar.pointerBits)→Cell out7)
    (decode:(Fin x.strips→Cell x.printBits)→Directory 4 x.vertices x.arguments)
    (count modulo homes:Bank) (boundary:ℕ) (control:ℕ→ℕ)

local notation "s" => x.scalar
local notation "H0" => (s).shops
local notation "C" => x.issuedBook base peer wing
local notation "P" => x.publicWidths base
local notation "A" => x.draft base count modulo homes boundary
local notation "ports" => x.eventInputs base peer wing
local notation "T" => x.cables base peer wing
local notation "c" => x.controls base
local notation "at0" => x.primitive base
local notation "popStart" => x.cohortEnd base
local notation "next" => DescentTerminalPriorArena.actStart s x.groups x.paidLanes x.paidBits x.externalBits popStart
local notation "takeActor" => (fun (_:Fin (s).blocks) (u:Cell 1)=>u)
local notation "pop" => DescentTerminalPopulation.RAM.issue H0 x.groups x.paidLanes x.paidBits nd x.externalBits popStart oldPaid (x.census base) w
local notation "live" => DescentTerminalActorRepack.program takeActor H0 x.groups x.actorLanes next actor w
local notation "prim" => DescentTerminalPrimitiveNames.program w first second at0 ((s).gather at0) H0 chart f0 f7
  ((s).sources at0 (x.population base)) (s).countBits ((s).counting at0) ((s).widths at0) q hidden nodes args x.groups p
local notation "weights" => Book.WeightShelf.program x.vertices x.arguments (x.weights base) w
local notation "book" => (C).prefix decode (x.vertices*x.arguments) w 6 le_rfl
local notation "controls" => (c).program w control (Book.expression (x.parts base))
local notation "rack" => (T).program w q p
local notation "exterior" => (P).program w q p
local notation "literals" => litProc w (x.literalBase base) (A).rows
local notation "draft" => machine A ports x.degree w

/-- Execution order ends at the last written source/format digits, immediately
before the masked meter. It includes both genuine row-number scans. -/
def purchasedProgram := (((((pop).seq live).seq prim).seq ((weights).seq book)).seq controls).seq
  (((rack).seq exterior).seq ((literals).seq draft))

def purchasedClocks :=
  DescentTerminalPopulation.RAM.ticks H0 x.groups x.paidLanes x.paidBits x.externalBits popStart oldPaid (x.census base)+
  DescentTerminalActorRepack.ticks (a:=1) H0 x.groups x.actorLanes next actor+
  DescentTerminalPrimitiveNames.clocks (s).pointerBits (s).countBits ((s).gather at0) H0 chart+
  (4+10*Book.WeightShelf.words x.vertices x.arguments)+(C).time 6 le_rfl+
  (c).time (Book.expression (x.parts base))+(T).time q p+(P).clocks q p+
  (4+40*DescentTerminalHeaderDraft.span (A).rows)+clocks A ports x.degree

local notation "machine_" => purchasedProgram x base peer wing w q p nd nodes hidden args oldPaid actor
  first second chart f0 f7 decode count modulo homes boundary control
local notation "ticks_" => purchasedClocks x base peer wing q p oldPaid actor chart count modulo homes boundary

theorem purchased_price (h bw factor paid:ℕ) (room:ProgramRoom x base peer wing h factor paid)
    (hp:0<H0) (hf:0<factor) (degrees:x.degree=3) :
    (names machine_+ticks_)*(bw+1)≤24200000*((2^(h/2)+H0*factor)*(bw+1)+paid*(bw+1)) := by
  have job:=DescentTerminalPreflightInvoice.total w H0 x.groups x.paidLanes x.paidBits nd x.externalBits popStart
    x.actorLanes next oldPaid (x.census base) takeActor actor P q p A ports (x.literalBase base)
    first second at0 ((s).gather at0) (s).countBits ((s).counting at0) ((s).widths at0) hidden nodes args chart f0 f7
    ((s).sources at0 (x.population base)) C x.vertices x.arguments (x.weights base) decode T c control (x.parts base)
    h bw (4*factor) paid (by simpa only [Nat.add_assoc] using room.menus) room.priorPacking
    le_rfl le_rfl room.widthAndDraft hp (by omega) ((x.rasters base peer wing).source_work degrees)
    room.books room.cables room.counts room.bookRows room.cableRows room.tapeCap room.weights
    room.pointer room.counter room.scalarRows room.data room.shift room.addresses
  unfold purchasedProgram purchasedClocks
  rw [congrArg (fun deg => machine A ports deg w) degrees,
    congrArg (fun deg => clocks A ports deg) degrees, invoice_names]
  exact job.trans (invoice_scale _ _ _ _ _)

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI

import OAI.Hierarchy.DescentTerminalFixedSlices
import OAI.Hierarchy.DescentScheduledResetAtPorts
import OAI.Hierarchy.DescentTerminalResetDatedFields

namespace OAI
/-! The terminal field reader at the last cursor. Old-host padding, the presence pass,
the ingress and the operand repack all precede the returned register pages. -/
namespace Hierarchy.DescentTerminalFixedSlices.Phase
open DescentDatedAddressBook DescentCompiler DescentSixParty DescentTerminalSliceRuns
open DescentSIMDLookup DescentTerminalPointerDigits DescentOperandCandidateLookup DescentPackedColony DescentPackedZip
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false

section Published
open scoped Fin.CommRing

variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "start" => (v).sheetsStart b
local notation "plan" => (v).linkedRankInputs u.sectors start
local notation "rendered" => (v).renderFromRanks plan b
local notation "actorBase" => (v).middle.stop b
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits

/-- Output of a dated reset, read at the seven banks supplied by the terminal chart. -/
private abbrev PublishedFields (ok : u.Ready) (bits : (s).coeff=(v).nodeBits)
    (small : 2*(A).candidates<2^(A).queryBits) (m dst : Memory w)
    (field : Fin 7 → Fin (v).argumentSlots → Fin (A).blocks → Bank) : Prop :=
    ∃actorMem,((head).seq ((v).actor.actorBody u.actor actorBase w)).Exec m actorMem
        (ht+(v).actor.actorTicks u.actor actorBase w) ∧
      ∀(q : Fin (A).fields→Fin (A).hosts→Fin (A).groups→Option (Fin (2*(A).candidates)))
       (raw : Fin (A).fields→Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
       (kept value : Fin (A).fields→Fin (A).hosts→Fin (A).groups→Cell (s).coeff),
       (∀i,Source ((s).query i) (fun h g=>code small (q i h g)) (A).lanes (u.operandEntry ok actorMem)) →
       (∀i,Source ((s).kept i) (kept i) (A).lanes (u.operandEntry ok actorMem)) →
       (∀i j,Source ((v).previous (s) rendered b i j) (raw i j) (A).lanes (u.operandEntry ok actorMem)) →
       (∀i h g,(kept i h g).val+
        (selected (q i) (fun j h g=>((raw i j h g).val:Cell (s).coeff)) h g).val=(value i h g).val) →
       ∀(f:Fin 7) (arg:Fin (v).argumentSlots) (x:Fin (A).blocks),
       Reads (field f arg x) (fun h g=>encode (v).nodeBits (v).nodes (fun n=>
         (value ((v).operandOrdinal (s) f (arg.cast ok.slots.symm) x (n.cast ok.nodes.symm)) h g).cast (congrArg (2^·) bits)))
         (A).lanes dst

private abbrev PublishedDecoder (z : u.FinalInputs)
    (field : Fin 7 → Fin (v).argumentSlots → Fin (A).blocks → Bank) : Prop :=
  ∀ (ok : u.Ready) (_room : z.Room) {m mid dst : Memory w}
    (_prefix : u.throughOperandDate.Runs m mid) (_run : (PhysicalReset.date z).Runs m dst)
    (bits : (s).coeff=(v).nodeBits) (small : 2*(A).candidates<2^(A).queryBits),
      PublishedFields u ok bits small m dst field

private theorem decoderFromRun (z : u.FinalInputs) :
    PublishedDecoder u z ((v).terminalField b) :=
  fun ok room {_ _ _} pre run bits small => PhysicalReset.dated_fields z ok room pre run bits small

end Published

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree payload : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (ports : Chronology.DatePorts) (cursor : ℕ)
local notation "outer" => ports.priorStart k cursor
local notation "entered" => PhysicalReset.scheduledAtPorts G S board k tail age p f gain drift degree payload
  ordinary op (S.firstWidth G.b p) (S.grainAt G.b p 0) ports cursor
local notation "stage₀" => (entered).inner
local notation "inner" => (stage₀).stageStart outer

/-- Use the actual preceding host and presence allocation, then the new reset's ingress. -/
def atPorts : Phase F :=
  scheduled G S board k tail age p f gain drift degree payload ordinary op
    ports.operandLanes ports.roleLanes ports.venue ports.io.wire ports.io.roster outer

local notation "P" => atPorts G S board k tail age p f gain drift degree payload ordinary op ports cursor
local notation "v" => (stage₀).successor
local notation "base" => (stage₀).rebased inner
local notation "A" => (v).receiver

theorem registered_layout :
    (entered).priorStart=outer ∧ (P).output=(v) ∧ (P).dateBase=base ∧
    (P).output.metadataEnd (P).dateBase=(entered).fullEnd := ⟨rfl,rfl,rfl,rfl⟩

theorem registered_registers (x : Fin (A).blocks) :
    (P).chart (leading 0) x=.hosts ((v).terminalRole base (x.cast (P).tokenBlocks)) ∧
    (P).chart (leading 1) x=.hosts ((v).terminalArity base (x.cast (P).countBlocks)) ∧
    ∀(ch:Fin 3)(j:Fin (v).argumentSlots),(P).chart (triple ch j) x=
      .hosts ((v).terminalField base ⟨4+ch.val,by omega⟩ j x) :=
  ⟨token_bank (v) base (P).tokenBlocks (P).countBlocks x,
   count_bank (v) base (P).tokenBlocks (P).countBlocks x,
   fun ch j=>span_bank (v) base (P).tokenBlocks (P).countBlocks ch j x⟩

/-- Each of the seven physically published operands uses the same rebased address as the
terminal slice chart. Both execution witnesses start at the actual interior DateInputs entry. -/
theorem registered_fields {w : ℕ} {u : (stage₀).DateInputs inner w} (z : u.FinalInputs) :
    PublishedDecoder (a:=stage₀) (floor:=inner) (w:=w) u z ((P).output.terminalField (P).dateBase) :=
  @decoderFromRun stage₀ inner w u z

end
end Hierarchy.DescentTerminalFixedSlices.Phase

end OAI

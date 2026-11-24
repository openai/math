import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherLayout
import OAI.Computability.VPVNP.PairSimulationTerminalSiteLinear
import OAI.Computability.VPVNP.PairVertexImage

/-! # Relocatable terminal endpoint gather

Each incoming slot first reads its matching outgoing slot. Both passes then
read the width and exclusive prefix of that outgoing slot and copy the
corresponding shared wire words to the site's private argument buffer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalRootGather

open BurstRAM PrivateRAM
open scoped Fin.CommRing

/-- Symbolic register names shared with the site bootstrap. The gather maps the first nine
names to its own temporaries, the next eleven to saved fields and the final three to DFS
registers. -/
abbrev Reg := TerminalSiteStart.Reg
/-- Straight-line instruction format used for the gather's initialization and per-slot
directory reads. -/
abbrev Line := TerminalSiteStart.Line
/-- Names one of the nine gather temporaries used for wire addresses, the private destination,
and slot loop bounds. -/
abbrev tmp := TerminalSiteStart.dfs
/-- Names a bootstrap register from which the gather reads the site ordinal, root, slot counts
or endpoint array heads. -/
abbrev save := TerminalSiteStart.saved

/-- Twelve instructions that load the private argument stride, compute the root's destination
address and set the first slot, exclusive limit and unit increment for the outgoing scan. -/
def bootLines : List Line :=
  [.pub (tmp 8) 6, .load (tmp 0) (tmp 8), .lit (tmp 3) 7,
   .bin .add (tmp 0) (tmp 0) (tmp 3), .load (tmp 0) (tmp 0),
   .bin .mul (tmp 0) (tmp 0) (save VertexImage.root), .bin .add (tmp 2) (tmp 8) (tmp 0),
   .bin .div (tmp 0) (save VertexImage.slots) (save VertexImage.finalSites),
   .bin .mul (tmp 7) (save VertexImage.ordinal) (tmp 0), .bin .add (tmp 6) (tmp 7) (tmp 0),
   .copy (tmp 5) (tmp 7), .lit (tmp 3) 1]

instance : NeZero bootLines.length := ⟨by decide⟩

/-- Reads a slot's width and exclusive prefix to compute its source interval in the wire bank.
The incoming pass first reads the matched outgoing slot from the inverse incidence table. -/
def headerLines (b : Bool) : List Line :=
  (if b then [.bin .add (tmp 4) (save VertexImage.incoming) (tmp 5), .read (tmp 0) (tmp 4)]
   else [.copy (tmp 0) (tmp 5)]) ++
  [.bin .add (tmp 4) (save VertexImage.widths) (tmp 0), .read (tmp 1) (tmp 4),
   .bin .add (tmp 4) (save VertexImage.prefixBase) (tmp 0), .read (tmp 0) (tmp 4),
   .bin .add (tmp 0) (save VertexImage.wires) (tmp 0), .bin .add (tmp 1) (tmp 1) (tmp 0)]

/-- Labels for gather initialization and the two slot scans. Each pass has a loop test,
directory reads, a wire-copy loop and a slot increment, with a cursor reset between passes. -/
inductive PC where
  | boot (i : Fin bootLines.length)
  | scan (b : Bool)
  | header (b : Bool) (i : Fin (headerLines b).length)
  | bits (b : Bool) (i : Fin 5)
  | advance (b : Bool)
  | reset
  deriving DecidableEq, Fintype

/-- Index of the first directory instruction for a slot in the selected scan direction. -/
def firstHeader (b : Bool) : Fin (headerLines b).length := ⟨0, by cases b <;> decide⟩

/-- Extends the labels of a straight-line gather block by one position holding its
continuation, so the last instruction can target the next phase. -/
def blockPC {n p : ℕ} (pc : Fin n → Fin p) (done : Fin p) : Fin (n+1) → Fin p := Fin.lastCases done pc

/-- Emits the gather instruction at a symbolic label. The outgoing pass resets the slot cursor
for the incoming pass, which transfers to the supplied continuation after its last slot. -/
def rows {w p r : ℕ} (pc : PC → Fin p) (reg : Reg → Fin r) (br : Fin 5 ↪ Fin r) (done : Fin p) :
    PC → Instr w p r 11
  | .boot i => (bootLines[i]).emit reg id (blockPC (pc ∘ PC.boot) (pc (.scan false)) i.succ)
  | .scan b => .jumpEq (reg (tmp 5)) (reg (tmp 6))
      (if b then done else pc .reset) (pc (.header b (firstHeader b)))
  | .header b i => ((headerLines b)[i]).emit reg id (blockPC (pc ∘ PC.header b) (pc (.bits b 0)) i.succ)
  | .bits b i => EndpointBits.instruction (pc ∘ PC.bits b) br (pc (.advance b)) i
  | .advance b => .binary .add (reg (tmp 5)) (reg (tmp 5)) (reg (tmp 3)) (pc (.scan b))
  | .reset => .copy (reg (tmp 5)) (reg (tmp 7)) (pc (.scan true))

variable {w p r : ℕ}

/-- Assigns the first five gather temporaries to the endpoint copy loop as source cursor,
exclusive end, destination cursor, unit increment and transfer word. -/
def bitRegs (reg : Reg ↪ Fin r) : Fin 5 ↪ Fin r := (Fin.castAddEmb 4).trans (Function.Embedding.inl.trans reg)

/-- Requires the machine to contain every gather instruction at its assigned label, with the
specified register bank and final continuation. -/
def Linked (M : Machine w p r 11) (pc : PC → Fin p) (reg : Reg ↪ Fin r) (done : Fin p) :=
  ∀ i, M.code (pc i) = rows pc reg (bitRegs reg) done i

/-- Resolves gather register names into the segment's nine private temporaries, the eleven
saved bootstrap registers and the first three host DFS registers. -/
def regMap (dfs : Fin 9 ↪ Fin r) (saved : Fin 11 ↪ Fin r) (work : Fin 9 ↪ Fin r) : Reg → Fin r :=
  Sum.elim work (Sum.elim saved (fun i => dfs (Fin.castAdd 6 i)))

/-- Finite vertex-image segment for gathering the terminal root's endpoint packet. It enters at
initialization and allocates nine private temporaries for both scan directions. -/
noncomputable def segment : VertexImage.Segment where
  count := Fintype.card PC
  privateRegs := 9
  entry := Fintype.equivFin PC (.boot 0)
  row pc dfs saved work done i :=
    rows (pc ∘ Fintype.equivFin PC) (regMap dfs saved work) ((Fin.castAddEmb 4).trans work) done
      ((Fintype.equivFin PC).symm i)

theorem resize_rows (pc : PC → Fin p) (reg : Reg → Fin r) (br : Fin 5 ↪ Fin r) (done : Fin p) (i : PC) :
    (rows (w := 5) pc reg br done i).resize w = rows pc reg br done i := by
  cases i with
  | boot i | header _ i => exact TerminalSiteStart.Line.resize_emit ..
  | bits b i => fin_cases i <;> rfl
  | _ => rfl

/-- Saved fields read by this segment. The private geometry pointer and
stride are initialized by the previous stage. -/
structure Saved (L : Layout) (reg : Reg ↪ Fin r) (c : Config w p r) : Prop where
  ordinal : c.reg (reg (save VertexImage.ordinal)) = (L.vertex : Word w)
  root : c.reg (reg (save VertexImage.root)) = (L.root : Word w)
  sites : c.reg (reg (save VertexImage.finalSites)) = (L.sites : Word w)
  slots : c.reg (reg (save VertexImage.slots)) = (L.slots : Word w)
  widths : c.reg (reg (save VertexImage.widths)) = (L.widthHead : Word w)
  incoming : c.reg (reg (save VertexImage.incoming)) = (L.incomingHead : Word w)
  prefixBase : c.reg (reg (save VertexImage.prefixBase)) = (L.prefixHead : Word w)
  wires : c.reg (reg (save VertexImage.wires)) = (L.wires : Word w)

/-- Register frame for a gather run. The two configurations agree on the persistent word and on
every register outside the nine gather temporaries. -/
def Frame (reg : Reg ↪ Fin r) (c out : Config w p r) :=
  out.persistent = c.persistent ∧ ∀ j, (∀ i, reg (tmp i) ≠ j) → out.reg j = c.reg j

/-- For any remaining fuel and choice bits, execution from the initial configuration produces
the given event prefix followed by the continuation from the final configuration on the
same external memory. -/
def Prefix (M : Machine w p r 11) (m : Memory w) (c : Config w p r) (es : List (Event w)) (out : Config w p r) :=
  ∀ fuel bs, execute M.program (fuel+es.length) c m bs =
    (execute M.program fuel out m bs).map (fun rep => ⟨es ++ rep.events,rep.result⟩)

theorem linked_boot {M : Machine w p r 11} {pc : PC → Fin p} {reg : Reg ↪ Fin r} {done : Fin p}
    (hl : Linked M pc reg done) (i : Fin bootLines.length) :
    let labels := blockPC (pc ∘ PC.boot) (pc (.scan false))
    M.code (labels i.castSucc) = (bootLines[i]).emit reg id (labels i.succ) := by
  simpa only [rows, blockPC, Fin.lastCases_castSucc,Function.comp_apply] using hl (.boot i)

theorem linked_header {M : Machine w p r 11} {pc : PC → Fin p} {reg : Reg ↪ Fin r} {done : Fin p}
    (hl : Linked M pc reg done) (b : Bool) (i : Fin (headerLines b).length) :
    let labels := blockPC (pc ∘ PC.header b) (pc (.bits b 0))
    M.code (labels i.castSucc) = ((headerLines b)[i]).emit reg id (labels i.succ) := by
  simpa only [rows, blockPC, Fin.lastCases_castSucc,Function.comp_apply] using hl (.header b i)

end PairSimulation.TerminalRootGather

end VPVNP
end Computability
end OAI

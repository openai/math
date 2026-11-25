import OAI.Hierarchy.DescentTerminalRegisteredHeaderDigit
import OAI.Hierarchy.DescentTerminalPointerSource
import OAI.Hierarchy.DescentTerminalPointerPages

namespace OAI
/-! # Recovering the terminal operand from its four original pointer pages -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSIMDLookup DescentOperandStateBanks DescentPackedColony ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap N K d : ℕ} (fmt : Widths) (raw : Source cap N K d) (group : ℕ)

/-- The pre-remix pointer stores the original exterior identifier.
Each live constructor has exactly one image under the four-field encoding. -/
theorem decode_fields (loc : Fin (N*K)) (ptr : Pointer)
    (digits : ∀f : Fin 4,fmt.nodeDigit (fmt.pointer f) (nodeOf loc).val group
      (raw (pcol f loc)).val=ptr.header f) :
    (decode D fmt (fun _ _ j=>j) raw group).pointer loc=ptr := by
  unfold decode
  dsimp only
  simp only [digits]
  cases ptr <;> rfl

theorem header_injective {left right : Pointer} (cols : ∀f : Fin 4,left.header f=right.header f) : left=right := by
  let rebuild (f : Fin 4→ℕ) : Pointer :=
    if f 0=0 then .privateWord (f 2) else if f 0=1 then .cable (f 1) (f 2) (f 3) else .pin (f 2) (f 3)
  have original (p : Pointer) : rebuild p.header=p := by cases p <;> rfl
  exact (original left).symm.trans ((congrArg rebuild (funext cols)).trans (original right))

theorem source_pointer_fields (t : CellInputs D cap N K) (read : SourceRead fmt raw group t)
    (loc : Fin (N*K)) (live : t.active loc) (ptr : Pointer)
    (words : ∀f : Fin 4,fmt.nodeDigit (fmt.pointer f) (nodeOf loc).val group (raw (pcol f loc)).val=ptr.header f) :
    t.pointer loc=ptr := header_injective (fun f=>(read.fields loc live f).symm.trans (words f))

theorem inactive_argument (t : CellInputs D cap N K) (q scale size : ℕ) (loc : Fin (N*K)) (unused : ¬t.active loc) :
    t.argument q scale size loc=0 := by simp [CellInputs.argument,unused]

theorem nodeDigit_low {d width n g a K : ℕ} (fmt : Widths) (cap : fmt.nodeCapacity=some K)
    (fits : (width*K)*(g+1)≤d) :
    fmt.nodeDigit width n g (a%2^d)=fmt.nodeDigit width n g a :=by
  have low : digit (width*K) g (a%2^d)=digit (width*K) g a := by
    unfold digit
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow _ fits)]
  simp only [Widths.nodeDigit,cap,low]


end
end Hierarchy.DescentTerminalPointerDigits

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup DescentTerminalPointerDigits ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)

variable {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B→Label G s Z op) (pointer : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)

variable {ports r B number room shape op label pointer flags}
variable {m : Memory w} (held : ArchiveRead ports r B number room shape op label pointer flags m)
    (fmt : Widths) (capacity : fmt.nodeCapacity=some ports.nodes) (width : ∀f,fmt.pointer f=ports.operandBits)
    (positive : 0<ports.operandLanes) (packed : (ports.operandBits*ports.nodes)*ports.operandLanes≤w)

variable {K d₀ : ℕ} (one : chunks ports.venue.groups ports.operandLanes=1) (current : Memory w)
    (x : Fin (2^ports.venue.k)) (h : Fin ports.operandHosts) (g : Fin ports.venue.groups)
local notation "args_" i => ((finProdFinEquiv (m:=ports.nodes) (n:=K)).symm i).2
variable (i : Fin (ports.nodes*K)) (inCap : (finProdFinEquiv.symm i : Fin ports.nodes×Fin K).2.val<ports.argumentsPerNode)
local notation "arg" => (⟨(args_ i).val,inCap⟩ : Fin ports.argumentsPerNode)
variable (y : NodeOrder.All B)
    (place : slotAt ports r B number room x (nodeOf i) h g=some y)
    (active : (finProdFinEquiv.symm i : Fin ports.nodes×Fin K).2.val<(occurrences (shape.sites y.1) y.2).length)
local notation "payload" => (pointer y (args_ i).val)

variable (pages : Gather.Pages (2^ports.venue.k) r.placement.cap K)
    (hold : ∀f,current ((pages.pointers f (finProdFinEquiv.symm i : Fin ports.nodes×Fin K).2 x).base+h.val)=
      m ((previousBank ports.rangeLayout ports.archive.arguments x
        (DescentOperandStateBanks.page (Fin.castLE (by decide : 4≤7) f)
          ⟨(finProdFinEquiv.symm i : Fin ports.nodes×Fin K).2.val,inCap⟩)).base+h.val))
    (fits : (ports.operandBits*ports.nodes)*(g.val+1)≤d₀)
local notation "rawPage" => pages.source (N:=ports.nodes) (d:=d₀) current x h

include held one capacity width positive packed place active hold fits in
/-- The gather's low-word cast preserves each occupied pointer field. -/
theorem ArchiveRead.gathered_header_digit (f : Fin 4) :
    fmt.nodeDigit (fmt.pointer f) (nodeOf i).val g.val (rawPage (pcol f i)).val=(payload).header f :=by
  change fmt.nodeDigit (fmt.pointer f) (nodeOf i).val g.val
    ((current ((pages.address (pcol f i) x).atHost h)).val%2^d₀)=_
  have lowRoom : ((fmt.pointer f)*ports.nodes)*(g.val+1)≤d₀:=by rw [width];exact fits
  rw [pages.pointer,Gather.Address.atHost,nodeDigit_low fmt capacity lowRoom,hold]
  obtain ⟨addr,group⟩:=singleton_pitch one positive h g
  have data:=held.terminal_header_digit fmt capacity width positive packed x (nodeOf i) arg f h g y place active
  rw [addr,group] at data
  exact data

include held one capacity width positive packed place active hold fits in
/-- At a real argument, decoding the original gathered page needs only the
archived physical reads and their address frame. -/
theorem ArchiveRead.gathered_pointer_at :
    (decode r.placement.degree fmt (fun _ _ j=>j) rawPage g.val).pointer i=payload :=by
  apply decode_fields
  exact held.gathered_header_digit fmt capacity width positive packed one current x h g i inCap y place active pages hold fits

include held one capacity width positive packed place active hold fits in
/-- A semantic record read from the gathered cell has the same live pointer.
Columns outside the available argument range may hold arbitrary padding. -/
theorem ArchiveRead.cell_pointer_at (t : CellInputs r.placement.degree r.placement.cap ports.nodes K)
    (read : SourceRead fmt rawPage g.val t) (live : t.active i) :
    t.pointer i=payload :=by
  apply source_pointer_fields fmt _ g.val t read i live payload
  exact held.gathered_header_digit fmt capacity width positive packed one current x h g i inCap y place active pages hold fits

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI

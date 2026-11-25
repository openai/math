import OAI.Hierarchy.DescentDatedOperandDigits
import OAI.Hierarchy.DescentDonorWindow
import OAI.Hierarchy.DescentPackedOperand
import OAI.Hierarchy.DescentDatedOperandLookup

namespace OAI
/-! # Physical ordinary operand reads from the donor word retained by the matcher -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Operand
open DescentSIMDLookup DescentPackedZip DescentPackedOperand Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {cap c : ℕ}

variable (f : Shape) (profile branch slots depth trim width indexBits : ℕ) (block : Fin f.blocks)

def datum (first : Bool) (sample : Cell (2+c)) : Bool :=
  if first then samePre sample else !samePre sample && samePost sample

/-- The four columns are the two disjoint captures and the two radix digits of
the raw cable ticket. The capture branch reads the donor word and role selected
by the incoming numeric ticket. -/
def values (v : Parts f) (old : Fin f.cap) (role : Fin 11) : Fin 4→Cell (width+2) :=
  let issued : Donor 3 f.names f.widths:=unpackDonor
    ((encode _ (f.blocks*f.cap)).symm (chip f f.cap profile branch slots v) (finProdFinEquiv (block,old)))
  let sample:=report depth trim slots issued role
  ![flagCell width (datum true sample),flagCell width (datum false sample),
    (old.val:Cell (width+2)),(role.val:Cell (width+2))]

def lookupField (field : Fin 4) (v : Cell (totalBits f)) (r : Cell indexBits) : Cell (width+2) :=
  match decode f.cap r.val with
  | some x=>values f profile branch slots depth trim width block (separate f v) x.1 x.2 field
  | none=>0

theorem lookup_hole (field : Fin 4) (v : Cell (totalBits f)) :
    lookupField f profile branch slots depth trim width indexBits block field v 0=0 := by
  simp [lookupField,decode]

theorem lookup_real (field : Fin 4) (v : Parts f) (old : Fin f.cap) (role : Fin 11)
    (bits : ticket old role<2^indexBits) :
    lookupField f profile branch slots depth trim width indexBits block field (combine f v) (ticket old role:Cell indexBits)=
      values f profile branch slots depth trim width block v old role field := by
  simp only [lookupField,Fin.val_cast_of_lt bits,decode_ticket,separate_combine]

def gates (i : Fin 4) : Book.Gate :=
  ⟨totalBits f,indexBits,width+2,lookupField f profile branch slots depth trim width indexBits block i⟩

/-- Both source banks are previous program outputs. A source row may contain any
word. All instructions and their exact clock depend only on the finite chart.
The last partial group is included in the equality for every physical row. -/
theorem field_run {H groups M w : ℕ} (i : Fin 4) (tables : Tables) (prior select : Bank)
    (out : ℕ) (m : Memory w) (data : Fin H→Fin groups→Parts f)
    (idx : Fin H→Fin groups→Cell indexBits)
    (fit : DescentPackedZip.Fits tables (.lookup prior .row) (.lookup select .row)
      (totalBits f) indexBits M out w) (safe : out+H*chunks groups M<2^w)
    (rom : Static tables (lookupField f profile branch slots depth trim width indexBits block i) M m)
    (before : DescentPackedZip.Source (.lookup prior .row) (fun h g=>combine f (data h g)) M m)
    (picked : DescentPackedZip.Source (.lookup select .row) idx M m) :
    let term:=tables.read (.lookup prior .row) (.lookup select .row)
    let last:=image out (H*chunks groups M) term m
    (scan w out (H*chunks groups M) term).Exec m last (4+(H*chunks groups M)*(2*term.work+4)) ∧
      (∀h : Row H groups M,last (out+(row H groups M h).val)=
        ((DescentSIMDLookup.data (fun u g=>lookupField f profile branch slots depth trim width indexBits block i
          (combine f (data u g)) (idx u g)) h).val:Word w)) ∧
      (∀x,x<out ∨ out+H*chunks groups M≤ x → last x=m x) ∧ CheapCode (scan w out (H*chunks groups M) term) := by
  exact lookup_run (lookupField f profile branch slots depth trim width indexBits block i)
    (lookup_hole f profile branch slots depth trim width indexBits block i 0) tables
    (.lookup prior .row) (.lookup select .row) out m (fun h g=>combine f (data h g)) idx fit safe rom before picked

/-- The literal lookup pages are installed once for every *block and field*.
Every circuit node and operand reuses those pages across all physical hosts. -/
def allGates (i : Fin (f.blocks*4)) : Book.Gate :=
  let part : Fin f.blocks×Fin 4:=finProdFinEquiv.symm i
  gates f profile branch slots depth trim width indexBits part.1 part.2

theorem install {M w : ℕ} (base unit : ℕ) (m : Memory w)
    (bound : totalBits f+indexBits≤ unit)
    (room : base+(f.blocks*4)*(2*2^(unit*M))<2^w) :
    let gs:=allGates f profile branch slots depth trim width indexBits
    let saved:=Book.image gs unit M base m
    (Book.install gs unit M w base).Exec m saved (4+10*((f.blocks*4)*(2*2^(unit*M)))) ∧
      (∀(x : Fin f.blocks) (i : Fin 4),Static (Book.tables gs unit M base (finProdFinEquiv (x,i)))
        (lookupField f profile branch slots depth trim width indexBits x i) M saved) ∧
      (∀a,a<base ∨ base+(f.blocks*4)*(2*2^(unit*M))≤ a → saved a=m a) ∧
      CheapCode (Book.install gs unit M w base) := by
  intro gs saved
  obtain ⟨run,values,frame,cheap⟩:=Book.mount gs unit M base m (fun _=>bound) room
  refine ⟨run,?_,frame,@cheap⟩
  intro x i
  simpa only [gs,allGates,Equiv.symm_apply_apply,gates] using values (finProdFinEquiv (x,i))

/-- For a prior live raw edge the native report's first flag is equality of
the two first-stage locations. Its second flag records precisely a new equality
created by the hub merge. -/
theorem capture_values {first last : Bool} (n : Cell c) :
    datum true (cell first last n)=first ∧ datum false (cell first last n)=(!first && last) := by
  simp [datum]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Operand

end OAI

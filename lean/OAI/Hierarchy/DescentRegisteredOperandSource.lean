import OAI.Hierarchy.DescentDatedPointerDecode
import OAI.Hierarchy.DescentDatedPriorOperand
import OAI.Hierarchy.DescentRegisteredOperandFields

namespace OAI
/-! # Physical source fields and the original seven-column predecessor books -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentOperandStateBanks DescentPackedOperand
open DescentOrdinaryAtomFieldRAM.ScalarOperand
open scoped Classical Fin.CommRing
noncomputable section
variable {l:Layout}

/-- Physical rows and typed prior operands for an entire public job. This
contains just the predecessor's stored columns and the current route fields. -/
structure Source (l : DescentDatedPriorOperand.Layout) where
  books : Pages l.operands→Fin l.hosts→Fin l.groups→Cell ((l.size+2)*l.nodes)
  pointer : Fin l.hosts→Fin l.groups→DescentOperandStateBanks.Pointer
  side : Fin l.hosts→Fin l.groups→DescentPriorOperandColumns.Side l.size
  size : ∀h g f,(pointer h g).header f<2^(l.size+2)
  routed : Fin 3→Fin l.hosts→Fin l.groups→Cell (l.size+2)
  noCarry : ∀h g,11*(routed 1 h g).val+(routed 2 h g).val<2^(l.size+2)

namespace Source

def fragment (v : Source l) (h g) :=(v.side h g).withHeader (v.pointer h g) (v.size h g)
def compiled (v : Source l) (h g) := DescentOrdinaryLocalFragment.route (v.fragment h g) (v.routed 0 h g)
  (DescentPackedRawTicket.payload (v.routed 1) (v.routed 2) v.noCarry h g)
end Source

abbrev Books (l : Layout) := Fin l.blocks→Pages l.operands→Fin l.hosts→Fin l.groups→Cell ((l.size+2)*l.nodes)
def booksHeader (b : Books l) (j : Fin l.jobs) (h : Fin l.hosts) (g : Fin l.groups) (f : Fin 4) : Cell (l.size+2) :=
  let z:=l.index.symm j
  take z.2.1 (b z.1 (DescentPriorOperandColumns.pageOf z.2.2 f) h g)

def BookPointers (b : Books l) :=∀j h g,∃ p : Pointer,∀f,(booksHeader b j h g f).val=p.header f

def ofBooks (b : Books l) (typed : BookPointers b)
    (s : Fin l.jobs→Fin l.hosts→Fin l.groups→DescentPriorOperandColumns.Side l.size)
    (route : Fin l.jobs→Fin 3→Fin l.hosts→Fin l.groups→Cell (l.size+2))
    (room : ∀j h g,11*(route j 1 h g).val+(route j 2 h g).val<2^(l.size+2))
    (j : Fin l.jobs) : Source l where
  books:=b (l.index.symm j).1
  pointer:=fun h g=>decodeHeader (booksHeader b j h g)
  side:=s j
  size:=by
    intro h g f
    obtain ⟨p,read⟩:=typed j h g
    rw [decode_of_pointer read,← read f]
    exact (booksHeader b j h g f).isLt
  routed:=route j
  noCarry:=room j

theorem ofBooks_header (b : Books l) (typed : BookPointers b) (s route room j h g f) :
    (booksHeader b j h g f).val=((ofBooks b typed s route room j).pointer h g).header f:=by
  obtain ⟨p,read⟩:=typed j h g
  change _=(decodeHeader _).header _
  rw [decode_of_pointer read]
  exact read f

end
end Hierarchy.DescentDatedPriorOperand

end OAI

import OAI.Hierarchy.DescentDatedPointerTagFields
import OAI.Hierarchy.DescentRegisteredOperandSource

namespace OAI
/-! # Decoding the observed prior pointer while allowing unused reset columns -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks DescentPriorOperandColumns
open scoped Classical Fin.CommRing
noncomputable section
variable {k : ℕ}

/-- The source projection reads the actual, possibly noncanonical stored fields. -/
theorem readFragment_header (r : Fin 4→Cell (k+2)) (s : Side k) (ok : HeaderTag r) (f : Fin 4) :
    sourceFields (readFragment r s) (headerIndex f)=r f :=by
  rcases ok.values with h|h|h <;> fin_cases f <;> apply Fin.ext <;>
    simp [readFragment,sourceFields,headerIndex,Kind.parse,Kind.code,h]

theorem readFragment_side (r : Fin 4→Cell (k+2)) (s : Side k) (i : Fin 6) :
    sourceFields (readFragment r s) (sideIndex i)=
      sourceFields (s.withHeader (decodeHeader r) (decodedSize r)) (sideIndex i) :=by
  fin_cases i <;> rfl

variable {l : Layout}
def BookTags (b : Books l) := ∀j h g, HeaderTag (booksHeader b j h g)

theorem BookPointers.tags {b : Books l} (valid : BookPointers b) : BookTags b :=by
  intro j h g
  obtain ⟨p,issued⟩:=valid j h g
  unfold HeaderTag
  rw [issued 0]
  cases p <;> simp [Pointer.header]

def decodedBooks (b : Books l) (s : Fin l.jobs→Fin l.hosts→Fin l.groups→Side l.size)
    (route : Fin l.jobs→Fin 3→Fin l.hosts→Fin l.groups→Cell (l.size+2))
    (room : ∀j h g,11*(route j 1 h g).val+(route j 2 h g).val<2^(l.size+2))
    (j : Fin l.jobs) : Source l where
  books := b (l.index.symm j).1
  pointer := fun h g=>decodeHeader (booksHeader b j h g)
  side := s j
  size := fun h g=>decodedSize (booksHeader b j h g)
  routed := route j
  noCarry := room j

theorem decodedBooks_eq (b : Books l) (typed : BookPointers b) (s route room j) :
    decodedBooks b s route room j=ofBooks b typed s route room j := rfl

theorem decodedBooks_key (b : Books l) (typed : BookTags b) (s route room j h g) :
    resolve (DescentOrdinaryLocalFragment.route (readFragment (booksHeader b j h g) (s j h g))
      (route j 0 h g) (DescentPackedRawTicket.payload (route j 1) (route j 2) (room j) h g))=
      resolve ((decodedBooks b s route room j).compiled h g) :=
  readFragment_key _ _ (typed j h g) _ _

end
end Hierarchy.DescentDatedPriorOperand

end OAI

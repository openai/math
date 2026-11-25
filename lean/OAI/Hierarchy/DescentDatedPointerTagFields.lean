import OAI.Hierarchy.DescentDatedPointerDecode

namespace OAI
/-! # Decoding the observed prior pointer while allowing unused reset columns -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks DescentPriorOperandColumns
open scoped Classical Fin.CommRing
noncomputable section
variable {k : ℕ}

/-- The three numerical tags admitted by both the original pointer decoder and the packed resolver. -/
def HeaderTag (r : Fin 4→Cell (k+2)) : Prop := (r 0).val≤2

/-- Read the four original words, including every ignored field, into the native ten-column fragment. -/
def readFragment (r : Fin 4→Cell (k+2)) (s : Side k) : Fragment k :=
  ⟨Kind.parse (r 0).val,s.donor,r 1,r 2,r 3,s.firstCapture,s.secondCapture,s.marked,s.start,s.grain⟩

theorem HeaderTag.values {r : Fin 4→Cell (k+2)} (ok : HeaderTag r) :
    (r 0).val=0 ∨ (r 0).val=1 ∨ (r 0).val=2 :=by unfold HeaderTag at ok;omega

theorem decodedSize (r : Fin 4→Cell (k+2)) (f : Fin 4) : (decodeHeader r).header f<2^(k+2) :=by
  have four : 4≤2^(k+2):=Nat.pow_le_pow_right (by decide : 0<2) (show 2≤k+2 by omega)
  have a:=(r 1).isLt
  have b:=(r 2).isLt
  have c:=(r 3).isLt
  by_cases one : (r 0).val=1 <;> by_cases two : (r 0).val=2 <;>
    fin_cases f <;> simp [decodeHeader,one,two,Pointer.header]; omega

/-- The true routed key is invariant under the decoder discarding the private peer and chunk
or the exterior peer. All the earlier numerical columns of a cable are preserved by decoding. -/
theorem readFragment_key (r : Fin 4→Cell (k+2)) (s : Side k) (ok : HeaderTag r)
    (peer ticket : Cell (k+2)) :
    resolve (DescentOrdinaryLocalFragment.route (readFragment r s) peer ticket)=
      resolve (DescentOrdinaryLocalFragment.route (s.withHeader (decodeHeader r) (decodedSize r)) peer ticket) :=by
  have compare (p : Pointer) (width : ∀f,p.header f<2^(k+2)) (chosen : p=decodeHeader r) :
      resolve (DescentOrdinaryLocalFragment.route (readFragment r s) peer ticket)=
        resolve (DescentOrdinaryLocalFragment.route (s.withHeader p width) peer ticket) :=by
    rcases ok.values with h|h|h
    · have found : p=.privateWord (r 2).val:=chosen.trans (by simp [decodeHeader,h])
      clear chosen
      subst p
      simp [readFragment,Side.withHeader,Pointer.header,Kind.parse,DescentOrdinaryLocalFragment.route,resolve,h]
    · have found : p=.cable (r 1).val (r 2).val (r 3).val:=chosen.trans (by simp [decodeHeader,h])
      clear chosen
      subst p
      simp [readFragment,Side.withHeader,Pointer.header,Kind.parse,DescentOrdinaryLocalFragment.route,resolve,h]
    · have found : p=.pin (r 2).val (r 3).val:=chosen.trans (by simp [decodeHeader,h])
      clear chosen
      subst p
      simp [readFragment,Side.withHeader,Pointer.header,Kind.parse,DescentOrdinaryLocalFragment.route,resolve,h]
  exact compare _ (decodedSize r) rfl

end
end Hierarchy.DescentDatedPriorOperand

end OAI

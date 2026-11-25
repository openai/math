import OAI.Computability.MultitapeWeakETH.CyclicKeys
import OAI.Computability.NearSquareRoot.SynchronizedBitAddress
import OAI.Computability.VPVNP.LiveHeaderBits

/-! # Preparing signed wire endpoints and their address fields -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram

open Algorithms.SubexponentialSAT IntegerMultiplication IntegerMultiplication.Code FormulaRanks

private def left (x : Key) : Bool := decide ((x.headD []).length = 1)
private def tail (x : Key) : Key := List.casesOn x [] fun _ xs => xs

private theorem left_poly : Poly left :=
  (((Iter.leader ([] : Tally)).pair (Easy.const [()])).compose Iter.linked).poly

private theorem tail_poly : Poly tail := (Easy.listCase [] Easy.snd).poly

/-- A source is either its own slot or the slot of its literal. A target
is the next slot in its variable cycle or the containing clause. -/
def owner (q : Body × Key) : Key :=
  let w := tail q.2
  let payload := tail w
  bif left q.2 then
    [()] :: (bif left w then payload else asSlot payload)
  else bif left w then [()] :: advance (payload,q.1) else [(),()] :: tail payload

theorem owner_poly : Poly owner := by
  have w := (Easy.snd (X:=Body)).poly.compose tail_poly
  have p := w.compose tail_poly
  have tag (i : Tally) {f : Body × Key → Key} (h : Poly f) :
      Poly (fun q => i :: f q) := ((IntegerMultiplication.Code.Poly.const i).pair h).compose Easy.cons.poly
  exact Poly.choose (Easy.snd.poly.compose left_poly)
    (tag [()] (Poly.choose (w.compose left_poly) p (p.compose asSlot_poly)))
    (Poly.choose (w.compose left_poly) (tag [()] ((p.pair Easy.fst.poly).compose advance_poly))
      (tag [(),()] (p.compose tail_poly)))

theorem owner_eq {n} (F : SAT.CNF (Fin n)) (wd : SAT.WidthAtMost 3 F) (e : End F) :
    owner ((slots n (Encoding.cnfNumbers F)).map encodeKey,encodeKey (endKey F e)) =
      encodeKey (siteKey F (host F e)) := by
  rcases e with (s | l) | (s | l)
  · rfl
  · change [()] :: asSlot (encodeKey (occKey F l)) = [()] :: encodeKey (slotKey F (atOcc F l))
    rw [asSlot_encode,realSlot_occ]
  · exact congrArg ([()] :: ·) (advance_eq F wd s)
  · rfl

/-- Binary fields are little endian and padded to the declared width. -/
def field (p : Tally × Tally) : List Bool :=
  Bits.resize (p.1,Carry.born p.2.length)

theorem field_poly : Poly field :=
  (Bits.easy_resize (Easy.fst.pair (Easy.snd.compose Carry.easy_chart))).poly

theorem field_eq (w : ℕ) (i : Fin (2^w)) :
    field (tally w,tally i.val) = List.ofFn (VPVNP.RAMSerialization.wordBits w i) := by
  change Bits.sized w (Carry.born _) = _
  rw [tally_length]
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hv : Bits.value (Bits.sized w (Carry.born i.val)) = i.val := by
      rw [Bits.sized_low,Carry.birthValue,Nat.mod_eq_of_lt i.isLt]
    rw [← NearSquareRoot.BoxFin.value_bit _ j hj,hv,List.getElem_ofFn]
    exact VPVNP.LiveHeader.testBit_wordBits i ⟨j, by simpa using hj⟩

def swapEnd (e : Key) : Key := (bif left e then [(),()] else [()]) :: tail e

theorem swap_poly : Poly swapEnd :=
  ((Poly.choose left_poly (IntegerMultiplication.Code.Poly.const [(),()]) (IntegerMultiplication.Code.Poly.const [()])).pair tail_poly).compose Easy.cons.poly

theorem swap_encode {n} (F : SAT.CNF (Fin n)) (e : End F) :
    swapEnd (encodeKey (endKey F e)) = encodeKey (endKey F e.swap) := by
  cases e <;> rfl

end OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram

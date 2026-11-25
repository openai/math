import OAI.Hierarchy.DescentEarlyRotationReel
import OAI.Hierarchy.DescentEarlyMatrixBudget
import OAI.Hierarchy.DescentDatedEventualAddress

namespace OAI
/-! # The early matrix reel starts above both the dated registers and the old compact sheet -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentExteriorMatrixUpdate DescentExteriorShelf Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B : ℕ)

def replayBase (last compact width : ℕ) :=max last (compact+32*width)

theorem early_bound (S : AtomSchedule) (k tail last compact j r s e head : ℕ)
    (paid : compact+17*span j r s e≤head) :
    Calendar.earlyEnd S k tail (replayBase last compact (span j r s e)) j r s e ≤
      last+4*head+S.length*Calendar.stride S k tail+S.length+1 :=by
  let block:=span j r s e
  have rows : e≤block := (Nat.le_mul_of_pos_right e (Nat.two_pow_pos _)).trans (row_room j r s e)
  have enclosed : compact+17*block≤head:=paid
  have report : max (17*block) (block+e)≤17*block:=by apply max_le le_rfl; omega
  have origin : max last (compact+32*block)≤last+2*head:=by apply max_le <;> omega
  change max last (compact+32*block)+S.length*Calendar.stride S k tail+S.length+1+
    max (17*block) (block+e)≤_
  omega

theorem early_bound_after_roles (S:AtomSchedule) (k tail last compact j r s e head roles:ℕ)
    (paid:compact+17*span j r s e≤head) :
    Calendar.earlyEnd S k tail (replayBase last compact (span j r s e)+roles) j r s e≤
      last+4*head+S.length*Calendar.stride S k tail+S.length+1+roles :=by
  have fixed:=early_bound S k tail last compact j r s e head paid
  simp only [Calendar.earlyEnd,Calendar.earlyAt,Calendar.stop,Calendar.tableAt] at fixed ⊢
  omega

theorem early_room_at {ι : ℕ→Type*} (sites last compact j r s e head : ∀h,ι h→ℕ)
    (openWord : 20≤B) (lastBound : Bounded last) (seedBound : Bounded head)
    (paid : ∀h i,compact h i+17*span (j h i) (r h i) (s h i) (e h i)≤head h i) :
    Bounded (fun h i=>let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset (sites h i) (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      Calendar.earlyEnd S k (tail τ J) (replayBase (last h i) (compact h i) (span (j h i) (r h i) (s h i) (e h i)))
        (j h i) (r h i) (s h i) (e h i)) :=by
  let half : Bounded (fun h (_:ι h)=>2^(h/2)):=Bounded.pow_of_linear (K:=1)
    (Eventually.of_forall fun h i=>by simpa only [one_mul] using Nat.div_le_self h 2)
  have bill:=(((lastBound.add ((Bounded.const 4).mul seedBound)).add half).add half).add (Bounded.const 1)
  apply bill.of_eventually_le
  filter_upwards [early_matrix_words G t f g reset τ B openWord] with h issued
  intro i
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset (sites h i) (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  obtain ⟨matrices,rows,_⟩:=issued (sites h i)
  have matrixBound : S.length*Calendar.stride S k (tail τ J)≤2^(h/2):=matrices
  have lengthBound : S.length ≤ 2^(h/2) := rows
  exact (early_bound S k (tail τ J) (last h i) (compact h i) (j h i) (r h i) (s h i) (e h i) (head h i)
    (paid h i)).trans (by change _≤last h i+4*head h i+2^(h/2)+2^(h/2)+1;omega)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

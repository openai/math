import OAI.Hierarchy.DescentSeedPublicFront
import OAI.Hierarchy.DescentWideSeedOriginalInvoice
import OAI.Hierarchy.DescentExteriorPublicPins
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # The original seed header, dated profile rows, and seventeen exterior columns -/
namespace Hierarchy.DescentWideSeedFlags
open DescentInitialHost DescentSeedRoot DescentPackedEpochShelves DescentTerminalEpochChart DescentPackedProfileInstall
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentTerminalEpochDecoder DescentExterior
open DescentDatedAddressBook Catalyst Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp nP : ℕ}
/-- The public start has polynomial size in the purchased word count, including
every original exterior row and the padded selector directory. -/
theorem public_front_words (X : Approximation F cp nP) {A : Type} (R s h C : ℕ) (steps : List (Source A))
    (j rest a : ℕ) (large : 10≤h) (budget : h≤a) (source : X.size+1≤2^a) (copies : R≤2^a)
    (dates : steps.length≤2^a) (seats : seatBill steps≤2^a)
    (width : 2*digitsNeeded s≤h) (profile : 2*unit C≤h/2)
    (lookup : DescentExteriorShelf.tableBits j rest s≤h/2) (split : R=2^(j+(j+rest))) :
    publicFront X R s h C steps j rest≤2^(12+3*a):=by
  let z:=2^a
  have pos : 0<z:=Nat.two_pow_pos _
  have word : h≤z:=budget.trans Nat.lt_two_pow_self.le
  have dict : 2^(h/2)≤z:=Nat.pow_le_pow_right (by decide) ((Nat.div_le_self ..).trans budget)
  have small : unit C≤z:=(show unit C≤h by omega).trans word
  have digit : digitsNeeded s≤z:=(show digitsNeeded s≤h by omega).trans word
  have num : 2^(j+rest)≤R:=by rw [split];exact Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)
  have ext : ExteriorCount X≤X.size:=Nat.le_add_left ..
  have rows : DescentExteriorShelf.rows j rest (ExteriorCount X)≤z*z:=
    Nat.mul_le_mul ((ext.trans (Nat.le_succ _)).trans source) (num.trans copies)
  have native_:=initial_bits X R s h C steps j rest (ExteriorCount X) large width profile lookup
  have joined : 3*((6+90*(X.size+1))*h+320*(X.size+1)*R*digitsNeeded s)+
      30*steps.length*h+48*seatBill steps*unit C+34*DescentExteriorShelf.rows j rest (ExteriorCount X)*h+
      45*2^(h/2)*h ≤ 3*((6+90*z)*z+320*z*z*z)+30*z*z+48*z*z+34*(z*z)*z+45*z*z :=by
    gcongr
  have scale1 : z≤z*z:=Nat.le_mul_of_pos_right _ pos
  have scale2 : z*z≤z*z*z:=Nat.le_mul_of_pos_right _ pos
  have price : 3*((6+90*z)*z+320*z*z*z)+30*z*z+48*z*z+34*(z*z)*z+45*z*z≤2^12*z^3 :=by
    norm_num
    nlinarith only [scale1,scale2,Nat.zero_le (z*z*z)]
  rw [Nat.pow_add,Nat.mul_comm 3 a,Nat.pow_mul]
  exact (Nat.le_mul_of_pos_right _ (by omega : 0<h)).trans (native_.trans (joined.trans price))

end
end Hierarchy.DescentWideSeedFlags

end OAI

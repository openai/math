import OAI.Hierarchy.DescentOperandPathPriceNumbers
import OAI.Hierarchy.DescentDatedLocalRankPages
import OAI.Hierarchy.DescentDatedSourcePathMount
import OAI.Hierarchy.DescentPackedChunkWork
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # The actual per-host path and local-rank headers shared by every operand query -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentSixParty.Chronology DescentSharedLeafLookup DescentSIMDLookup DescentHaloWalkRAM
open DescentStaticWordColumn DescentSharedCableNames
noncomputable section

theorem all_word_bill (B : Banks) (base H G M D w h u ratio : ℕ)
    (cap : M≤ h) (fill : h≤ M*u) (bus : w≤ ratio*h) :
    (allPages B base H G M D w).wordInvoice≤ pathCharge H G D h u ratio :=by
  let P:=breadth D
  let n:=P*(D+1)
  let F:=(P+1)*(30+4*P+4*(P*P))
  let j:=hostJob B H D
  let p:=allPages B base H G M D w
  let z:=stop base H G M D-hostEnd base H D
  have bounds:=all_cost B base H G M D w
  have lookup : names p.program≤15+n*(11+4*F)+15*(z+1):=bounds.2
  have delay : p.ticks≤4+n*(4+H*(2*F+4))+(4+10*z):=bounds.1
  have table : 2^(Packed.bits P)≤2*(P+1)+1:=DescentDyadicSpan.span_le (P+1)
  have first:=DescentDyadicSpan.span_le (H*chunks G M)
  have second:=DescentDyadicSpan.span_le ((M+1)*2^(Packed.bits P))
  have count : (M+1)*2^(Packed.bits P)≤(h+1)*(2*(P+1)+1):=Nat.mul_le_mul (by omega) table
  have pages : z≤4*(H*chunks G M)+3+2*((h+1)*(2*(P+1)+1)):=by
    dsimp only [z,stop,Public.stop,Public.stride,Public.words,P]
    dsimp only [DescentDyadicSpan.span,P] at first second count
    omega
  have rectangle:=DescentDatedSeedStartup.chunk_work H G M h u fill
  have room : z*h≤4*(H*h+H*G*u)+(3+2*(h+1)*(2*(P+1)+1))*h:=by
    calc z*h≤(4*(H*chunks G M)+3+2*((h+1)*(2*(P+1)+1)))*h:=Nat.mul_le_mul_right _ pages
         _=4*((H*chunks G M)*h)+(3+2*(h+1)*(2*(P+1)+1))*h:=by ring
         _≤_:=by gcongr
  have namesAndClock:=Nat.add_le_add delay (Nat.mul_le_mul_left 7 lookup)
  calc
    _≤((4+n*(4+H*(2*F+4))+(4+10*z))+7*(15+n*(11+4*F)+15*(z+1)))*(ratio*h):=Nat.mul_le_mul namesAndClock bus
    _=hostCost H D h ratio+ratio*(109*h+115*(z*h)):=by unfold hostCost columnCost rankWork;dsimp [n,P,F];ring
    _≤_:=Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ room) _)) _

theorem local_word_bill (B : Local.Directory) (base H D w h ratio : ℕ) (bus : w≤ ratio*h) :
    ((Local.job B H D).atBase base w).wordInvoice≤ rankCost H D h ratio :=by
  have bounds:=Local.cost B base H D w
  have both:=Nat.add_le_add bounds.1 (Nat.mul_le_mul_left 7 bounds.2)
  apply (Nat.mul_le_mul both bus).trans_eq
  unfold rankCost columnCost
  change ((4+_*(4+H*(2*(rankWork D)+4)))+7*(15+_*(11+4*(rankWork D))))*(ratio*h)=_
  ring

end
end Hierarchy.DescentDatedSourcePathDirectory

end OAI

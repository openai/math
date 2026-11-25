import OAI.Hierarchy.DescentIncomingChunkWork
import OAI.Hierarchy.DescentSeedPitchFill
import OAI.Hierarchy.DescentDatedSeedWordVolume

namespace OAI
/-! # Bit cost at the two genuine first-stage rectangle margins -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup
/-- The first term is shared per host; the second is a short price on
every original copy. The incomplete final chunk in each bank is included. -/
theorem seed_bit_rectangle (base O V H G M T d N check word s₁ s₂ s₃ ticks : ℕ)
    (old : O≤H) (vertices : V≤H) (hosts : 0<H) (sm : 0<chunks G M) (tm : 0<chunks G T)
    (signedFill : G≤M ∨ word≤M*s₁) (operandFill : word≤T*s₂) (checkFill : word≤check*s₃)
    (bill : ticks≤3500*(seededFloor base V H G M T d N-base+1)+66*(O*chunks ((G*2^d)*8) check)) :
    ticks*word ≤
      H*word*(14000066+224000*(N+1)*2^d)+
      H*(G*2^d)*(14000000*s₁+224000*(N+1)*s₂+528*s₃) :=by
  let r:=2^d
  have shape:=seed_extent_work base V H G M T d N vertices hosts sm tm
  have sign:=chunk_work_or H G M word s₁ signedFill
  have ops:=chunk_work H G T word s₂ operandFill
  have ballot:=chunk_work O ((G*2^d)*8) check word s₃ checkFill
  have height : H*G≤H*(G*r) :=by
    have hr : G≤G*r := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    exact Nat.mul_le_mul_left _ hr
  have shared:=Nat.mul_le_mul_right word old
  have source:=Nat.mul_le_mul_right (((G*r)*8)*s₃) old
  have inv : ticks≤3500*(4000*(H*chunks G M)+(64*(N+1)*r)*(H*chunks G T))+
      66*(O*chunks ((G*r)*8) check) :=bill.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ shape) _)
  calc
    ticks*word ≤ _ := Nat.mul_le_mul_right word inv
    _ = 14000000*((H*chunks G M)*word)+(224000*(N+1)*r)*((H*chunks G T)*word)+
        66*((O*chunks ((G*r)*8) check)*word) :=by ring
    _ ≤ 14000000*(H*word+H*G*s₁)+(224000*(N+1)*r)*(H*word+H*G*s₂)+
        66*(O*word+O*((G*r)*8)*s₃) :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ sign) (Nat.mul_le_mul_left _ ops))
        (Nat.mul_le_mul_left _ ballot)
    _ ≤ 14000000*(H*word+H*(G*r)*s₁)+(224000*(N+1)*r)*(H*word+H*G*s₂)+
        66*(H*word+H*((G*r)*8)*s₃) :=by
      apply Nat.add_le_add
      · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ height) _)) _
      · exact Nat.mul_le_mul_left _ (Nat.add_le_add shared (by simpa only [Nat.mul_assoc] using source))
    _ = _ :=by dsimp [r];ring

end Hierarchy.DescentDatedSeedStartup

end OAI

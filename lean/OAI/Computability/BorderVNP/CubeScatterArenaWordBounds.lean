import OAI.Computability.BorderVNP.CubeISAOwnedRowAllocation

/-! # Word bounds for the row scan from the two allocated data bank sizes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowSources

open RoutingISA RoutingISA.OwnedStages Physical.Owned Tally

/-- Fitting the ends of the allocated packet and singleton banks also fits
the intermediate public key, digit and trial counters. The independent finite
cube selector/vertex alphabet and the power directory are bounded separately. -/
theorem bankRooms (row : OwnedRowSetup.Layout) (w n b h K s frame singleBase endAddr : ℕ)
    (alphabet : 0 < row.d) (bits : 0 < row.blocks*row.bc) (width : 0 < bankWidth n b h K s)
    (frameEnd : frame+112 ≤ row.bank) (headEnd : row.header+13 ≤ row.bank)
    (powerEnd : row.power+n+1 ≤ endAddr)
    (packetEnd : row.bank+(row.d*row.d)^(n+1)*2*row.blocks*bankWidth n b h K s ≤ singleBase)
    (singleEnd : singleBase+row.d^(n+1)*row.d^(n+1)*(row.blocks*row.bc) ≤ endAddr)
    (endFit : endAddr < 2^w) (finiteCube : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w) :
    PacketRoom row w n b h K s frame ∧ SingleRoom w n row.d (row.blocks*row.bc) frame singleBase := by
  let Z := row.d^(n+1)
  have Zpos : 0 < Z := pow_pos alphabet _
  have blockPos : 0 < row.blocks := Nat.pos_of_mul_pos_right bits
  have grow : row.d^n ≤ Z := by
    dsimp only [Z]; rw [pow_succ]; exact Nat.le_mul_of_pos_right _ alphabet
  have digit : row.d ≤ Z := by
    dsimp only [Z]; rw [pow_succ]; exact Nat.le_mul_of_pos_left _ (pow_pos alphabet _)
  have key : Z*Z ≤ Z*Z*(row.blocks*row.bc) := Nat.le_mul_of_pos_right _ bits
  have len : row.blocks*row.bc ≤ Z*Z*(row.blocks*row.bc) := Nat.le_mul_of_pos_left _ (Nat.mul_pos Zpos Zpos)
  have keyFit : Z*Z < 2^w := key.trans_lt ((Nat.le_add_left _ singleBase).trans_lt (singleEnd.trans_lt endFit))
  have squares : row.d*row.d < 2^w := (Nat.mul_le_mul digit digit).trans_lt keyFit
  have endpoints : row.d^n*row.d^n < 2^w := (Nat.mul_le_mul grow grow).trans_lt keyFit
  have squarePos : 0 < row.d*row.d := Nat.mul_pos alphabet alphabet
  have packetCount : (row.d*row.d)^n*2*row.blocks ≤ (row.d*row.d)^(n+1)*2*row.blocks :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ squarePos))
  have cap := (Nat.le_add_left _ row.bank).trans packetEnd
  have trialBound := (packetCount.trans (Nat.le_mul_of_pos_right _ width)).trans cap
  have widthBound := (Nat.le_mul_of_pos_left (bankWidth n b h K s)
    (Nat.mul_pos (Nat.mul_pos (pow_pos squarePos _) (by decide)) blockPos)).trans cap
  have singleFit := singleEnd.trans_lt endFit
  have baseFit : singleBase < 2^w := (Nat.le_add_right _ _).trans_lt singleFit
  have bankFit : row.bank < 2^w := ((Nat.le_add_right _ _).trans packetEnd).trans_lt baseFit
  refine ⟨⟨⟨by omega,by omega,by omega,squares,endpoints,?_⟩,trialBound.trans_lt baseFit,finiteCube,
    widthBound.trans_lt baseFit,width,packetEnd.trans baseFit.le⟩,⟨by omega,keyFit.le,singleFit⟩⟩
  exact len.trans_lt ((Nat.le_add_left _ singleBase).trans_lt singleFit)

end Cube.TeamRowSources

end BorderVNP
end Computability
end OAI

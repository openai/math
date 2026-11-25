import OAI.Computability.BorderVNP.CubeISALocalRowSpace
import OAI.Computability.BorderVNP.CubeISAHeaderInstallBoot

/-! # Native row workspace and arithmetic bounds from the actual geometric arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open BorderVNP.Cube BorderVNP.Cube.Physical.Owned BorderVNP.Cube.Tally CubeHeaderInstall

/-- Row setup fields after the secondary header installation and power-table boot. -/
def rowLayout (stat : Inputs) (b h power : ℕ) : OwnedRowSetup.Layout :=
  ⟨stat.d,stat.blocks,h*b,power,stat.header,stat.packetBase⟩

/-- All fixed scalar template words that must fit regardless of the length-dependent geometry. -/
def templateLimit (n b h K s : ℕ) : ℕ :=
  max (max (n+1) s) (max (bankWidth n b h K s) (max (Fintype.card (Selector n K h)) (Fintype.card (Edge (n+1)))))

private theorem payload_room (n b h K s : ℕ) : h*b ≤ bankWidth n b h K s ∧ h*s ≤ bankWidth n b h K s := by
  have ep : 0 < Fintype.card (Ends n) := Fintype.card_pos
  have eg : 0 < Fintype.card (Edge (n+1)) := Fintype.card_pos
  have eb := Nat.mul_le_mul_right (h*b) ep
  have es := Nat.mul_le_mul_right (h*s) eg
  change 1*(h*b) ≤ _ at eb
  change 1*(h*s) ≤ _ at es
  rw [one_mul] at eb es
  unfold bankWidth supplyBase
  omega

/-- The complete concrete bank reservation and its scratch sentinel dominate
the variable machine counters, the full label count, and the padded selector
tally. The only additional numeric bound concerns the fixed cube template. -/
theorem space_of_bankStop (stat : Inputs) (w n b h K s power frame : ℕ)
    (axes : stat.a = n+1) (alphabet : 0 < stat.d) (blocks : 0 < stat.blocks)
    (primary : frame+63 < stat.header) (powerEnd : power+n < 2^w)
    (endRoom : bankStop stat n (bankWidth n b h K s)+8+h < 2^w)
    (fixedFit : templateLimit n b h K s < 2^w) (positive : 0 < bankWidth n b h K s) :
    let l := rowLayout stat b h power
    Space l w n b h K s frame (stat.header+13) (stat.header+13+stat.entries) ∧
    stat.d^(n+1) < 2^w ∧ packetTrials n stat.d stat.blocks*(h*s) < 2^w := by
  intro l
  let stride := bankWidth n b h K s
  let radix := stat.d*stat.d
  let cells := radix^(n+1)
  let volume := cells*2*stat.blocks*stride
  have hp : 0 < radix := Nat.mul_pos alphabet alphabet
  have hp' : 0 < cells := pow_pos hp _
  have dims : n+1 < 2^w ∧ s < 2^w ∧ stride < 2^w ∧
      Fintype.card (Selector n K h) < 2^w ∧ Fintype.card (Edge (n+1)) < 2^w := by
    unfold templateLimit at fixedFit
    dsimp only [stride]
    omega
  have arena : stat.packetBase+volume+8+h < 2^w := endRoom
  have volumeFit : volume < 2^w := by omega
  have cellsBound : cells ≤ volume := by
    change cells ≤ cells*2*stat.blocks*stride
    calc cells ≤ cells*2 := by omega
         _ ≤ cells*2*stat.blocks := Nat.le_mul_of_pos_right _ blocks
         _ ≤ cells*2*stat.blocks*stride := Nat.le_mul_of_pos_right _ positive
  have radices : radix^n ≤ cells := Nat.pow_le_pow_right hp (Nat.le_succ _)
  have raw : packetTrials n stat.d stat.blocks ≤ cells*2*stat.blocks :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ radices)
  have allPackets : cells*2*stat.blocks ≤ volume := Nat.le_mul_of_pos_right _ positive
  have bCount : stat.blocks ≤ cells*2*stat.blocks := by
    have u : 1 ≤ cells*2 := by omega
    simpa only [one_mul] using Nat.mul_le_mul_right stat.blocks u
  have fitsB := (Nat.mul_le_mul bCount (payload_room n b h K s).1).trans_lt volumeFit
  have fitsS := (Nat.mul_le_mul raw (payload_room n b h K s).2).trans_lt volumeFit
  have square : radix ≤ cells := by simpa only [pow_one] using Nat.pow_le_pow_right hp (by omega : 1 ≤ n+1)
  have tail : stat.d^n*stat.d^n < 2^w := by
    rw [← mul_pow]
    exact radices.trans_lt (cellsBound.trans_lt volumeFit)
  have hd : stat.d ≤ radix := Nat.le_mul_of_pos_right _ alphabet
  have label : stat.d^(n+1) < 2^w :=
    (Nat.pow_le_pow_left hd (n+1)).trans_lt (cellsBound.trans_lt volumeFit)
  have countA : n+1 ≤ stat.entries := by
    have hh : 1*(n+1) ≤ radix*(n+1) := Nat.mul_le_mul_right (n+1) hp
    simpa only [Inputs.entries,axes,one_mul,radix] using hh
  have afterHead : stat.header+13 ≤ stat.packetBase := by unfold Inputs.packetBase; omega
  have low : stat.header+8 < 2^w := by omega
  have fits : l.Fits w n frame := ⟨by omega,low,powerEnd,square.trans_lt (cellsBound.trans_lt volumeFit),tail,fitsB⟩
  refine ⟨⟨fits,primary,by dsimp only [l,rowLayout]; omega,by omega,?_,?_,
    raw.trans_lt (allPackets.trans_lt volumeFit),(selector_room n b h K s).trans_lt dims.2.2.1,
    dims.2.2.2.1,dims.2.2.1,positive,dims.2.2.2.2,dims.1,dims.2.1⟩,label,fitsS⟩
  · change stat.header+13+stat.entries+stat.d*stat.d*(n+1) ≤ stat.packetBase
    have eq : stat.d*stat.d*(n+1) = stat.entries := by simp only [Inputs.entries,axes]
    rw [eq]
    unfold Inputs.packetBase
    omega
  · rw [head_eq]
    exact endRoom

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI

import OAI.Hierarchy.DescentPackedCensusPhaseWidth
import OAI.Hierarchy.DescentPackedMatchPolynomial
import OAI.Hierarchy.DescentPackedMatchFee
import OAI.Hierarchy.DescentPackedSixBirths
import OAI.Hierarchy.DescentSignedCableCodec

namespace OAI
/-! # A single physical lane width for the census, matching and six births -/

namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentPackedColony DescentSIMDLookup
noncomputable section

/-- All parameters are public. The census quota can differ from the ordinary
matching cap, and its literal value fits in this scale. -/
def ordinaryScale (k D cap choiceBits censusBits quota profile panelBits : ℕ) :=
  1+2^k+D+2*cap+choiceBits+censusBits+quota+profile+panelBits

def ordinaryUnit (scale : ℕ) := 600*scale^9

theorem ordinary_width (k D cap choiceBits censusBits quota profile panelBits : ℕ) :
    let r:=(2:ℕ)^k
    let s:=shape r D (2*cap) profile
    let unit:=ordinaryUnit (ordinaryScale k D cap choiceBits censusBits quota profile panelBits)
    0<unit ∧ Phase.recordWidth k censusBits quota≤unit ∧ r+choiceBits≤unit ∧
      DescentSignedCableCodec.width D cap≤unit ∧ Gather.matchUnit s panelBits r D (2*cap)≤unit ∧
      SixBirths.unit s≤unit := by
  let r:=(2:ℕ)^k
  let level:=ordinaryScale k D cap choiceBits censusBits quota profile panelBits
  let s:=shape r D (2*cap) profile
  have layout : level=1+r+D+2*cap+choiceBits+censusBits+quota+profile+panelBits := rfl
  have positive : 1≤level := by
    rw [layout]
    simp only [Nat.add_assoc]
    exact Nat.le_add_right 1 _
  have blocks : r≤level := by omega
  have depth : k≤r := Nat.lt_two_pow_self.le
  have degree : D≤level := by omega
  have ports : 2*cap≤level := by omega
  have pw : profile≤level := by omega
  have small : panelBits≤level := by omega
  have scale9 (n : ℕ) (hn : n≤9) : level^n≤level^9 := Nat.pow_le_pow_right positive hn
  have first : level≤level^9 := by simpa using scale9 1 (by decide)
  have second:=scale9 2 (by decide)
  have third:=scale9 3 (by decide)
  have budget:=local_budget positive blocks degree ports pw
  have chooser := Phase.recordWidth_polynomial k censusBits quota
  have hA : 1+k+censusBits+quota≤level := by omega
  have hB : r+1≤2*level := by omega
  have fact:=Nat.mul_le_mul hA hB
  have choices : Phase.recordWidth k censusBits quota≤10*level^2 := by
    change Phase.recordWidth k censusBits quota≤5*(1+k+censusBits+quota)*(r+1) at chooser
    nlinarith only [chooser,fact]
  have wire (x : ℕ) : DescentSharedCableNames.Packed.bits x≤x :=
    Nat.clog_le_of_le_pow (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  have signed : DescentSignedCableCodec.width D cap≤6*level := by
    unfold DescentSignedCableCodec.width
    have d:=wire D
    have c:=wire cap
    omega
  have rp : r*(2*cap)≤level^2 := by simpa only [pow_two] using Nat.mul_le_mul blocks ports
  have dr : D*r≤level^2 := by simpa only [pow_two] using Nat.mul_le_mul degree blocks
  have linear : level≤level^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  have nFields : fields r D (2*cap)≤3*level^2 := by
    change r+(r*(2*cap)+D*r)≤_
    omega
  have panel:=Nat.mul_le_mul small nFields
  have size : Gather.matchUnit s panelBits r D (2*cap)≤ordinaryUnit level := by
    apply max_le
    · unfold ordinaryUnit
      nlinarith only [panel,small,first,third]
    · exact budget.2.2.1.trans (by dsimp only [ordinaryUnit];omega)
  have sd : 0<s.digit := by
    change 0 < max profile (Nat.clog 2 (2+entryCount r D (2*cap)+binCount r D+(D+1)*r+r*(2*cap)))
    exact (Nat.clog_pos (by decide) (by omega)).trans_le (le_max_right ..)
  have output : s.outputBits≤ProfileTable.envelope s :=
    (le_max_right s.inputBits s.outputBits).trans (Nat.le_add_right ..)
  have birth:=SixBirths.unit_bound s sd
  change 0<ordinaryUnit level ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨by dsimp [ordinaryUnit];positivity,?_,?_,?_,size,?_⟩
  · change Phase.recordWidth k censusBits quota≤600*level^9
    omega
  · change r+choiceBits≤600*level^9
    omega
  · change DescentSignedCableCodec.width D cap≤600*level^9
    omega
  · change SixBirths.unit s≤600*level^9
    have lim : ProfileTable.envelope s≤279*level^9:=budget.2.2.1
    omega

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI

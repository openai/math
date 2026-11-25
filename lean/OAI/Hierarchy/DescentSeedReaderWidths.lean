import OAI.Hierarchy.DescentSeedChosenLayoutCore
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! # Word room for the first actual signed and operand readers -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentSIMDLookup DescentPackedWalsh
variable {F : Type} [Field F]

private theorem cap_le_amount (r degree cap short names units prof : ℕ) (rows : 0 < r) :
    cap ≤ AgeBound.laneAmount r degree cap short names units prof :=by
  unfold AgeBound.laneAmount
  apply (le_trans · (le_max_left _ _))
  apply (le_trans · (le_max_right _ _))
  apply (Nat.le_mul_of_pos_right _ ?_).trans' (Nat.le_mul_of_pos_left _ rows)
  exact (by omega : 1 ≤ (2+units)*11).trans (le_max_right _ _)

theorem venue_room (D : PoweredGadget F) (S : AtomSchedule) (h gain k tail p f quota : ℕ)
    (tailPos : 0 < tail) (height : 32 ≤ h) :
    DescentSignedCableCodec.width 3 256*venuePitch D S h gain k tail p f quota ≤ h :=by
  have fixed : DescentSignedCableCodec.width 3 256 ≤ 32 :=by decide
  by_cases first : S.rounds=0
  · let m:=S.groupWidth k tail 0+k
    let b:=firstPrecision S k tail p f quota
    have gm : 1 ≤ m :=by dsimp only [m,AtomSchedule.groupWidth];omega
    have narrow : 32 ≤ 8*b :=by
      dsimp only [b,firstPrecision,AtomSchedule.localWalshBits,DescentWalshPrecision.bits]
      change 32 ≤ 8*(3*m+2*_+_+1)
      omega
    change _*(if S.rounds=0 then 2^(laneBits m h b-k) else _) ≤ h
    rw [ite_eq_left first]
    by_cases small : h/(8*b)=0
    · simpa [laneBits,small] using fixed.trans height
    · have lanes : 2^(laneBits m h b-k) ≤ h/(8*b) :=
        (Nat.pow_le_pow_right (by decide) ((Nat.sub_le _ _).trans (Nat.min_le_right ..))).trans
          (Nat.pow_log_le_self 2 small)
      have bpos : 0 < 8*b:=by omega
      calc
        _ ≤ (8*b)*2^(laneBits m h b-k) :=Nat.mul_le_mul_right _ (fixed.trans narrow)
        _ ≤ h:=by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le bpos).mp lanes
  · rw [venuePitch,ite_eq_right first]
    let degree:=originalDegree D S gain
    change _*lanes h (donorAmount k degree 256 D.b D.C D.k) ≤ h
    have full : 256 ≤ donorAmount k degree 256 D.b D.C D.k := cap_le_amount _ _ _ _ _ _ _ (Nat.two_pow_pos _)
    apply ((Nat.mul_le_mul_right _ (fixed.trans ((by decide : 32 ≤ 256).trans full))).trans ?_).trans (Nat.div_le_self h 2)
    simpa only [Nat.mul_comm] using lanes_fit h (donorAmount k degree 256 D.b D.C D.k)

theorem chosen_operand_half (D : PoweredGadget F) (S : AtomSchedule)
    (h k tail g p drift degree f quota base field wire hist : ℕ) :
    let l:=selectedLayout D S h k tail g p drift degree f quota base field wire hist
    l.operandBits*l.operandLanes ≤ h/2 :=by
  intro l
  let bits:=DescentOperandWidth.recordBits D S k tail drift degree p
  have packed : (2*bits)*lanes h (2*bits) ≤ h/2:=by simpa only [Nat.mul_comm] using lanes_fit h (2*bits)
  exact (Nat.mul_le_mul_right _ (by omega : bits ≤ 2*bits)).trans packed

theorem chosen_reader_room (D : PoweredGadget F) (S : AtomSchedule)
    (h k tail g p drift degree f quota base field wire hist : ℕ) (tailPos : 0 < tail) (height : 32 ≤ h) :
    let l:=selectedLayout D S h k tail g p drift degree f quota base field wire hist
    DescentSignedCableCodec.width 3 256*l.packedLanes ≤ h ∧ l.operandBits*l.operandLanes ≤ h :=by
  intro l
  exact ⟨venue_room D S h g k tail p f quota tailPos height,
    (chosen_operand_half D S h k tail g p drift degree f quota base field wire hist).trans (Nat.div_le_self h 2)⟩

end Hierarchy.DescentDatedSeedStartup

end OAI

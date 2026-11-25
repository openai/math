import OAI.Hierarchy.DescentSeedChosenLayout
import OAI.Hierarchy.DescentSeedGuardRoom
import OAI.Hierarchy.DescentNativeSocketScale
import OAI.Hierarchy.DescentOpenSplitStageCount

namespace OAI
/-! # The incoming ordinary and reset readers retain the density of the actual two original pitches -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentPrimitivePalette DescentSIMDLookup Filter
variable {F : Type} [Field F] (D : PoweredGadget F) (op : RotorSpec)

private theorem widen (J e n m : ℕ) (bound : n ≤ scale J e) (occupied : m ≤ 16*n) : m ≤ scale J (e+4) :=by
  have c : 16 ≤ scale J 4:=by
    change 2^4 ≤ 2^(4*(J+1))
    apply Nat.pow_le_pow_right (by decide)
    omega
  calc
    m ≤ 16*n:=occupied
    _ ≤ scale J 4*scale J e:=Nat.mul_le_mul c bound
    _ = scale J (e+4):=(scale_mul J 4 e).trans (congrArg (scale J) (Nat.add_comm 4 e))

theorem previous_pitches (t f g reset drift degreeMax quota : ℕ) :
    ∃C : ℕ,∃B₀ : ℕ → ℕ,∀τ B,0 < τ → B₀ τ ≤ B →
      ∀ᶠh : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
        ∀M degree base field wire hist : ℕ,let S:=stageNumbers D t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let q₀:=2^Nat.clog 2 (NativeBranch.localLimit D S)
        let split:=NativeBranch.binLimit (k:=k) S
        let q:=q₀*(D.b^(t*J)*D.b)
        let p:=split*(h/(16*(q*split)))
        let Z:=S.grainAt D.b p 0
        let l:=selectedLayout D S h k (tail τ J) g p drift degree f quota base field wire hist
        let m:=Primitive.paletteLanes D op l.seedWidth Z h k
        degree ≤ degreeMax → h ≤ l.operandLanes*scale J C ∧ h ≤ m*scale J C :=by
  let L:=localSocketRate D t g
  let κ:=1+(hostRate t reset+capRate D t g)*(t+1)+8+cutRate t f g
  refine ⟨κ+3+4,fun τ=>1+(κ+3+6)+(2*(L+(τ+κ+4))+Nat.clog 2 D.b*(t+1)),?_⟩
  intro τ B _ budget
  change 1+(κ+3+6)+(2*(L+(τ+κ+4))+Nat.clog 2 D.b*(t+1)) ≤ B at budget
  have tokenBudget : κ+3+6 ≤ B :=
    ((Nat.le_add_left (κ+3+6) 1).trans (Nat.le_add_right _ _)).trans budget
  have socketBudget : 2*(L+(τ+κ+4))+Nat.clog 2 D.b*(t+1) ≤ B :=
    (Nat.le_add_left _ _).trans budget
  have pos : 0 < B := (Nat.zero_lt_succ _).trans_le tokenBudget
  filter_upwards [DescentOperandWidth.issued D drift degreeMax t f g reset τ B pos,
    primitive_rate D op B pos,age_room B pos,eventually_ge_atTop 1,
    stage_open_split_counts D t f g reset τ L (τ+κ+4) B pos socketBudget]
    with h records primitives age high sockets
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M degree base field wire hist
  let S:=stageNumbers D t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let q₀:=2^Nat.clog 2 (NativeBranch.localLimit D S)
  let split:=NativeBranch.binLimit (k:=k) S
  let q:=q₀*(D.b^(t*J)*D.b)
  let p:=split*(h/(16*(q*split)))
  let l:=selectedLayout D S h k (tail τ J) g p drift degree f quota base field wire hist
  let Z:=S.grainAt D.b p 0
  let b:=printedBits D l.seedWidth Z op
  let a:=DescentPackedSeed.Primitive.roleBits l.seedWidth
  let co:=max (a*2^k) b
  intro small
  obtain ⟨_,_,qcap,binPos,binSize,_,_,_⟩:=native_socket_scale D t J f g reset M τ
  have live:0 < q₀:=Nat.two_pow_pos _
  obtain ⟨_,_,eq,lo,_,_⟩:=sockets M q₀ split live binPos qcap binSize
  have qpos : 0 < q:=Nat.mul_pos live (Nat.mul_pos (pow_pos D.base_pos _) D.base_pos)
  have src : l.seedWidth ≤ h:=
    (Nat.le_mul_of_pos_left _ live).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans lo)
  have piece : p ≤ h:=(Nat.le_mul_of_pos_left _ qpos).trans (by
    rw [←eq]
    exact (Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans lo)
  have operand : l.operandBits ≤ scale J 3:=records M p degree piece small
  obtain ⟨print_,raw_,_⟩:=primitives l.seedWidth Z (Nat.le_mul_of_pos_right _ D.base_pos) src
  have block : 2^k ≤ scale J κ:=groupRateAt t J S.hostGain S.capGain (cutRate t f g)
  have mono : scale J 3 ≤ scale J (κ+3):=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have packed : co ≤ scale J (κ+3):=
    max_le ((Nat.mul_le_mul raw_ block).trans_eq (by rw [scale_mul,Nat.add_comm 3])) (print_.trans mono)
  have plenty : 16*scale J (κ+3) ≤ h:=token_epoch_room h B (κ+3) high age.1 tokenBudget
  have r:=operand.trans mono
  have front : 4*l.operandBits ≤ h:=by
    exact (Nat.mul_le_mul (by decide : 4≤16) r).trans plenty
  have side : 8*co ≤ h:=(Nat.mul_le_mul (by decide : 8≤16) packed).trans plenty
  have good : 0 < l.operandBits :=by
    change 0 < DescentOperandWidth.recordBits D S k (tail τ J) drift degree p
    exact (Nat.zero_lt_succ _).trans_le (Nat.le_max_right _ _)
  have o:=pitch_fill h (2*l.operandBits) h 1 (by omega) (by omega) (by omega)
  have token:=token_lane_fit h h 1 a b (2^k) (Nat.zero_lt_succ _) (Nat.two_pow_pos _) side (by omega)
  refine ⟨o.trans (Nat.mul_le_mul_left _ (widen J (κ+3) _ _ r (by simp; omega))),?_⟩
  exact token.2.2.2.2.trans (Nat.mul_le_mul_left _ (widen J (κ+3) _ _ packed (by simp only [Nat.mul_one,co,Nat.le_refl])))

end Hierarchy.DescentDatedSeedStartup

end OAI

import OAI.Hierarchy.DescentPrivateMeterNumbers
import OAI.Hierarchy.DescentOpenStageCount
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # The private counter and the packed seat table fit the same original word -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

private theorem stage_binary_factor (h J e : ℕ) (live : 0<h) (age : J≤Nat.log 2 h) :
    2^(e*(J+1))≤2^e*(h+1)^e:=calc
  _ = 2^e*(2^J)^e :=by rw [←pow_mul,←pow_add];congr 1;ring
  _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (((Nat.pow_le_pow_right (by decide : 0<2) age).trans (Nat.pow_log_le_self 2 live.ne')).trans (Nat.le_succ _)) _)

/-- At a scheduled terminal word the full private aggregate and both additional
packed seat banks fit alongside the literal batch. The physical epoch grain
is at most its input width by the definition of SIMD lanes. -/
theorem terminal_private_word_room (t f g reset τ : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ J M p packWidth w : ℕ,
      let S:=stageNumbers G t J f g reset M (tail τ J)
      J≤Nat.log 2 h → 2^h≤M → M≤(2^h)^2 → S.firstWidth G.b p≤h → packWidth≤h → 3*h≤w →
      Nat.log 2 (NativeBranch.privateMax G S p)+1≤w ∧ S.batch+2*packWidth<2^w ∧ S.batch<2^w :=by
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let e:=κ+11+(hostRate t reset+capRate G t g)*(t+1)
  let d:=(t+1)*GadgetNetwork.privateRate G
  filter_upwards [eventually_ge_atTop 1,stage_open_record_capacity G t f g reset τ ((d+4)*2^e) (e+1)]
    with h positive storage
  intro J M p packWidth w S age low high payload packed wide
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let R:=2^e*(h+1)^e
  let gain:=hostRate t reset+capRate G t g
  let homes:=M*(S.copies*h)
  let area:=(R*(h+1))*homes
  have mesh : J≤h:=age.trans (Nat.log_le_self 2 h)
  have length : S.length≤(t+1)*(h+1):=Nat.mul_le_mul_left _ (mesh.trans (Nat.le_succ h))
  have coeff : κ≤e ∧ 11≤e ∧ gain*(t+1)≤e:=by dsimp only [e,gain];omega
  have key : k≤κ*(J+1):=groupBits_linear ..
  have dyadic:=stage_binary_factor h J e positive age
  have radix : S.radix≤R:=by
    change 2^k≤_
    exact (Nat.pow_le_pow_right (by decide) (key.trans (Nat.mul_le_mul_right (J+1) coeff.1))).trans dyadic
  have gains : (2^S.hostGain)^S.length*2^(11+S.capGain*S.length)≤R:=by
    rw [←pow_mul,←pow_add]
    apply le_trans _ dyadic
    apply Nat.pow_le_pow_right (by decide)
    calc
      _ = 11+(gain*(t+1))*J :=by
        change (hostRate t reset)*((t+1)*J)+(11+capRate G t g*((t+1)*J))=
          11+((hostRate t reset+capRate G t g)*(t+1))*J
        ring
      _ ≤ e+e*J := Nat.add_le_add coeff.2.1 (Nat.mul_le_mul_right J coeff.2.2)
      _ = _ :=by ring
  have copia : 0<S.copies:=by
    change 0<2^(tail τ J)*(2^k)^((t+1)*J+1)
    positivity
  have hm : 0<M:=(Nat.two_pow_pos _).trans_le low
  have hHomes : h≤homes:= (Nat.le_mul_of_pos_left _ copia).trans (Nat.le_mul_of_pos_left _ hm)
  have vR : 0<R:=Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (Nat.succ_pos h))
  have hArea : homes≤area:=Nat.le_mul_of_pos_left _ (Nat.mul_pos vR (Nat.succ_pos h))
  have living : 0<area:=positive.trans (hHomes.trans hArea)
  have light : R*homes≤area:=Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos h))
  have seats : S.batch≤area:=by
    calc
      _ = (M*S.copies)*((2^S.hostGain)^S.length*2^(11+S.capGain*S.length)) :=by
        unfold AtomSchedule.batch
        change (M*S.copies)*(2^S.hostGain)^S.length*2^(11+S.capGain*S.length)=_
        ac_rfl
      _ ≤ homes*R := Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ positive)) gains
      _ ≤ area := (Nat.mul_comm homes R).le.trans light
  have privateCount : NativeBranch.privateMax G S p≤d*area:=by
    calc
      _ = S.length*GadgetNetwork.privateRate G*S.radix*(M*(S.copies*S.firstWidth G.b p)) :=by
        unfold NativeBranch.privateMax
        change S.length*GadgetNetwork.privateRate G*S.radix*M*(S.copies*S.firstWidth G.b p)=_
        ac_rfl
      _ ≤ ((t+1)*(h+1))*GadgetNetwork.privateRate G*R*homes :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ length) radix) (Nat.mul_le_mul_left M (Nat.mul_le_mul_left _ payload))
      _ = d*area :=by dsimp only [d,area];ring
  have bound : (d+4)*area≤2^(3*h):=by
    apply storage J M M h _ age high le_rfl
    change (d+4)*area≤(d+4)*2^e*(h+1)^(e+1)*M*(S.copies*h)
    dsimp only [area,R,homes]
    rw [pow_succ (h+1) e]
    exact le_of_eq (by ring)
  have code : (d+4)*area≤2^w:=bound.trans (Nat.pow_le_pow_right (by decide) wide)
  rw [Nat.add_mul] at code
  have row : packWidth≤area:=packed.trans (hHomes.trans hArea)
  have counter : NativeBranch.privateMax G S p<2^w:=by omega
  have large : 0<w:=by omega
  exact ⟨Nat.log_lt_of_lt_pow' large.ne' counter,by omega,by omega⟩

end Hierarchy.DescentSixParty

end OAI

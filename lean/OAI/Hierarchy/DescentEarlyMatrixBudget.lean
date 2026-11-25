import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentPrivateGateScale
import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentNativeSocketScale
import OAI.Hierarchy.DescentOpenSplitStageCount

namespace OAI
/-! # Dated matrix ROM and the price of the original open-port reel at a common height -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Filter
open scoped Topology
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)
variable (rounds f g reset τ B : ℕ)
local notation "κ" => 1+(hostRate rounds reset+capRate G rounds g)*(rounds+1)+8+cutRate rounds f g
local notation "bits" => fun J => groupBits rounds J (hostRate rounds reset) (capRate G rounds g) (cutRate rounds f g)
local notation "sched" => fun J M => stageNumbers G rounds J f g reset M (tail τ J)

/-- Charge a common ROM half-table and all original exterior plane rows to the two
summands in the open-host estimate. The number of original ports is unrestricted. -/
theorem early_open_words (h M copies s T factor E j r w fee : ℕ)
    (large : 10≤h) (support : 2^h≤2*(M*copies)) (power : T≤ s)
    (arch : w+1≤factor*h) (outside : copies=2^(j+(j+r))) (packed : h≤32*(2^j*s))
    (rows : fee≤8192*(2^(h/2)+E*2^(j+r))) :
    fee*(w+1)*T≤(262144*factor)*((copies*s)*(M+T*E)) := by
  have localTable:2^(h/2)*h*T≤(copies*s)*M := calc
    _ ≤ (M*copies)*s := Nat.mul_le_mul (table_fund large support) power
    _ = _ := by ring
  have exterior:E*2^(j+r)*h*T≤32*((copies*s)*(T*E)) := calc
    _ ≤ E*2^(j+r)*(32*(2^j*s))*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ packed)
    _ = _ := by rw [outside,pow_add 2 j (j+r)]; ring
  calc
    _ ≤ 8192*(2^(h/2)+E*2^(j+r))*(factor*h)*T :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul rows arch)
    _ = (8192*factor)*(2^(h/2)*h*T+E*2^(j+r)*h*T) := by ring
    _ ≤ (8192*factor)*((copies*s)*M+32*((copies*s)*(T*E))) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add localTable exterior)
    _ ≤ _ := by ring_nf; omega

private theorem matrix_budget (age d h : ℕ) (fit : age+1+(d*d+d*d)≤h/2) :
    age*(2^(d*d)+2^(d*d)*2^(d*d))≤2^(h/2) := by
  have one:1≤2^(d*d):=Nat.one_le_two_pow
  have pad:2^(d*d)≤2^(d*d)*2^(d*d) := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^(d*d)) one
  have page:2^(d*d)+2^(d*d)*2^(d*d)≤2^(1+(d*d+d*d)) := by
    rw [pow_add 2 1 _,pow_add 2 (d*d) (d*d)]
    omega
  calc
    _ ≤ 2^age*2^(1+(d*d+d*d)) := Nat.mul_le_mul (Nat.lt_two_pow_self.le) page
    _ = 2^(age+1+(d*d+d*d)) := by rw [←pow_add,Nat.add_assoc]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) fit

theorem early_matrix_words (large : 20≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M, let S:=sched J M
        let d:=S.groupWidth (bits J) (tail τ J) 0+bits J
        S.length*(2^(d*d)+2^(d*d)*2^(d*d))≤2^(h/2) ∧
          S.length≤2^(h/2) ∧ 4*(d*d+d+1)≤h := by
  filter_upwards [eventually_home 0 0 10 B (by omega) (by omega),
    eventually_late (τ+rounds+κ+10) B (by omega)] with h room late
  intro J
  let X:=2^(J+1)
  change τ+rounds+κ+10≤J at late
  have xJ:J+1≤X:=Nat.lt_two_pow_self.le
  have one:1≤X:=Nat.one_le_two_pow
  have x2:2≤X:=by dsimp [X];rw [pow_succ];have:=Nat.one_le_two_pow (n:=J);omega
  have raw:=room.2 0 1 (scale J 10) (by simp [tail]) (by simp) le_rfl
  have cap:32*X^10≤h:=by
    change 32*(1*2^(10*(J+1)))≤h at raw
    simpa only [X,←pow_mul,Nat.mul_comm (J+1) 10,Nat.one_mul] using raw
  let a:=(rounds+1)*J
  let d:=tail τ J+bits J*a+bits J
  have age:a≤X^2:=by dsimp [a];rw [pow_two];exact Nat.mul_le_mul (by omega) (by omega)
  have bit:bits J≤X^2:=by rw [pow_two];exact (groupBits_linear ..).trans (Nat.mul_le_mul (by omega) xJ)
  have tailBound:tail τ J≤X^2:=by unfold tail;rw [pow_two];exact Nat.mul_le_mul (by omega) xJ
  have x24:X^2≤X^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have prodBits:bits J*a≤X^4:=by simpa only [←pow_add] using Nat.mul_le_mul bit age
  have digit:d≤3*X^4:=calc
    _ ≤ X^4+X^4+X^4 := Nat.add_le_add (Nat.add_le_add (tailBound.trans x24) prodBits) (bit.trans x24)
    _ = _ := by ring
  have square:d*d≤9*X^8:=calc
    _ ≤ (3*X^4)*(3*X^4) := Nat.mul_le_mul digit digit
    _ = _ := by ring
  have extra:X^4≤X^8:=Nat.pow_le_pow_right (by omega) (by decide)
  have next:4*X^8≤X^10:=calc
    _ ≤ X^2*X^8 := Nat.mul_le_mul_right _ (by simpa only [pow_two] using Nat.mul_le_mul x2 x2)
    _ = _ := by ring
  have pos:1≤X^8:=Nat.pow_pos (by omega : 0<X)
  have sizes:a+1+(d*d+d*d)≤h/2:=by omega
  intro M
  change a*(2^(d*d)+2^(d*d)*2^(d*d))≤2^(h/2) ∧ a≤2^(h/2) ∧ 4*(d*d+d+1)≤h
  exact ⟨matrix_budget a d h sizes,(show a≤h/2 by omega).trans Nat.lt_two_pow_self.le,by omega⟩


theorem early_native_packing (large : 20≤B) (reserve : 2*localSocketRate G rounds g≤τ)
    (budget : 2*(localSocketRate G rounds g+(τ+κ+4))+Nat.clog 2 G.b*(rounds+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M : ℕ, let S:=sched J M
        let j:=Nat.clog 2 (NativeBranch.localLimit G S)
        let dim:=S.groupWidth (bits J) (tail τ J) 0+bits J
        let r:=dim-2*j
        let split:=NativeBranch.binLimit (k:=bits J) S
        let U:=G.b^(rounds*J)*G.b
        let p:=split*(h/(16*((2^j*U)*split)))
        let s:=S.firstWidth G.b p
        dim=j+(j+r) ∧ S.copies=2^(j+(j+r)) ∧ 2^J≤ s ∧ 16*(2^j*s)≤h ∧ h≤32*(2^j*s) := by
  let a:=localSocketRate G rounds g
  have bpos:0<B:=by omega
  have head:2*(0+0+(a+1))≤B:=by dsimp [a];omega
  filter_upwards [stage_open_split_counts G rounds f g reset τ a (τ+κ+4) B bpos budget,
    eventually_home 0 0 (a+1) B bpos head] with h grain enough
  intro J M S j dim r split U p s
  obtain ⟨_,_,qbound,wpos,wbound,_,_,width⟩:=native_socket_scale G rounds J f g reset M τ
  have qpos:0<2^j:=Nat.two_pow_pos _
  obtain ⟨_,_,_,low,high,_,_⟩:=grain M (2^j) split qpos wpos qbound wbound
  have shape:dim=j+(j+r):=by have:2*j≤dim:=(width reserve).2;dsimp [r];omega
  have copies:S.copies=2^(j+(j+r)):=calc
    _ = S.groupCount 0*2^(bits J) := by
      simpa only [Fintype.card_fin,Fintype.card_prod] using Fintype.card_congr (S.initialDigits (show S.radix=2^(bits J) from rfl))
    _ = 2^dim := by
      rw [←S.group_power (show S.baseGroups=2^(tail τ J) from rfl) (show S.radix=2^(bits J) from rfl) 0,←pow_add]
    _ = _ := by rw [shape]
  have short:2^J≤ scale J 1:=by
    unfold scale
    simp only [one_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  have small:(2^j)*2^J≤ scale J (a+1):=(Nat.mul_le_mul qbound short).trans_eq (scale_mul J a 1)
  have alloc:=enough.2 0 1 (scale J (a+1)) (by simp [tail]) (by simp) le_rfl
  have widthRoom:32*((2^j)*2^J)≤h:=(Nat.mul_le_mul_left 32 small).trans (by simpa using alloc)
  have upper : h≤32*(2^j*s) := high
  have power:2^J≤ s:=Nat.le_of_mul_le_mul_left (show (32*2^j)*2^J≤(32*2^j)*s by
    simpa only [Nat.mul_assoc] using widthRoom.trans upper) (Nat.mul_pos (by decide) qpos)
  exact ⟨shape,copies,power,low,high⟩

end
end Hierarchy.DescentSixParty

end OAI

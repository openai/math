import OAI.Hierarchy.DescentNativeSocketScale
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! The positive original selected chunk pays the width used in the dated
ledger independently of the tail-dependent number of terminal bins. -/
namespace Hierarchy.DescentSixParty
open DescentCompiler TerminalScale
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem registered_packing_width (t J f g reset copies τ h p : ℕ) :
    let S:=stageNumbers G t J f g reset copies (tail τ J)
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    let socket:=2^Nat.clog 2 (NativeBranch.localLimit G S)
    let bin:=NativeBranch.binLimit (k:=k) S
    0 < p → p=bin*(h/(16*((socket*(G.b^(t*J)*G.b))*bin))) →
    p ≤ h ∧ S.firstWidth G.b p ≤ h ∧ h ≤ p*scale J (5+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))) :=by
  intro S k socket bin positive chosen
  let fields:=G.b^(t*J)*G.b
  let q:=socket*fields
  let den:=16*(q*bin)
  let r:=h/den
  obtain ⟨_,_,_,binPositive,_,fieldPositive,bitSize,_⟩:=native_socket_scale G t J f g reset copies τ
  have socketPositive:0 < socket:=Nat.two_pow_pos _
  have qPositive:0 < q:=Nat.mul_pos socketPositive fieldPositive
  have denPositive:0 < den:=Nat.mul_pos (by decide) (Nat.mul_pos qPositive binPositive)
  have rPositive:0 < r:=by
    apply Nat.pos_of_ne_zero
    intro rzero
    change p=bin*r at chosen
    rw [rzero,Nat.mul_zero] at chosen
    omega
  have priced:den*r=16*(q*p):=by
    change p=bin*r at chosen
    rw [chosen]
    dsimp [den]
    ring
  have split:=Nat.div_add_mod h den
  change den*r+h%den=h at split
  have rem:=Nat.mod_lt h denPositive
  have cover:den ≤ den*r:=Nat.le_mul_of_pos_right _ rPositive
  have below:16*(q*p) ≤ h:=by omega
  have cost:h ≤ 32*(q*p):=by omega
  have use : q*p ≤ h:=(Nat.le_mul_of_pos_left _ (by decide : 0 < 16)).trans below
  have first:S.firstWidth G.b p=fields*p:=by
    change (p*G.b^(t*J-(0-0/(t+1))))*G.b=fields*p
    simp only [Nat.zero_div,Nat.sub_zero,fields]
    ring
  refine ⟨(Nat.le_mul_of_pos_left _ qPositive).trans use,?_,?_⟩
  · rw [first]
    exact (Nat.mul_le_mul_right p (Nat.le_mul_of_pos_left fields socketPositive)).trans use
  · rw [←scale_mul]
    calc
      _ ≤ 32*(q*p):=cost
      _ = p*(32*q):=by ring
      _ ≤ _:=Nat.mul_le_mul_left p (Nat.mul_le_mul
        (show 32 ≤ scale J 5 by
          change (2:ℕ)^5 ≤ 2^(5*(J+1))
          exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega)) bitSize)

/-- Every physical reset matrix has one quadratic logarithmic dimension bound,
regardless of the tail coefficient and bus divisor used to select its date. -/
theorem registered_matrix_dimension (t J f g reset copies frozen age h : ℕ)
    (epoch : J ≤ Nat.log 2 h) (tailRoom : frozen ≤ Nat.log 2 h) :
    let S:=stageNumbers G t J f g reset copies frozen
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
    S.groupWidth k frozen age+k ≤ (1+κ*(t+2))*(Nat.log 2 h+1)^2 :=by
  intro S k κ
  let l:=Nat.log 2 h
  have kFit:k ≤ κ*(l+1):=(groupBits_linear ..).trans (Nat.mul_le_mul_left κ (Nat.succ_le_succ epoch))
  have len:S.length ≤ (t+1)*l:=Nat.mul_le_mul_left _ epoch
  have remaining:S.length-age+1 ≤ (t+2)*(l+1):=by
    have less:=Nat.sub_le S.length age
    nlinarith only [less,len,Nat.zero_le t,Nat.zero_le l]
  have terms:=Nat.mul_le_mul kFit remaining
  change frozen+k*(S.length-age)+k ≤ (1+κ*(t+2))*(l+1)^2
  calc
    _ = frozen+k*(S.length-age+1):=by ring
    _ ≤ l+κ*(l+1)*((t+2)*(l+1)):=Nat.add_le_add tailRoom terms
    _ ≤ (1+κ*(t+2))*(l+1)^2:=by nlinarith only [Nat.zero_le (l*l),Nat.zero_le l]

end Hierarchy.DescentSixParty

end OAI

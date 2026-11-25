import OAI.Hierarchy.DescentTerminalNativeLimits
import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentResetDigits

namespace OAI
/-! # The dyadic external socket count and the true terminal bin height at a native stage -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- This rate only uses the local incidence growth, before the residual tail is chosen. -/
def localSocketRate (t g : ℕ) := 9+Nat.clog 2 G.b+capRate G t g*(t+1)

theorem native_socket_scale (t J f g reset M τ : ℕ) :
    let S:=stageNumbers G t J f g reset M (tail τ J)
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    let j:=Nat.clog 2 (NativeBranch.localLimit G S)
    let W:=NativeBranch.binLimit (k:=k) S
    let a:=localSocketRate G t g
    let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
    let U:=G.b^(t*J)*G.b
    j≤a*(J+1) ∧ NativeBranch.localLimit G S≤2^j ∧ 2^j≤scale J a ∧
      0<W ∧ W≤scale J (τ+κ+4) ∧ 0<U ∧ 2^j*U≤scale J (a+Nat.clog 2 G.b*(t+1)) ∧
      (2*a≤τ → j≤S.groupWidth k (tail τ J) S.length+k ∧ 2*j≤S.groupWidth k (tail τ J) 0+k) := by
  intro S k j W a κ U
  let ℓ:=Nat.clog 2 G.b
  let gain:=capRate G t g*(t+1)
  have bsize : G.b≤2^ℓ := Nat.le_pow_clog (by decide) _
  have bpos : 0<G.b := by have:=G.paid;omega
  have numerator : 2*G.b≤2^(ℓ+1) := by
    rw [pow_succ,Nat.mul_comm (2^ℓ)]
    exact Nat.mul_le_mul_left 2 bsize
  have sum : ℓ+1+(8+gain*J)≤a*(J+1) := by
    change ℓ+1+(8+gain*J)≤(9+ℓ+gain)*(J+1)
    rw [Nat.add_mul]
    have fixed:=Nat.le_mul_of_pos_right (9+ℓ) (Nat.succ_pos J)
    have dynamic:=Nat.mul_le_mul_left gain (Nat.le_succ J)
    calc
      _ = (9+ℓ)+gain*J := by omega
      _ ≤ _ := Nat.add_le_add fixed dynamic
  have capped : NativeBranch.localLimit G S≤2^(a*(J+1)) := calc
    _ = (2*G.b)*2^(8+gain*J) := by
      change (2*G.b)*2^(8+capRate G t g*((t+1)*J))=_
      dsimp only [gain]
      rw [Nat.mul_assoc (capRate G t g)]
    _ ≤ 2^(ℓ+1)*2^(8+gain*J) := Nat.mul_le_mul_right _ numerator
    _ ≤ _ := by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) sum
  have age : j≤a*(J+1) := Nat.clog_le_of_le_pow capped
  have sockets : 2^j≤scale J a := Nat.pow_le_pow_right (by decide) age
  have ksize : k≤κ*(J+1) := groupBits_linear ..
  let V:=2^(tail τ J)*2^k
  have units : 0<V := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have cells : W=3*V+6 := by
    simp only [W,NativeBranch.binLimit,AtomSchedule.groupCount,Nat.sub_self,pow_zero,Nat.mul_one]
    rfl
  have base : V≤scale J (τ+κ) := by
    change 2^(τ*(J+1))*2^k≤scale J (τ+κ)
    rw [←scale_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) ksize)
  have binSize : W≤scale J (τ+κ+4) := calc
    _ ≤ V*16 := by rw [cells];omega
    _ ≤ scale J (τ+κ)*scale J 4 := Nat.mul_le_mul base (by
      change 2^4≤2^(4*(J+1))
      exact Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos J)))
    _ = _ := scale_mul ..
  have uSize : U≤scale J (ℓ*(t+1)) := by
    change G.b^(t*J)*G.b≤2^((ℓ*(t+1))*(J+1))
    rw [←pow_succ]
    apply (Nat.pow_le_pow_left bsize _).trans
    rw [←pow_mul,Nat.mul_assoc]
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.mul_le_mul_left _ (by nlinarith : t*J+1≤(t+1)*(J+1))
  refine ⟨age,Nat.le_pow_clog (by decide) _,sockets,by rw [cells];omega,binSize,
    Nat.mul_pos (Nat.pow_pos bpos) bpos,?_,?_⟩
  · rw [←scale_mul]
    exact Nat.mul_le_mul sockets uSize
  · intro reserve
    have room : 2*j≤tail τ J := by
      change 2*j≤τ*(J+1)
      have fee:=Nat.mul_le_mul_left 2 age
      simpa only [Nat.mul_assoc] using fee.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (J+1) reserve)
    dsimp only [AtomSchedule.groupWidth]
    constructor <;> omega

end Hierarchy.DescentSixParty

end OAI

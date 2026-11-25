import OAI.Hierarchy.DescentCanvasDateBill
import OAI.Hierarchy.DescentResetIngressWork

namespace OAI
/-! Fund the physical reset ingress at the date's old host and group counts. -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

def ingressUnit (t f g reset τ B quota ratio J : ℕ) :=
  scale J (canvasRate G t f g reset) *
  (2097152*(ratio+1)*(localCoefficient G t f g reset quota τ*(2*B+1)^2+1)*(tail τ J+1)^2)

private theorem columns_le (t f g reset J M tail i n : ℕ)
    (age : i≤(t+1)*J) (cap : n≤2^(8+(capRate G t g-(G.b+3))*i)) :
    let S:=stageNumbers G t J f g reset M tail
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    2^k+2^k*(2*n)+1≤2*scale J (canvasRate G t f g reset) := by
  intro S k
  let v:=capRate G t g
  let a:=1+(hostRate t reset+v)*(t+1)+8+cutRate t f g
  have gk:k ≤ a*(J+1):=groupBits_linear ..
  have vcap:(v-(G.b+3))*i ≤ v*(t+1)*J:=(Nat.mul_le_mul (Nat.sub_le ..) age).trans_eq (by ring)
  have qty:=cap.trans (Nat.pow_le_pow_right (by decide : 0<2) (Nat.add_le_add_left vcap 8))
  have big:=Nat.two_pow_pos (8+v*(t+1)*J)
  have packed:2*n+1≤2^(10+v*(t+1)*J):=by
    rw [show 10+v*(t+1)*J=(8+v*(t+1)*J)+2 by omega,pow_add]
    norm_num
    omega
  have kg:k+(10+v*(t+1)*J)≤(a+10+v*(t+1))*(J+1):=by
    nlinarith only [gk,Nat.zero_le J,Nat.zero_le (v*(t+1))]
  have slots:=Nat.mul_le_mul_left (2^k) packed
  rw [←pow_add] at slots
  have top:=slots.trans (Nat.pow_le_pow_right (by decide : 0<2) kg)
  have positive:=Nat.two_pow_pos ((a+10+v*(t+1))*(J+1))
  change 2^k+2^k*(2*n)+1≤2*2^((a+10+v*(t+1))*(J+1))
  nlinarith only [top,positive]

/-- Uniform conversion of the literal two traffic terms and one shared book.
The statement is independent of the body, so it applies to the actual named reset phase. -/
theorem ingress_date_scale (t f g reset τ B quota ratio saving : ℕ) (tailPos : 0<τ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop,∀M i p n : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let b:=S.localWalshBits p (S.groupWidth k (tail τ J) i+k) f quota
      let H:=S.hostSize i
      let N:=2^k+2^k*(2*n)+1
      let U:=ingressUnit G t f g reset τ B quota ratio J
      i≤S.length → p ≤ h → 2^h≤M → n≤2^(8+(S.capGain-(G.b+3))*i) →
      H*h*(65536*N*ratio)+H*S.groupCount i*(65536*N*ratio*(16*2^k*b))+
        (65536*N*ratio*(h+1)^3)*2^(h/2) ≤ H*h*U+H*(S.groupCount i*S.radix)*U+M/(2^J)^saving := by
  let K:=canvasRate G t f g reset
  let C:=localCoefficient G t f g reset quota τ
  filter_upwards [global_control_shared (131072*(ratio+1)) 3 K 1 saving] with h common
  intro M i p n J S k b H N U age payload ambient cap
  let W:=scale J K
  let V:=tail τ J+1
  let a:=C*(2*B+1)^2+1
  have Jle:J≤Nat.log 2 h:=Nat.div_le_self ..
  have Vle:tail τ J≤τ*(Nat.log 2 h+1)^2:=
    Nat.mul_le_mul_left _ ((Nat.succ_le_succ Jle).trans (by nlinarith))
  have width:b≤C*(Nat.log 2 h+1)^2:=actual_width G t J f g reset M (tail τ J) i h p quota τ payload Jle Vle age
  have div:=Nat.mod_add_div (Nat.log 2 h) (2*B)
  have rem:=Nat.mod_lt (Nat.log 2 h) (show 0<2*B by omega)
  change Nat.log 2 h%(2*B)+2*B*J=Nat.log 2 h at div
  have log:Nat.log 2 h+1≤(2*B+1)*(J+1):=by nlinarith only [div,rem]
  have stage:J+1≤V:=by change J+1≤τ*(J+1)+1;have q:=Nat.le_mul_of_pos_left (J+1) tailPos;omega
  have mag:0<V^2:=by dsimp [V];positivity
  have square:=Nat.pow_le_pow_left (log.trans (Nat.mul_le_mul_left (2*B+1) stage)) 2
  rw [mul_pow] at square
  have bbound:b ≤ a*V^2:=by
    have p:=width.trans (Nat.mul_le_mul_left C square)
    dsimp only [a];nlinarith only [p,mag]
  have aPos:0 < a:=by dsimp only [a];omega
  have one:1 ≤ a*V^2:=Nat.mul_pos aPos mag
  have cols:N≤2*W:=columns_le G t f g reset J M (tail τ J) i n age cap
  have host:65536*N*ratio≤U:=calc
    _≤65536*(2*W)*(ratio+1)*(a*V^2) := by
      exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ cols) (Nat.le_succ _)).trans (Nat.le_mul_of_pos_right _ one)
    _≤U := by change _≤W*(2097152*(ratio+1)*a*V^2);nlinarith only [Nat.zero_le (W*(ratio+1)*a*V^2)]
  have load:65536*N*ratio*(16*b)≤U:=calc
    _≤65536*(2*W)*(ratio+1)*(16*(a*V^2)) := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ cols) (Nat.le_succ _)) (Nat.mul_le_mul_left _ bbound)
    _=U :=by change _=W*(2097152*(ratio+1)*a*V^2);ring
  have exponent:K*(J+1)≤K*(J+1)^1:=by rw [pow_one]
  have table:=common J (K*(J+1)) M Jle exponent ambient
  have lut:(65536*N*ratio*(h+1)^3)*2^(h/2)≤M/(2^J)^saving:=by
    apply le_trans _ table
    calc
      _≤(65536*(2*W)*(ratio+1)*(h+1)^3)*2^(h/2) := by gcongr; omega
      _=(131072*(ratio+1)*(h+1)^3*2^(K*(J+1)))*2^(h/2) :=by dsimp [W,scale];ring
  have host₁:=Nat.mul_le_mul_left (H*h) host
  have load₁:=Nat.mul_le_mul_left (H*(S.groupCount i*2^k)) load
  change _≤H*h*U+H*(S.groupCount i*2^k)*U+_
  nlinarith only [host₁,load₁,lut]

end Hierarchy.DescentSixParty

end OAI

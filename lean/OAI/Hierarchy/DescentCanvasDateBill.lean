import OAI.Hierarchy.DescentCanvasNumericBill
import OAI.Hierarchy.DescentEstimatorDateTariff

namespace OAI
/-! # The full dated reset prelude at its actual signed-cable and packed group sizes -/
namespace Hierarchy.DescentSixParty
open Filter DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh DescentSIMDLookup
open PackedFlow.Canvas PackedFlow.Canvas.Setup

variable {F : Type} [Field F] (G : PoweredGadget F)

def canvasRate (t f g reset : ℕ) :=
  (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)+10+capRate G t g*(t+1)

def canvasFactor (t f g reset τ B quota D ratio : ℕ) :=
  let C:=localCoefficient G t f g reset quota τ*(2*B+1)^2+1
  canvasCoeff D*(ratio+1)*16*C^2

private theorem cable_factor (t f g reset J M tail i n : ℕ)
    (age : i≤(t+1)*J) (capacity : n≤2^(8+(capRate G t g-(G.b+3))*i)) :
    let S:=stageNumbers G t J f g reset M tail
    2^(groupBits t J S.hostGain S.capGain (cutRate t f g))*(2*n+1)≤ scale J (canvasRate G t f g reset) :=by
  let A:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let v:=capRate G t g
  have gb:=groupBits_linear t J (hostRate t reset) v (cutRate t f g)
  have ex:(v-(G.b+3))*i≤(v*(t+1))*J:=(Nat.mul_le_mul (Nat.sub_le ..) age).trans_eq (by ring)
  have cap₀:=capacity.trans (Nat.pow_le_pow_right (by decide : 0<2) (Nat.add_le_add_left ex 8))
  have cap₁:2*n+1≤2^(10+v*(t+1)*J):=by
    rw [show 10+v*(t+1)*J=(8+v*(t+1)*J)+2 by omega,pow_add]
    have atLeast:=Nat.two_pow_pos (8+v*(t+1)*J)
    norm_num
    omega
  change 2^(groupBits t J (hostRate t reset) v (cutRate t f g))*(2*n+1)≤_
  apply (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<2) gb) cap₁).trans
  rw [←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  change A*(J+1)+(10+v*(t+1)*J)≤(A+10+v*(t+1))*(J+1)
  nlinarith only [Nat.zero_le J,Nat.zero_le (v*(t+1))]

/-- A complete chronological native prelude has exactly two signed half-banks
for each of the true old capacity slots. Both front and Walsh dictionary books
are paid only once. The optional saving concerns only that shared term. -/
theorem canvas_date_tariff (t f g reset τ B quota D ratio saving : ℕ) (tailPos : 0<τ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop,∀M i p w n batch : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let m:=S.groupWidth k (tail τ J) i+k
      let b:=S.localWalshBits p m f quota
      let l:=laneBits m h b
      let unit:=scale J (canvasRate G t f g reset)*(canvasFactor G t f g reset τ B quota D ratio*(tail τ J+1)^4)
      ∀X : Date k (2*n), i≤S.length → p≤h → 2^h≤M → w≤ratio*h →
        n≤2^(8+(S.capGain-(G.b+3))*i) → 2^l=batch*2^k →
        X.fee (S.hostSize i) D (S.groupCount i) (m-l) l b (Nat.clog 2 (D+1)) batch w ≤
          S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+M/(2^J)^saving :=by
  let C:=localCoefficient G t f g reset quota τ
  let A:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let a:=C*(2*B+1)^2+1
  filter_upwards [eventually_actual_width G t f g reset B quota τ,
    global_control_shared (canvasCoeff D*(ratio+1)) 2 A 1 saving,
    eventually_late (Nat.clog 2 (D+1)) B den,eventually_ge_atTop 1] with h widths tables late hpos
  intro M i p w n batch
  let J:=Nat.log 2 h/(2*B);let V:=tail τ J+1
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let m:=S.groupWidth k (tail τ J) i+k
  let b:=S.localWalshBits p m f quota
  let l:=laneBits m h b;let H:=S.hostSize i
  let W:=scale J (canvasRate G t f g reset)
  let U:=W*(canvasFactor G t f g reset τ B quota D ratio*V^4)
  dsimp only
  intro X age payload ambient word cap lanes
  change X.fee H D (S.groupCount i) (m-l) l b (Nat.clog 2 (D+1)) batch w≤H*h*U+H*(S.groupCount i*S.radix)*U+M/(2^J)^saving
  have logAge:J≤Nat.log 2 h:=Nat.div_le_self ..
  have span:tail τ J≤τ*(Nat.log 2 h+1)^2:=by
    exact Nat.mul_le_mul_left _ ((Nat.succ_le_succ logAge).trans (by nlinarith))
  have small:8*b≤h/2:=(widths M (tail τ J) i p payload span age).1
  have bpos:0<b:=by change 0<DescentWalshPrecision.bits m f quota (S.censusBits p);unfold DescentWalshPrecision.bits;omega
  have m_le:m≤b:=by change m≤DescentWalshPrecision.bits m f quota (S.censusBits p);unfold DescentWalshPrecision.bits;omega
  have wide:=actual_width G t J f g reset M (tail τ J) i h p quota τ payload logAge span age
  have floor:Nat.log 2 h+1≤(2*B+1)*(J+1):=by
    have rem:=Nat.mod_lt (Nat.log 2 h) (show 0<2*B by omega)
    have eqn:=Nat.mod_add_div (Nat.log 2 h) (2*B)
    change Nat.log 2 h%(2*B)+2*B*J=Nat.log 2 h at eqn
    nlinarith only [rem,eqn]
  have raw:b≤C*(Nat.log 2 h+1)^2:=wide
  have bv:b+1≤a*V^2:=by
    have stamp:J+1≤V:=by change J+1≤τ*(J+1)+1;have z:=Nat.le_mul_of_pos_left (J+1) tailPos;omega
    have grow:=Nat.mul_le_mul_left C (Nat.pow_le_pow_left (floor.trans (Nat.mul_le_mul_left _ stamp)) 2)
    rw [mul_pow, ←Nat.mul_assoc] at grow
    have vv : 0<V^2:=by dsimp [V];positivity
    dsimp [a];rw [Nat.add_mul,Nat.one_mul];omega
  have mv:m+1≤a*V^2:=(Nat.succ_le_succ m_le).trans bv
  have mass:2^k*(2*n+1)≤W:=cable_factor G t f g reset J M (tail τ J) i n age cap
  have kp : J≤k:=by change J≤J+_+8+_;omega
  have short:Nat.clog 2 (D+1)≤b*2^k:=
    ((late.trans kp).trans (Nat.lt_two_pow_self (n:=k)).le).trans (Nat.le_mul_of_pos_left _ bpos)
  have hp:0<H:=by
    change 0<M*(2^S.hostGain*S.radix)^i
    have mp:0<M:=(Nat.two_pow_pos _).trans_le ambient
    have rp:0<S.radix:=Nat.two_pow_pos _
    positivity
  have lb:l≤ m:=Nat.min_le_left ..;have dim:m-l+l=m:=Nat.sub_add_cancel lb
  have geom:2^m=S.groupCount i*2^k:=by dsimp only [m];rw [pow_add,S.group_power (tail:=tail τ J) (k:=k) rfl rfl]
  have bm : 0<batch := by
    by_contra! no
    have z : batch=0 := by omega
    rw [z,Nat.zero_mul] at lanes
    exact (Nat.two_pow_pos _).ne' lanes
  have rowCount:=original_chunks (u:=m-l) (l:=l) (k:=k) (R:=S.groupCount i) (M:=batch) (by rw [dim,geom]) lanes bm
  have big:bigKey l b≤h/2:=keys_fit bpos (by omega : 8*b≤h)
  have price:=X.measured H D (S.groupCount i) (m-l) l b (Nat.clog 2 (D+1)) batch h w hp rowCount
    (lanes.trans (Nat.mul_comm ..)) short big
  rw [dim] at price
  have layer: H*2^(m-l)*h≤H*h+16*H*2^m*b:=per_layer H bpos (by omega : 8*b≤h)
  have rsize:k≤A*(J+1)^1:=by rw [pow_one];exact groupBits_linear ..
  have common:=tables J k M logAge rsize ambient
  have mh:m+1≤h+1:=by omega
  have word' : w≤(ratio+1)*(h+1):=by nlinarith only [word,Nat.zero_le h,Nat.zero_le ratio]
  have dict : canvasCoeff D*((m+1)*2^k*2^(h/2))*w≤M/(2^J)^saving:=by
    apply le_trans _ common
    calc
      _ ≤ canvasCoeff D*(((h+1)*2^k)*2^(h/2))*((ratio+1)*(h+1)):=by gcongr
      _ = _ :=by ring
  have heights : canvasCoeff D*(m+1)*(2^k*(2*n+1))*ratio≤U:=by
    calc
      _ ≤ canvasCoeff D*(a*V^2)*W*(ratio+1):=by gcongr; omega
      _ ≤ canvasCoeff D*(a*V^2)*W*(ratio+1)*(16*(a*V^2)):=Nat.le_mul_of_pos_right _ (by dsimp [a,V];positivity)
      _ = _:=by dsimp [U,canvasFactor,a,C,V,W];ring
  have loads : 16*(canvasCoeff D*(m+1)*(2^k*(2*n+1))*ratio)*b≤U:=by
    calc
      _ ≤ 16*(canvasCoeff D*(a*V^2)*W*(ratio+1))*(a*V^2):=by gcongr <;> omega
      _ = _ :=by dsimp [U,canvasFactor,a,C,V,W];ring
  let Z:=canvasCoeff D*(m+1)*(2^k*(2*n+1))*ratio
  have hi:=Nat.mul_le_mul_left (H*h) heights
  have low:=Nat.mul_le_mul_left (H*2^m) loads
  have slab : canvasCoeff D*((m+1)*(2^k*(2*n+1))*(H*2^(m-l)))*w≤H*h*U+H*2^m*U:=by
    calc
      _ ≤ canvasCoeff D*((m+1)*(2^k*(2*n+1))*(H*2^(m-l)))*(ratio*h):=Nat.mul_le_mul_left _ word
      _ = Z*((H*2^(m-l))*h):=by dsimp [Z];ring
      _ ≤ Z*(H*h+16*H*2^m*b):=Nat.mul_le_mul_left Z layer
      _ ≤ _:=by dsimp [Z];nlinarith only [hi,low]
  have geom':2^m=S.groupCount i*S.radix:=geom
  rw [geom'] at slab
  nlinarith only [price,slab,dict]

end Hierarchy.DescentSixParty

end OAI

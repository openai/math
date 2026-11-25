import OAI.Hierarchy.DescentResetMiddleText
import OAI.Hierarchy.DescentResetSuffixScale

namespace OAI
/-! # Full bit charge from the recorded matrix to the saved original-coordinate channels -/
namespace Hierarchy.DescentGLPacked.BankImage.Dated
open DescentGLPacked DescentGLControlCode DescentGLNielsen DescentPackedWalsh
open DescentSIMDLookup DescentColonies.CandidateRAM ProtocolRAM
noncomputable section

theorem native_low (m b payload : ℕ) : lowBits m (2*b) payload=laneBits m payload b := by
  simp only [lowBits,laneBits,Nat.log2_eq_log_two,show 4*(2*b)=8*b by ring]

private theorem chart_bound (C : Chart) (H m l b h : ℕ)
    (bits : C.bits=chartBits H (m-l) l b) (old : l=laneBits m h b) (hb : 0<b) (area : 8*b≤h) :
    C.page*h≤2^(h/2)*h+2*(H*h+16*H*2^m*b+h) := by
  have fit:4*(2*b)≤h:=by omega
  have mono:chartBits H (m-l) l b≤chartBits H (m-l) l (2*b):=by
    unfold chartBits;apply max_le_max_left;gcongr <;> omega
  have bound:=footprint H m (2*b) h h 1 (by omega) fit (by omega)
  rw [native_low,←old] at bound
  dsimp only [Chart.page]
  rw [bits]
  apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) mono)).trans
  simpa only [one_mul,show 8*H*2^m*(2*b)=16*H*2^m*b by ring] using bound

/-- Multiplicities in the GL gate schedule are paid for explicitly even when the old
nonzero basis is the identity at many gate locations. -/
theorem middle_fee {w b D : ℕ} (C : Chart) (base solve fresh H hi lo payload ratio : ℕ)
    (counts : Bank) (pair : Fin D→Bank) (hb : 0<b) (hosts : 0<H) (dim : 2≤hi+lo)
    (old : lo=laneBits (hi+lo) payload b) (area : 8*b≤payload)
    (chart : C.bits=chartBits (((1+D)+(hi+lo))*H) hi lo b)
    (decode : (hi+lo)*(hi+lo)≤payload/2) (hardware : w≤ratio*payload)
    (A : ℕ) (axes : hi+lo≤A) (ports : D≤A) (prec : b≤A) :
    let proc:=middle C base solve fresh counts pair H hi lo w hb
    let ticks:=middleTime C base solve counts pair H hi lo w hb
    (ticks+7*DescentStaticWordColumn.names proc)*w≤
      100000000*ratio*(A+1)^5*(H*payload+H*2^(hi+lo)+2^(payload/2)*payload) := by
  let m:=hi+lo
  let L:=A+1
  let F:=(1+D)+m
  let G:=Count m
  let N:=H*2^hi
  let Q:=2^(payload/2)
  let T:=H*payload+H*2^m+Q*payload
  let P:=middle C base solve fresh counts pair H hi lo w hb
  let ticks:=middleTime C base solve counts pair H hi lo w hb
  have clock:ticks≤500*(1+G)*(1+m+F)*(1+keys m+2^hi+N+C.page):=middle_clock C base solve counts pair hb
  have text:DescentStaticWordColumn.names P≤4*ticks:=(middle_text C base solve fresh counts pair hb hosts dim).size
  have lpos:1≤L:=Nat.succ_pos _
  have fbound:F≤2*L:=by dsimp [L,F,m];omega
  have sq:m*m≤L*L:=Nat.mul_le_mul (axes.trans (Nat.le_succ _)) (axes.trans (Nat.le_succ _))
  have gp:G≤3*m*m:=length_le m
  have gbound:1+G≤4*L^2:=by dsimp [L] at *;nlinarith only [sq,gp,axes]
  have shape:1+m+F≤3*L:=by dsimp [L] at *;omega
  have core:=Nat.mul_le_mul gbound shape
  have cost:500*(1+G)*(1+m+F)≤6000*L^3:=by nlinarith only [core]
  have lp:4*(2*b)≤payload:=by omega
  have back:m-lo=hi:=by dsimp [m];omega
  have row:=charged H m (2*b) payload payload 1 (by omega) lp (by omega)
  dsimp only at row
  rw [native_low,←old,back,Nat.one_mul] at row
  have cells:b*(H*2^m)≤L*T:=Nat.mul_le_mul (prec.trans (Nat.le_succ _)) (by dsimp [T];omega)
  have Hunit:H*payload≤T:=by dsimp [T];omega
  have bcharge:N*payload≤17*L*T:=by
    change N*payload≤H*payload+8*H*2^m*(2*b) at row
    have het:=Nat.mul_le_mul_right T lpos
    nlinarith only [row,Hunit,cells,het]
  have cq:2^hi≤N:=Nat.le_mul_of_pos_left _ hosts
  have qle:keys m≤Q:=by
    unfold keys
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) decode
  have whole:1≤Q:=Nat.two_pow_pos _
  have low:payload≤T:=(Nat.le_mul_of_pos_left _ hosts).trans Hunit
  have qload:Q*payload≤T:=by dsimp [T];omega
  have chartCost:=chart_bound C (F*H) m lo b payload (by rwa [back]) old hb area
  change C.page*payload ≤ Q*payload+2*(F*H*payload+16*(F*H)*2^m*b+payload) at chartCost
  have rows2:F*(H*payload+16*H*2^m*b)≤34*L^2*T:=calc
    _ ≤ (2*L)*(17*L*T):=Nat.mul_le_mul fbound (by
      have het:=Nat.mul_le_mul_right T lpos
      nlinarith only [Hunit,cells,het])
    _ = _:=by ring
  have squares:1≤L^2:= by simpa using Nat.pow_le_pow_left lpos 2
  have lsmall:L≤L^2:=by nlinarith only [Nat.mul_le_mul_left L lpos]
  have Tsmall:=Nat.mul_le_mul_right T squares
  have lone:=Nat.mul_le_mul_right T lsmall
  have page:C.page*payload≤71*L^2*T:=by nlinarith only [chartCost,rows2,qload,low,Tsmall]
  have bank:(1+keys m+2^hi+N+C.page)*payload≤107*L^2*T:=by
    have q:=Nat.mul_le_mul_right payload qle
    have n:=Nat.mul_le_mul_right payload cq
    nlinarith only [low,q,qload,n,bcharge,page,Tsmall,lone]
  have clk: ticks*payload≤642000*L^5*T:=calc
    _ ≤ (500*(1+G)*(1+m+F))*((1+keys m+2^hi+N+C.page)*payload):=by rw [←Nat.mul_assoc];exact Nat.mul_le_mul_right _ clock
    _ ≤ (6000*L^3)*(107*L^2*T):=Nat.mul_le_mul cost bank
    _ = _:=by ring
  change (ticks+7*DescentStaticWordColumn.names P)*w≤_
  calc _≤(29*ticks)*(ratio*payload):=Nat.mul_le_mul (by omega) hardware
       _=29*ratio*(ticks*payload):=by ring
       _≤29*ratio*(642000*L^5*T):=Nat.mul_le_mul_left _ clk
       _≤_:=by dsimp only [L,T,Q,m];ring_nf;omega

end
end Hierarchy.DescentGLPacked.BankImage.Dated

end OAI

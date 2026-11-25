import OAI.Hierarchy.DescentResetMiddleFee
import OAI.Hierarchy.DescentResetEndpointTariff

namespace OAI
/-! # Pricing the actual old-coordinate and paid-flow GL transaction at a scheduled reset -/
namespace Hierarchy.DescentSixParty
open Filter DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh DescentPlainTerminal.Suffix
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.Dated DescentSIMDLookup ProtocolRAM
noncomputable section

def remixInvoice {D : ℕ} (P : StencilBook) (C : Chart) (base solve fresh : ℕ) (counts : Bank)
    (pair : Fin D→Bank) (h w : ℕ) (live : 0<P.b) :=
  let l:=laneBits P.m h P.b
  let proc:=middle C base solve fresh counts pair P.hosts P.high l w live
  let fee:=middleTime C base solve counts pair P.hosts P.high l w live
  (fee+7*DescentStaticWordColumn.names proc)*w

variable {F : Type} [Field F] (G : PoweredGadget F)

def remixFactor (ratio : ℕ) := 100000000*(ratio+1)

theorem remix_date_tariff (t f g reset τ B D n ratio saving : ℕ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop, ∀M i p w : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let P:=S.endpointBook k (tail τ J) i p f D h n
      let l:=laneBits P.m h P.b
      let unit:=remixFactor ratio*TerminalScale.scale J (5*stencilRate G t f g reset)
      ∀(C : Chart) (base solve fresh : ℕ) (counts : Bank) (pair : Fin D→Bank),
      i≤S.length→p≤h→2^h≤M→w≤ratio*h→
      C.bits=chartBits (((1+D)+P.m)*P.hosts) P.high l P.b→
      ∃positive : 0<P.b,remixInvoice P C base solve fresh counts pair h w positive≤
        S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+M/(2^J)^saving := by
  let κ:=stencilRate G t f g reset
  let K:=localCoefficient G t f g reset (quota t) τ
  let L:=100000000*ratio
  filter_upwards [stencil_capacity_at G t f g reset τ B (quota t) D n den,
    eventually_actual_width G t f g reset B (quota t) τ,dyadic_log_room (2*K^2) 4,
    global_control_shared L 1 (5*κ) 1 saving] with h cap width keys paid
  intro M i p w J S k P l unit C base solve fresh counts pair age pFit ambient machine chart
  let a:=stencilCapacity k P.b D n
  let T:=2^(κ*(J+1))
  have scalea:a+1≤T:=cap M i p age pFit
  have ageFit:J≤Nat.log 2 h:=Nat.div_le_self ..
  have tailBudget:tail τ J≤τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ ageFit).trans (by nlinarith))
  have bnd:P.b≤K*(Nat.log 2 h+1)^2:=actual_width G t J f g reset M (tail τ J) i h p (quota t) τ pFit ageFit tailBudget age
  have small:8*P.b≤h/2:=(width M (tail τ J) i p pFit tailBudget age).1
  have hb:0<P.b:=by change 0<DescentWalshPrecision.bits _ _ _ _;unfold DescentWalshPrecision.bits;omega
  have mpos:2≤P.m:=by
    change 2≤S.groupWidth k (tail τ J) i+k
    have wide : 2 ≤ k := (show 2 ≤ 8 by decide).trans
      ((Nat.le_add_left 8 _).trans (Nat.le_add_right _ _))
    exact wide.trans (Nat.le_add_left ..)
  have m_b:P.m≤P.b:=by change _≤DescentWalshPrecision.bits P.m _ _ _;unfold DescentWalshPrecision.bits;omega
  have keyFit:P.m*P.m≤h/2:=by
    have z:=Nat.pow_le_pow_left (m_b.trans bnd) 2
    rw [mul_pow,←pow_mul] at z
    apply (Nat.le_div_iff_mul_le (by decide)).2
    calc
      _ = P.m^2*2 := by ring
      _ ≤ (K^2*(Nat.log 2 h+1)^4)*2 := Nat.mul_le_mul_right _ z
      _ = _ := by ring
      _ ≤ _ := keys
  have rad:0<S.radix:=Nat.two_pow_pos _
  have host:0<P.hosts:=by
    have old:0<M:=(Nat.two_pow_pos h).trans_le ambient
    change 0<M*(2^S.hostGain*S.radix)^i;positivity
  have eqdim:P.high+l=P.m:=Nat.sub_add_cancel (Nat.min_le_left ..)
  have many:P.b+D+n+7≤a:=by
    exact (Nat.le_mul_of_pos_left _ (by decide : 0<8)).trans (Nat.le_add_left ..)
  have price:=middle_fee C base solve fresh P.hosts P.high l h ratio counts pair hb host
    (by rwa [eqdim]) (by rw [eqdim]) (by omega) (by rw [eqdim];exact chart) (by rwa [eqdim]) machine
    a (by rw [eqdim];omega) (by omega) (by omega)
  have action:remixInvoice P C base solve fresh counts pair h w hb≤
      L*(a+1)^5*(P.hosts*h+P.hosts*2^P.m+2^(h/2)*h):=by
    simpa only [remixInvoice,L,eqdim,l] using price
  have locals:(a+1)^5≤T^5:=Nat.pow_le_pow_left scalea 5
  have shape:TerminalScale.scale J (5*κ)=T^5:=by unfold TerminalScale.scale;dsimp [T];rw [←pow_mul];congr 1;ring
  have coef:L*(a+1)^5≤unit:=by
    change _≤remixFactor ratio*TerminalScale.scale J (5*κ)
    rw [shape];exact Nat.mul_le_mul (by dsimp [L,remixFactor];omega) locals
  have res:=paid J (5*κ*(J+1)) M ageFit (by simp) ambient
  have teeth:2^(5*κ*(J+1))=T^5:=shape
  rw [teeth,pow_one] at res
  have rhs:L*(a+1)^5*(2^(h/2)*h)≤M/(2^J)^saving:=calc
    _ = (L*h*(a+1)^5)*2^(h/2):=by ring
    _ ≤ (L*(h+1)*T^5)*2^(h/2):=by gcongr; omega
    _ ≤ _:=res
  have geo:2^P.m=S.groupCount i*S.radix:=by
    change 2^(S.groupWidth k (tail τ J) i+k)=_
    rw [pow_add,S.group_power (tail:=tail τ J) (k:=k) rfl rfl]
    rfl
  refine ⟨hb,?_⟩
  have high:=Nat.mul_le_mul_left (P.hosts*h) coef
  have low:=Nat.mul_le_mul_left (P.hosts*2^P.m) coef
  change _≤P.hosts*h*unit+P.hosts*(S.groupCount i*S.radix)*unit+_
  rw [←geo]
  have sum_bound (coef u x y z tail : ℕ) (c : coef ≤ u) (r : coef*z ≤ tail) :
      coef*(x+y+z) ≤ x*u+y*u+tail := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm coef x, Nat.mul_comm coef y]
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left x c) (Nat.mul_le_mul_left y c)) r
  exact action.trans (sum_bound _ _ _ _ _ _ coef rhs)

end
end Hierarchy.DescentSixParty

end OAI

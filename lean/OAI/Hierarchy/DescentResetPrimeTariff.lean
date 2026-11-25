import OAI.Hierarchy.DescentPhysicalResetReceipt
import OAI.Hierarchy.DescentCanvasDateBill
import OAI.Hierarchy.DescentMeasuredLaneRoom

namespace OAI
/-! The real Canvas and estimator instruction bill at the address supplied by the ingress. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh DescentSIMDLookup
open DescentSixParty.PackedFlow.Canvas DescentStaticWordColumn ProtocolRAM Filter
noncomputable section
variable (a : PhysicalReset)

def primeCanvas (floor : ℕ) (src count : Bank) (degree : ℕ) : Setup.Date a.k a.c :=
  ⟨a.previousToken,a.previousRoster,src,count,floor,a.depthCut,a.fullBudget,a.classBound,a.grain,
    degree,(a.estimator floor).start⟩

theorem prime_invoice (floor : ℕ) (src count : Bank) (R degree w : ℕ) :
    let E:=a.estimator floor
    (a.primeTicks floor R degree w+7*names (a.prime floor src count R degree w))*w =
      (a.primeCanvas floor src count degree).fee a.hosts a.ports R a.high a.low a.bits a.short a.lanes w+
      (E.installedTicks+7*names (E.installedCPU w))*w := by
  intro E
  let X:=a.primeCanvas floor src count degree
  have program : a.prime floor src count R degree w=
      (X.cpu a.hosts a.ports R a.high a.low a.bits a.short a.lanes w).seq (E.installedCPU w) := rfl
  rw [program,names_seq]
  let setupTicks:=Setup.ticks a.hosts a.ports a.high a.low a.bits a.short a.lanes floor a.depthCut a.fullBudget a.classBound a.k R
  let prepareTicks:=(a.chart floor).prepareTicks (a.flow floor) a.k degree R a.lanes w
  let code:=names (X.cpu a.hosts a.ports R a.high a.low a.bits a.short a.lanes w)
  let estimatorCode:=names (E.installedCPU w)
  change ((setupTicks+prepareTicks+E.installedTicks)+7*(code+estimatorCode))*w=
    (setupTicks+prepareTicks+7*code)*w+(E.installedTicks+7*estimatorCode)*w
  ring

variable {F : Type} [Field F] (G : PoweredGadget F)

def primeUnit (t f g reset τ B D ratio J : ℕ) :=
  scale J (canvasRate G t f g reset)*(canvasFactor G t f g reset τ B (quota t) D ratio*(tail τ J+1)^4)+
  estimatorFactor G t f g reset τ B (quota t) D ratio*(tail τ J+1)^6

theorem prime_date_tariff (t f g reset τ B D ratio saving : ℕ) (tailPos : 0<τ) (den : 0<B)
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B) :
    ∀ᶠ h : ℕ in atTop,∀M i p w e n s : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(tape : List ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank) (out : ResetOutput) (floor : ℕ) (src count : Bank),
      let a:=fromCalendar S k (tail τ J) i G.b p f D h e n s tape addr roster out
      i≤S.length→p ≤ h→2^h≤M→w ≤ ratio*h→(tape.take i).prod*256≤2^(8+(S.capGain-(G.b+3))*i)→
      a.PrimeRoom floor src count (S.groupCount i) D w→
      (a.primeTicks floor (S.groupCount i) D w+7*names (a.prime floor src count (S.groupCount i) D w))*w ≤
        S.hostSize i*h*primeUnit G t f g reset τ B D ratio J+
        S.hostSize i*(S.groupCount i*S.radix)*primeUnit G t f g reset τ B D ratio J+2*(M/(2^J)^saving) := by
  filter_upwards [canvas_date_tariff G t f g reset τ B (quota t) D ratio saving tailPos den,
    estimator_date_tariff G t f g reset τ B (quota t) D ratio saving tailPos den,
    measured_lane_room G t f g reset τ B (quota t) cutoff] with h canvas estimator lanes
  intro M i p w e n s J S k tape addr roster out floor src count a age payload ambient machine cap ready
  let X:=a.primeCanvas floor src count D
  let E:=a.estimator floor
  let m:=S.groupWidth k (tail τ J) i+k
  let b:=S.localWalshBits p m f (quota t)
  let low:=laneBits m h b
  have dim:E.dim=m:=calendar_dim S k (tail τ J) i G.b p f D h e n s tape addr roster out
  have rows:E.hosts=S.hostSize i*(m+1+D):=by
    change S.hostSize i*(E.dim+1+D)=_
    rw [dim]
  have limbs : 2^low=a.lanes*2^k := by
    have fit:k ≤ low:=lanes M i p age payload
    change 2^low=2^(low-k)*2^k
    rw [←Nat.pow_add,Nat.sub_add_cancel fit]
  have front:=canvas M i p w ((tape.take i).prod*256) a.lanes X age payload ambient machine cap limbs
  have hostFit:E.hosts≤2^w:=ready.fit.hostRows.1.trans ready.fit.depth.2.1.le
  have digitFit:b ≤ w+1:=
    ((Nat.le_mul_of_pos_right E.precision (Nat.two_pow_pos _)).trans
      ((Nat.le_add_left ..).trans ready.fit.lookup)).trans (Nat.le_succ _)
  have gain:E.gainBits ≤ b:=DescentWalshPrecision.gain_le m f (quota t) (S.censusBits p)
  have back:=estimator M i p E w age payload ambient dim rfl rows rfl rfl gain machine hostFit digitFit
  rw [prime_invoice]
  change X.fee _ _ _ _ _ _ _ _ w+(E.installedTicks+7*names (E.installedCPU w))*w≤_
  unfold primeUnit
  exact (Nat.add_le_add front back).trans_eq (by ring)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

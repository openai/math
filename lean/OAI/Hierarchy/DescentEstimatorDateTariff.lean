import OAI.Hierarchy.DescentEstimatorCommonBill
import OAI.Hierarchy.DescentResetWalshScale
import OAI.Hierarchy.DescentStageLedger

namespace OAI
/-! # The original paid reset clock on its padded date of the physical calendar -/
namespace Hierarchy.DescentSixParty
open Filter DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh
open DescentPackedWalsh.EstimatorArena
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The same fixed polynomial coefficient pays both original site words and packed group fields.
Its degree is six because the canvas multiplicity, dimension and precision are each quadratic
in the chronological height. -/
def estimatorFactor (t f g reset τ B quota D ratio : ℕ) :=
  let c:=localCoefficient G t f g reset quota τ*(2*B+1)^2+1
  115*100000*(ratio+1)*(c+D)*c*c

set_option maxHeartbeats 2000000 in
theorem estimator_date_tariff (t f g reset τ B quota D ratio saving : ℕ) (tailPos : 0<τ)
    (den : 0<B) :
    ∀ᶠ h : ℕ in atTop,∀M i p : ℕ, ∀(E : EstimatorArena) (w : ℕ),
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let m:=S.groupWidth k (tail τ J) i+k
      let b:=S.localWalshBits p m f quota
      let unit:=estimatorFactor G t f g reset τ B quota D ratio*(tail τ J+1)^6
      i≤S.length → p≤h → 2^h≤M →
      E.dim=m → E.precision=b → E.hosts=S.hostSize i*(m+1+D) → E.payload=h →
      E.low=laneBits m h b → E.gainBits≤b → w≤ratio*h → E.hosts≤2^w → b≤w+1 →
      (E.installedTicks+7*DescentStaticWordColumn.names (E.installedCPU w))*w ≤
        S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+M/(2^J)^saving := by
  let C:=localCoefficient G t f g reset quota τ
  let c:=C*(2*B+1)^2+1
  let L:=C+ratio+2
  filter_upwards [eventually_actual_width G t f g reset B quota τ,
    common_funded 1 L saving c,dyadic_log_room C 2] with h width common hroom
  intro M i p E w
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let m:=S.groupWidth k (tail τ J) i+k
  let b:=S.localWalshBits p m f quota
  let V:=tail τ J+1
  let U:=estimatorFactor G t f g reset τ B quota D ratio*V^6
  dsimp only
  intro age pFit ambient dim prec rows pay lanes gain word fits dec
  change (E.installedTicks+7*DescentStaticWordColumn.names (E.installedCPU w))*w≤
    S.hostSize i*h*U+S.hostSize i*(S.groupCount i*S.radix)*U+M/(2^J)^saving
  have jL : J≤Nat.log 2 h:=Nat.div_le_self ..
  have span : tail τ J≤τ*(Nat.log 2 h+1)^2:=by
    exact Nat.mul_le_mul_left _ ((Nat.succ_le_succ jL).trans (by nlinarith))
  have small : 8*b≤h/2:=(width M (tail τ J) i p pFit span age).1
  have price:= (E.installed_price w ratio (by simpa only [pay] using word) fits (by simpa only [prec] using dec)
    (by simpa only [dim,pay,prec] using lanes.symm) (by simpa only [prec,pay] using small)
    (by simpa only [prec] using gain)).2
  have actual : b≤C*(Nat.log 2 h+1)^2 := actual_width G t J f g reset M (tail τ J) i h p quota τ pFit jL span age
  have hbl : b≤h:=actual.trans hroom
  have m_le : m≤b:=by
    change m≤DescentWalshPrecision.bits m f quota (S.censusBits p)
    unfold DescentWalshPrecision.bits
    omega
  have floor : Nat.log 2 h+1≤(2*B+1)*(J+1):=by
    have rem:=Nat.mod_lt (Nat.log 2 h) (show 0<2*B by omega)
    have eqn:=Nat.mod_add_div (Nat.log 2 h) (2*B)
    change Nat.log 2 h%(2*B)+2*B*J=Nat.log 2 h at eqn
    nlinarith only [eqn,rem]
  have quarters : 0<(J+1)^2:=by positivity
  have smallAge : b+1≤c*(J+1)^2:=by
    have a:=Nat.mul_le_mul_left C (Nat.pow_le_pow_left floor 2)
    rw [mul_pow] at a
    dsimp [c]
    nlinarith only [actual,a,quarters]
  have stamp : J+1≤V:=by
    change J+1≤τ*(J+1)+1
    have s:=Nat.mul_le_mul_right (J+1) tailPos
    omega
  have cb : b+1≤c*V^2:=smallAge.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left stamp 2))
  have md : m+1≤c*V^2:= (Nat.succ_le_succ m_le).trans cb
  have lo : m+1+D≤(c+D)*V^2:=by
    have v : 0<V^2:=by dsimp [V];positivity
    have extra:=Nat.le_mul_of_pos_right D v
    rw [Nat.add_mul]
    omega
  have scale : 0<c*V^2:=by dsimp [c,V];positivity
  have units:=local_units m b ratio
  have high : 115*((m+1+D)*hostUnit m ratio)≤U:=by
    apply (Nat.mul_le_mul_left 115 (Nat.mul_le_mul lo (units.1.trans
      (Nat.mul_le_mul_left _ md)))).trans
    dsimp [U,estimatorFactor]
    change 115*((c+D)*V^2*(5000*(ratio+1)*(c*V^2)))≤115*100000*(ratio+1)*(c+D)*c*c*V^6
    calc
      _ ≤ (115*((c+D)*V^2*(5000*(ratio+1)*(c*V^2))))*(c*V^2):=Nat.le_mul_of_pos_right _ scale
      _ ≤ _ := by nlinarith only [Nat.zero_le ((ratio+1)*(c+D)*c*c*V^6)]
  have low : 115*((m+1+D)*fieldUnit m b ratio)≤U:=by
    apply (Nat.mul_le_mul_left 115 (Nat.mul_le_mul lo (units.2.trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ md) cb)))).trans
    dsimp [U,estimatorFactor]
    change 115*((c+D)*V^2*(100000*(ratio+1)*(c*V^2)*(c*V^2)))≤115*100000*(ratio+1)*(c+D)*c*c*V^6
    exact le_of_eq (by ring)
  have dimRead : E.dim = m := dim
  have precisionRead : E.precision = b := prec
  have dimAge : E.dim ≤ c*(J+1)^2 := dimRead.le.trans (m_le.trans ((Nat.le_succ b).trans smallAge))
  have positiveLimit : 0<L := by dsimp [L]; omega
  have ratioLimit : ratio ≤ L := by dsimp [L]; omega
  have payloadRoom : h ≤ L*(h+1) :=
    (Nat.le_succ h).trans (Nat.le_mul_of_pos_left _ positiveLimit)
  have wordRoom : w ≤ L*(h+1) := word.trans (Nat.mul_le_mul ratioLimit (Nat.le_succ h))
  have ratioRoom : ratio ≤ L*(h+1) := ratioLimit.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos h))
  have depthRoom : E.plan.depth ≤ L*(h+1) := by
    change Nat.clog 2 E.hosts ≤ _
    exact (Nat.clog_le_of_le_pow fits).trans wordRoom
  have cc := common J M jL ambient E w ratio pay dimAge
    (dimRead.le.trans (m_le.trans (hbl.trans payloadRoom)))
    (precisionRead.le.trans (hbl.trans payloadRoom)) payloadRoom wordRoom ratioRoom depthRoom
  have geom : 2^m=S.groupCount i*S.radix:=by
    change 2^(S.groupWidth k (tail τ J) i+k)=_
    rw [pow_add,S.group_power (tail:=tail τ J) (k:=k) rfl rfl]
    rfl
  have rowRead : E.hosts = S.hostSize i*(m+1+D) := rows
  rw [dimRead,precisionRead,rowRead,pay,geom] at price
  simp only [Nat.one_mul] at cc
  have hiBill:=Nat.mul_le_mul_left (S.hostSize i*h) high
  have loBill:=Nat.mul_le_mul_left (S.hostSize i*(S.groupCount i*S.radix)) low
  apply price.trans
  calc
    _ = S.hostSize i*h*(115*((m+1+D)*hostUnit m ratio)) +
        (S.hostSize i*(S.groupCount i*S.radix))*(115*((m+1+D)*fieldUnit m b ratio)) +
        (115*E.commonBill w ratio+(109+7*E.controlNames)*w) := by ring
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add hiBill loBill) cc

/-- The sum uses the actual installed programs at the reset dates, with zero fee
at all remaining ordinary dates. The available common site at every age also pays its
once-only controller and literal-table installation. -/
theorem estimator_calendar (t f g reset τ B quota D ratio e : ℕ) (tailPos : 0<τ) (den : 0<B)
    (tailFit : 0+6+3+(e+5)≤τ)
    (timeFit : 2*((2+hostRate t reset*(t+1)+0+(6+1)+1)+5+e)≤B) :
    ∀ᶠ h : ℕ in atTop, ∀M q p w : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀arena : Fin (S.length+1)→Option EstimatorArena,
      0<q → q≤ scale J e → h≤32*(q*p) → p≤h → 2^h≤M → w≤ratio*h →
      (∀i E,arena i=some E →
        let m:=S.groupWidth k (tail τ J) i.val+k
        let b:=S.localWalshBits p m f quota
        E.dim=m ∧ E.precision=b ∧ E.hosts=S.hostSize i.val*(m+1+D) ∧ E.payload=h ∧
        E.low=laneBits m h b ∧ E.gainBits≤b ∧ E.hosts≤2^w ∧ b≤w+1) →
      (∑i, (arena i).elim 0 (fun E=>(E.installedTicks+7*DescentStaticWordColumn.names
        (E.installedCPU w))*w))*2^J≤2*(M*(S.copies*p)) := by
  let C:=estimatorFactor G t f g reset τ B quota D ratio
  filter_upwards [estimator_date_tariff G t f g reset τ B quota D ratio 0 tailPos den,
    calibration_at G t f g reset 0 0 e (C+1) 6 τ tailFit B den timeFit,
    eventually_ge_atTop 1] with h date ledger hpos
  intro M q p w
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  dsimp only
  intro arena qpos scaleQ bought fit ambient word config
  let u:=C*(tail τ J+1)^6
  have short : u+1≤ scale J 0*((C+1)*(tail τ J+1)^6):=by
    have pos : 0<(tail τ J+1)^6:=by positivity
    simp only [scale,Nat.zero_mul,pow_zero,Nat.one_mul]
    dsimp [u];rw [Nat.add_mul,Nat.one_mul];omega
  apply ledger M q p (u+1) (u+1) qpos scaleQ bought short short
    (fun j => (arena j).elim 0 (fun E => (E.installedTicks +
      7*DescentStaticWordColumn.names (E.installedCPU w))*w))
  intro i
  cases pick : arena i with
  | none=>simp only [Option.elim_none];omega
  | some E=>
    obtain ⟨dim,prec,rows,pay,lanes,gain,fits,dec⟩:=config i E pick
    have price:=date M i.val p E w (Nat.le_of_lt_succ i.isLt : i.val≤S.length) fit ambient
      dim prec rows pay lanes gain word fits dec
    have pop : M≤S.hostSize i.val:=by
      have pos : 0<S.radix:=by change 0<2^_;positivity
      change M≤M*(2^S.hostGain*S.radix)^i.val
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have minHost : M≤S.hostSize i.val*h:=pop.trans (Nat.le_mul_of_pos_right _ hpos)
    simp only [pow_zero,Nat.div_one] at price
    simp only [Option.elim_some]
    change _≤S.hostSize i.val*h*(u+1)+S.hostSize i.val*(S.groupCount i.val*S.radix)*(u+1)
    change _≤S.hostSize i.val*h*u+S.hostSize i.val*(S.groupCount i.val*S.radix)*u+M at price
    nlinarith only [price,minHost,Nat.zero_le (S.hostSize i.val*(S.groupCount i.val*S.radix))]

end Hierarchy.DescentSixParty

end OAI

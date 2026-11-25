import OAI.Hierarchy.DescentTerminalPublicRows
import OAI.Hierarchy.DescentDatedAddressRate
import OAI.Hierarchy.DescentGlobalControlRoom
import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentNativeSocketScale

namespace OAI
/-! # The true purchased terminal rows and the full exterior array fit one address exponent -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler TerminalScale DescentDatedAddressBook DescentColonies
open DescentTerminalGraphVolume DescentResetInvoice Catalyst
open ThreeFlat.Routing Filter
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F)
variable (t f g reset τ B n degree C : ℕ)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg M:arg => stageNumbers G t (J_ h) f g reset M (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "W_" h:arg M:arg => NativeBranch.binLimit (k:=k_ h) (S_ h M)
local notation "q_" h:arg M:arg => (2^Nat.clog 2 (NativeBranch.localLimit G (S_ h M)))*(G.b^(t*(J_ h))*G.b)
local notation "p_" h:arg M:arg => W_ h M*(h/(16*(q_ h M*W_ h M)))
local notation "bill" => ⌈258*reentryRate degree C+reentryExteriorRate degree C 256 (GroupStage.depthBound (atRound t) n f g)⌉₊

private def wireLimit (rate copies h M T : ℕ) :=(1+2*rate)*(copies*h)*(M+T*M)

private theorem paid_grain (h M : ℕ) :
    q_ h M * p_ h M≤h ∧ (S_ h M).firstWidth G.b (p_ h M)≤h :=by
  let q:=q_ h M
  let b:=W_ h M
  have packed : q*(b*(h/(16*(q*b))))≤h:=by
    calc
      _ = (h/(16*(q*b)))*(q*b) := by ac_rfl
      _ ≤ (h/(16*(q*b)))*(16*(q*b)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by decide))
      _ ≤ h := Nat.div_mul_le_self ..
  refine ⟨packed,le_trans ?_ packed⟩
  let p:=p_ h M
  let U:=G.b^(t*(J_ h))*G.b
  have first : (S_ h M).firstWidth G.b p=p*U:= by
    simp only [AtomSchedule.firstWidth,AtomSchedule.grainAt,AtomSchedule.ordinaryDone,Nat.zero_div,Nat.sub_zero,
      Nat.sub_self,stageNumbers,Nat.mul_assoc,U]
  change (S_ h M).firstWidth G.b p≤q*p
  rw [first,Nat.mul_comm p]
  exact Nat.mul_le_mul_right p (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))

private theorem scale_rows :
    ∀ᶠ h : ℕ in atTop,∀M,
      (S_ h M).copies≤2^h ∧ (S_ h M).hostSize (S_ h M).length≤M*2^h ∧
      (S_ h M).epochPower≤2^h ∧ W_ h M≤3*2^h+6 :=by
  let c:=hostRate t reset
  let K:=1+(c+capRate G t g)*(t+1)+8+cutRate t f g
  let limit:=τ+(c+K)*(t+2)
  filter_upwards [dyadic_log_room limit 2] with h short
  intro M
  let j:=J_ h
  let k:=k_ h
  have first : k≤K*(j+1):=groupBits_linear ..
  have count : (t+1)*j+1≤(t+2)*(j+1):=by nlinarith
  have width : c+k≤(c+K)*(j+1):=by nlinarith only [first,Nat.zero_le (c*j)]
  have product:=Nat.mul_le_mul width count
  have total : τ*(j+1)+(c+k)*((t+1)*j+1)≤limit*(j+1)^2:=by
    dsimp only [limit];nlinarith only [product,Nat.zero_le (τ*j*(j+1))]
  have room : limit*(j+1)^2≤h:= (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.div_le_self ..) 1) 2)).trans short
  have height : j≤h:=(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have replica : (S_ h M).copies≤2^h:=by
    change 2^(τ*(j+1))*(2^k)^((t+1)*j+1)≤2^h
    rw [←pow_mul,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_left k c)) _).trans (total.trans room)
  refine ⟨replica,?_,Nat.pow_le_pow_right (by decide) height,?_⟩
  · change M*(2^c*2^k)^((t+1)*j)≤M*2^h
    rw [←pow_add,←pow_mul]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by decide)
    exact (Nat.mul_le_mul_left _ (Nat.le_succ _)).trans ((Nat.le_add_left ..).trans (total.trans room))
  · change 3*((S_ h M).groupCount (S_ h M).length*2^k)+6≤_
    have group : (S_ h M).groupCount (S_ h M).length≤(S_ h M).groupCount 0:=by
      simp only [AtomSchedule.groupCount,Nat.sub_self,pow_zero,Nat.mul_one,Nat.sub_zero]
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.two_pow_pos _))
    have init:=Fintype.card_congr ((S_ h M).initialDigits (k:=k) rfl)
    have mul : (S_ h M).groupCount 0*2^k=(S_ h M).copies:=by simpa using init.symm
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 ((Nat.mul_le_mul_right _ group).trans (mul.le.trans replica))) _

local notation "jb" b:arg h:arg => Nat.log 2 h/(2*b)
local notation "kb" b:arg h:arg => groupBits t (jb b h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "sched" u:arg b:arg h:arg m:arg => stageNumbers G t (jb b h) f g reset m (tail u (jb b h))
local notation "Wb" u:arg b:arg h:arg m:arg => NativeBranch.binLimit (k:=kb b h) (sched u b h m)
local notation "qb" u:arg b:arg h:arg m:arg =>
  (2^Nat.clog 2 (NativeBranch.localLimit G (sched u b h m)))*(G.b^(t*(jb b h))*G.b)
local notation "pb" u:arg b:arg h:arg m:arg => Wb u b h m*(h/(16*(qb u b h m*Wb u b h m)))

/-- The address exponent is chosen before the two calibration parameters. -/
theorem terminal_public_row_rates :
    ∃L : ℕ,∀u b,∀ᶠ h : ℕ in atTop,∀ M,2^h≤M→M≤(2^h)^2→
    ∀{cp pins : ℕ} (X : Approximation F cp pins) (j rest : ℕ),10*(X.size+1)≤M→
    j+(j+rest)=(sched u b h M).groupWidth (kb b h) (tail u (jb b h)) 0+(kb b h)→
    terminalRawRows X G (sched u b h M) (pb u b h M) (qb u b h M) n degree C f g ≤ 2^(L*h) ∧
    terminalPool X G (sched u b h M) (pb u b h M) (qb u b h M) (Wb u b h M) n degree C f g + Wb u b h M ≤ 2^(L*h) ∧
    Fintype.card (Port pins X.width)*2^(j+rest)≤2^(L*h) :=by
  have unit : Bounded (ι:=fun _=>Unit) (fun h _=>2^h):=⟨1,Eventually.of_forall (by simp)⟩
  have nodes:=unit.pow 2
  have old:=unit.mul unit
  have wireBound:=((Bounded.const (1+2*bill)).mul old).mul (nodes.add (unit.mul nodes))
  have exterior:=old.mul nodes
  have bin:=((Bounded.const 3).mul unit).add (Bounded.const 6)
  have boxes := ((Bounded.const 2).mul (((Bounded.const 3).mul (((Bounded.const 2).mul wireBound).add exterior)).add
      ((nodes.mul unit).mul (Bounded.const 6)))).add bin
  obtain ⟨L,all⟩:=((wireBound.add unit).add (boxes.add bin)).add (nodes.mul unit)
  refine ⟨L,?_⟩
  intro u b
  filter_upwards [all,scale_rows G t f g reset u b] with h at_h dims
  intro M _ upper cp pins X j rest fit split
  have ticks : 2^((sched u b h M).groupWidth (kb b h) (tail u (jb b h)) 0+kb b h)=(sched u b h M).copies:=by
    rw [pow_add,(sched u b h M).group_power rfl rfl 0]
    have card:=Fintype.card_congr ((sched u b h M).initialDigits (k:=kb b h) rfl)
    simpa using card.symm
  let S:=sched u b h M
  let p:=pb u b h M
  let q:=qb u b h M
  let WW:=Wb u b h M
  let E:=Fintype.card (Port pins X.width)
  let wire:=wireLimit bill S.copies h M S.epochPower
  let upperBox:=2*(3*(2*wire+S.copies*h*M)+S.hostSize S.length*6)+WW
  have ⟨replicas,hosts,epoch,bin⟩:=dims M
  let X₀:=2^h
  have hh : h≤X₀:=Nat.lt_two_pow_self.le
  have wires : wire≤wireLimit (bill) X₀ X₀ (X₀^2) X₀:=by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul replicas hh))
      (Nat.add_le_add upper (Nat.mul_le_mul epoch upper))
  have clips : upperBox ≤ 2*(3*(2*wireLimit bill X₀ X₀ (X₀^2) X₀+(X₀*X₀)*(X₀^2))+
       (X₀^2*X₀)*6)+(3*X₀+6):=by
    have maxHosts:=hosts.trans (Nat.mul_le_mul_right X₀ upper)
    have span := Nat.add_le_add (Nat.mul_le_mul_left 2 wires) (Nat.mul_le_mul (Nat.mul_le_mul replicas hh) upper)
    exact Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.add_le_add (Nat.mul_le_mul_left 3 span)
      (Nat.mul_le_mul_right 6 maxHosts))) bin
  have allRows : ((wire+h)+(upperBox+WW))+M*S.copies ≤2^(L*h):=by
    apply le_trans _ (at_h ())
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add wires hh) (Nat.add_le_add clips bin)) (Nat.mul_le_mul upper replicas)
  have pin : E≤M:=by
    have inside : E≤X.size:=Nat.le_add_left ..
    omega
  have ⟨qp,fw⟩:=paid_grain G t f g reset u b h M
  have d : S.copies*S.firstWidth G.b p≤S.copies*h:=Nat.mul_le_mul_left _ fw
  have wireRead : terminalWireBudget X G S p n degree C f g≤wire:=by
    unfold terminalWireBudget integralFrontier
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ d)
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ pin) _))
  have raw : terminalRawRows X G S p q n degree C f g≤wire+h:=by
    unfold terminalRawRows poolBatchCount
    exact (Nat.div_le_self ..).trans ((Nat.sub_le ..).trans (Nat.add_le_add wireRead qp))
  have pool : terminalPool X G S p q WW n degree C f g≤upperBox:=by
    unfold terminalPool rowBudget
    apply (Nat.div_mul_le_self ..).trans
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ (Nat.add_le_add
      (Nat.mul_le_mul_left 2 wireRead) (Nat.mul_le_mul d pin)))
  have outside : E*2^(j+rest)≤M*S.copies:=by
    apply Nat.mul_le_mul pin
    rw [←ticks,←split]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)
  have left : wire+h≤(wire+h)+(upperBox+WW):=Nat.le_add_right ..
  have right : upperBox+WW≤(wire+h)+(upperBox+WW):=Nat.le_add_left ..
  have joined : (wire+h)+(upperBox+WW)≤2^(L*h):=(Nat.le_add_right ..).trans allRows
  exact ⟨raw.trans (left.trans joined),(Nat.add_le_add_right pool WW).trans (right.trans joined),
    outside.trans ((Nat.le_add_left ..).trans allRows)⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

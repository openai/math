import OAI.Hierarchy.DescentNamedEarnedCalendarRates
import OAI.Hierarchy.DescentNamedPreflightAt
import OAI.Hierarchy.DescentDatedTerminalAperture

namespace OAI
/-! # Address and scalar room for the original dated preflight and its two purchased row banks -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open CatalystSubstitution CorrectionBatch DescentKernelHistory
open DescentTerminalGraphVolume DescentDatedAddressBook Catalyst ThreeFlat.Routing Filter
noncomputable section
set_option quotPrecheck false
open DescentTerminalCompiledPrefix DescentTerminalPreflightSpace DescentTerminalLocalPortBook ProtocolRAM
open AddressPlan
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B n depth C : ℕ)

local notation "src_" h:arg => ShellSource F h
local notation "age_" h:arg => Nat.log 2 h/(2*B)
local notation "st_" h:arg x:arg => stageNumbers G t (age_ h) f g reset (ShellSource.sites x) (tail τ (age_ h))
local notation "kb_" h:arg => groupBits t (age_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "bw_" h:arg x:arg => NativeBranch.binLimit (k:=kb_ h) (st_ h x)
local notation "j_" h:arg x:arg => Nat.clog 2 (NativeBranch.localLimit G (st_ h x))
local notation "unit_" h:arg => G.b^(t*(age_ h))*G.b
local notation "q_" h:arg x:arg => 2^(j_ h x)*(unit_ h)
local notation "p_" h:arg x:arg => (bw_ h x)*(h/(16*((q_ h x)*(bw_ h x))))
local notation "pins_" x:arg => Fintype.card (Port (ShellSource.ports x) (ShellSource.X x).width)
local notation "normal_" h:arg x:arg => terminalWireBudget (ShellSource.X x) G (st_ h x) (p_ h x) n depth C f g
local notation "pool_" h:arg x:arg => terminalPool (ShellSource.X x) G (st_ h x) (p_ h x) (q_ h x) (bw_ h x) n depth C f g
local notation "raw_" h:arg x:arg => terminalRawRows (ShellSource.X x) G (st_ h x) (p_ h x) (q_ h x) n depth C f g
local notation "dim_" h:arg x:arg => (st_ h x).groupWidth (kb_ h) (tail τ (age_ h)) 0+kb_ h
local notation "pub_" h:arg x:arg => (pins_ x)*2^((j_ h x)+((dim_ h x)-2*(j_ h x)))


variable (op : RotorSpec) (drift : ℕ)

local notation "invoice" => PreflightCalendar.scanExponent G t f g reset
local notation "vshape" h:arg x:arg => Branch.geometryFormat G (st_ h x) (kb_ h) g (p_ h x) (tail τ (age_ h))
  (PreflightCalendar.publicSlots G (st_ h x)) drift op (pool_ h x) (pool_ h x)

def earnedPreflight {h : ℕ} (x : ShellSource F h) :=
  Branch.preflightSpec x.X G (st_ h x) (kb_ h) g (p_ h x) (tail τ (age_ h)) (vshape h x)

local notation "issued" x:arg => earnedPreflight G t f g reset τ B n depth C op drift x

/-- Existence of the original selected itinerary and its strictly positive calibrated grain. -/
def IssuedPreflightAt {h : ℕ} (x : ShellSource F h) : Prop :=
  let S:=st_ h x
  let p:=p_ h x
  let k:=kb_ h
  let s:=S.firstWidth G.b p
  let wire:=(S.epochPower:ℝ)^S.priceExponent
  let q':=(1/((s:ℝ)*(wire:ℝ)):ℝ)
  let ε':=(((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
  let u:=q'*(wire:ℝ)
  0<p ∧ ∃(he : 0≤ε') (hu : 0≤u) (radix : S.radix=2^k)
    (r : Epochs G hu he (h:=depth) (C:=C) (Ht:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial x.X S.copies s (S.groupCount 0) k (S.initialDigits radix)))
    (c : (Epochs.finish G hu he r).Choice), Nonempty (Branch x.X G S (k := k) (p := p) (n := n) (h := depth) (C := C) (f := f) (g := g) (he := he) (hu := hu) radix drift r c)

private theorem grain_le_height (h q W : ℕ) : W*(h/(16*(q*W)))≤h:=by
  by_cases zero:q=0
  · simp [zero]
  have factor : W≤16*(q*W):=by
    have one:1≤q:=by omega
    have qW:W≤q*W:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right W one
    omega
  exact ((Nat.mul_le_mul_right _ factor).trans (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self h (16*(q*W))))

/-- Four inputs to the original terminal address bound on every attained height.
The same purchased row pool supplies both the count and header banks. -/
theorem earned_preflight_rates (xs : ℕ→Spec) (paidRows : ℕ→ℕ)
    (realized : ∀ᶠ h:ℕ in atTop,∃x : ShellSource F h,xs h=issued x ∧
      paidRows h=(pool_ h x)+(pool_ h x) ∧ IssuedPreflightAt G t f g reset τ B n depth C drift x)
    (hb : 0<B) (branch : G.b≤2^(capRate G t g))
    (budget : 2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤B) :
    TerminalBound (fun h=>(xs h).scalar.shops) ∧ TerminalBound (fun h=>scale (age_ h) invoice) ∧
      TerminalBound paidRows ∧ ∀ᶠ h:ℕ in atTop,(xs h).ScalarRoom h (scale (age_ h) invoice) (paidRows h) :=by
  obtain ⟨K,volumes⟩:=shell_address G t f g reset τ B n depth C
  have scan : TerminalBound (fun h=>scale (age_ h) invoice):=by
    refine ⟨2*invoice,?_⟩
    filter_upwards [eventually_ge_atTop (1:ℕ)] with h one
    intro _
    apply Nat.pow_le_pow_right (by decide : 0<2)
    have day : age_ h≤h:=(Nat.div_le_self ..).trans (Nat.log_le_self ..)
    calc invoice*(age_ h+1)≤ invoice*(2*h):=Nat.mul_le_mul_left _ (by omega)
         _=(2*invoice)*h:=by ring
  refine ⟨⟨K,?_⟩,scan,⟨K,?_⟩,?_⟩
  · filter_upwards [volumes,realized] with h money selected
    obtain ⟨x,chart,_,_⟩:=selected
    intro _
    rw [chart]
    change (st_ h x).hostSize (st_ h x).length≤_
    have cap:=money x
    omega
  · filter_upwards [volumes,realized] with h money selected
    obtain ⟨x,_,size,_⟩:=selected
    intro _
    rw [size]
    have cap:=money x
    omega
  · filter_upwards [PreflightCalendar.attained G op t f g reset τ B drift hb branch budget,realized] with h date selected
    obtain ⟨x,shape,price,positive,he,hu,radix,r,c,⟨issued_⟩⟩:=selected
    rw [shape,price]
    exact Branch.stage_room x.X G op t f g reset τ B h x.sites drift (p_ h x)
      (n:=n) (D:=depth) (C:=C) (he:=he) (hu:=hu) (radix:=radix) (r:=r) (c:=c) issued_ positive
      (grain_le_height h (q_ h x) (bw_ h x)) hb budget date (pool_ h x) (pool_ h x)

/-- The exponent for the entire calibrated mask suffix is chosen before either temporal parameter.
The starting address ranges over all native locations on the one scheduled tape. -/
def MaskMarginal (rate : ℕ) := ∀ᶠ h : ℕ in atTop,∀x : ShellSource F h,
  IssuedPreflightAt G t f g reset τ B n depth C drift x → ∀base,(issued x).maskBase base≤base+2^(rate*h)

private theorem mask_height_bound (h sampled rate shellRate shops bank : ℕ)
    (positive : 1 ≤ h) (sample_le : sampled ≤ h)
    (shops_le : shops ≤ 2^(shellRate*h)) (banks_le : bank+bank ≤ 2^(shellRate*h)) :
    512*(2^(h/2)+shops*2^(rate*(sampled+1))+(bank+bank)+1) ≤
      2^((shellRate+2*rate+12)*h) := by
  let exponent := (shellRate+2*rate+1)*h
  have shell_exp : shellRate*h ≤ exponent :=
    Nat.mul_le_mul_right h (by omega)
  have half_exp : h/2 ≤ exponent :=
    Nat.le_trans (Nat.div_le_self h 2) (Nat.le_mul_of_pos_left h (Nat.succ_pos _))
  have column_exp : rate*(sampled+1) ≤ (2*rate)*h := by
    calc rate*(sampled+1) ≤ rate*(2*h) := Nat.mul_le_mul_left rate (by omega)
         _ = (2*rate)*h := by rw [Nat.mul_comm 2 rate, Nat.mul_assoc]
  have billed : shops*2^(rate*(sampled+1)) ≤ 2^exponent := by
    calc shops*2^(rate*(sampled+1)) ≤ 2^(shellRate*h)*2^((2*rate)*h) :=
           Nat.mul_le_mul shops_le (Nat.pow_le_pow_right (by decide : 0<2) column_exp)
         _ = 2^((shellRate+2*rate)*h) := by rw [← Nat.pow_add, Nat.add_mul]
         _ ≤ 2^exponent := Nat.pow_le_pow_right (by decide : 0<2)
           (Nat.mul_le_mul_right h (Nat.le_succ _))
  have total :
      2^(h/2)+shops*2^(rate*(sampled+1))+(bank+bank)+1 ≤
        2^exponent+2^exponent+2^exponent+2^exponent :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.pow_le_pow_right (by decide : 0<2) half_exp)
      billed) (Nat.le_trans banks_le (Nat.pow_le_pow_right (by decide : 0<2) shell_exp)))
      (Nat.two_pow_pos exponent)
  have gain : exponent+11 ≤ (shellRate+2*rate+12)*h := by
    calc exponent+11 ≤ exponent+11*h :=
           Nat.add_le_add_left (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 11 positive) _
         _ = (shellRate+2*rate+12)*h := by dsimp [exponent]; rw [← Nat.add_mul]
  calc 512*(2^(h/2)+shops*2^(rate*(sampled+1))+(bank+bank)+1) ≤
         512*(2^exponent+2^exponent+2^exponent+2^exponent) := Nat.mul_le_mul_left 512 total
       _ = 2^exponent*2^11 := by change 512*(2^exponent+2^exponent+2^exponent+2^exponent) = 2^exponent*2048; omega
       _ = 2^(exponent+11) := (Nat.pow_add 2 exponent 11).symm
       _ ≤ 2^((shellRate+2*rate+12)*h) := Nat.pow_le_pow_right (by decide : 0<2) gain

private theorem shops_and_banks {shops bank publicRows rawRows ceiling : ℕ}
    (budgeted : shops+bank+publicRows+(rawRows+bank) ≤ ceiling) :
    shops ≤ ceiling ∧ bank+bank ≤ ceiling := by omega

private theorem mask_marginal (K : ℕ)
    (volume : ∀ᶠ h:ℕ in atTop,∀x : ShellSource F h,(st_ h x).hostSize (st_ h x).length+
      (pool_ h x)+(pub_ h x)+((raw_ h x)+(pool_ h x))≤2^(K*h))
    (hb : 0<B) (budget : 2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤B)
    (branch : G.b≤2^(capRate G t g)) :
    MaskMarginal G t f g reset τ B n depth C op drift (K+2*invoice+12) :=by
  filter_upwards [volume,PreflightCalendar.attained G op t f g reset τ B drift hb branch budget,
    eventually_ge_atTop (1:ℕ)] with h shapes date one
  intro x selected base
  obtain ⟨positive,he,hu,radix,r,c,⟨issued_⟩⟩:=selected
  have native := (Branch.stage_preflight x.X G op t f g reset τ B h x.sites drift (p_ h x)
    (n:=n) (D:=depth) (C:=C) (he:=he) (hu:=hu) (radix:=radix) (r:=r) (c:=c)
    issued_ positive (grain_le_height h (q_ h x) (bw_ h x)) hb budget date
    (pool_ h x) (pool_ h x) base).2.2
  have bounds := shops_and_banks (shapes x)
  exact native.trans (Nat.add_le_add_left
    (mask_height_bound h (age_ h) invoice K ((st_ h x).hostSize (st_ h x).length)
      (pool_ h x) one ((Nat.div_le_self ..).trans (Nat.log_le_self ..)) bounds.1 bounds.2) base)

theorem earned_mask_uniform (branch : G.b≤2^(capRate G t g)) :
    ∃A : ℕ,∀τ B : ℕ,0<B → 2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤B →
      MaskMarginal G t f g reset τ B n depth C op drift A :=by
  obtain ⟨K,bound⟩:=uniform_shell_address (F:=F) G t f g reset n depth C
  exact ⟨K+2*invoice+12,fun τ B hb budget=>mask_marginal G t f g reset τ B n depth C op drift K
    (bound τ B) hb budget branch⟩

/-- The three scalar ROMs read this control alphabet and the original physical paid-row count. -/
def ControlMarginal (rate : ℕ) := ∀ᶠ h : ℕ in atTop,∀x : ShellSource F h,
    IssuedPreflightAt G t f g reset τ B n depth C drift x →
      (issued x).controlBytes≤2^(rate*h) ∧ (issued x).paidRows≤2^(rate*h)

private theorem control_marginal (K : ℕ)
    (volume : ∀ᶠ h:ℕ in atTop,∀x : ShellSource F h,(st_ h x).hostSize (st_ h x).length+
      (pool_ h x)+(pub_ h x)+((raw_ h x)+(pool_ h x))≤2^(K*h))
    (hb : 0<B) (budget : 2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤B)
    (branch : G.b≤2^(capRate G t g)) :
    ControlMarginal G t f g reset τ B n depth C op drift (K+1) :=by
  filter_upwards [volume,PreflightCalendar.attained G op t f g reset τ B drift hb branch budget] with h shapes date
  intro x selected
  obtain ⟨positive,he,hu,radix,r,c,⟨b⟩⟩:=selected
  have room:=Branch.stage_room x.X G op t f g reset τ B h x.sites drift (p_ h x)
    (n:=n) (D:=depth) (C:=C) (he:=he) (hu:=hu) (radix:=radix) (r:=r) (c:=c) b positive
    (grain_le_height h (q_ h x) (bw_ h x)) hb budget date (pool_ h x) (pool_ h x)
  have bounds := shops_and_banks (shapes x)
  constructor
  · exact room.book.trans (Nat.pow_le_pow_right (by decide) ((Nat.div_le_self ..).trans
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos K))))
  · change (pool_ h x)≤_
    exact (Nat.le_add_right _ _).trans (bounds.2.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ (Nat.le_succ K))))

theorem earned_control_uniform (branch : G.b≤2^(capRate G t g)) :
    ∃A : ℕ,∀τ B : ℕ,0<B → 2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤B →
      ControlMarginal G t f g reset τ B n depth C op drift A :=by
  obtain ⟨K,bound⟩:=uniform_shell_address (F:=F) G t f g reset n depth C
  exact ⟨K+1,fun τ B hb budget=>control_marginal G t f g reset τ B n depth C op drift K
    (bound τ B) hb budget branch⟩


end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

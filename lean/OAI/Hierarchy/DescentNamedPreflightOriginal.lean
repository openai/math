import OAI.Hierarchy.DescentNamedPreflightFieldBound
import OAI.Hierarchy.DescentTerminalPointerPrice

namespace OAI
/-! # Native fixed register and scan bounds from the reached date and published original capacities -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
attribute [local irreducible] Origin.source
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

open DescentTerminalPreflightSpace
open Computability.BorderVNP.FragmentBucket
namespace Branch

open DescentCompiler.TerminalScale DescentTerminalPointerDigits
variable {tail:ℕ} (base:S.baseGroups=2^tail) (boundary:ℕ) (op:RotorSpec) (headers paid:ℕ)
local notation "fmt" => geometryFormat G S k g p tail boundary R op headers paid
local notation "spec₀" => preflightSpec X G S k g p tail fmt
local notation "cap" => (capCalendar G.b S.rounds g S.height).prod*256
local notation "N" => S.epochPower^S.localTokenExponent
local notation "K" => NativeBranch.privateSlotCapacity G S R
local notation "G₀" => S.groupCount S.length
local notation "V" => G₀*2^k
local notation "A₀" => NativeBranch.localLimit G S
local notation "initialWidth" => S.groupWidth k tail 0+k
local notation "frozen" => k*S.length
local notation "cb" => 8+S.capGain*S.length
local notation "raw" => DescentOperandWidth.recordBits G S k tail R 3 p
local notation "side" => DescentSignedCableCodec.width 3 cap
local notation "extent" => actualSpan G S op boundary p R
local notation "J" => S.height


def shortExponent (σ κ τ ε₀ primitive grain:ℕ):=3*(σ+κ+τ+ε₀+primitive+grain)+4
def scanExponent (κ primitive seats:ℕ) :=6+(κ+max (2*primitive+4) seats)

variable (τ κ r₀ B h₀ σ ε₀:ℕ)
local notation "e" => max (DescentOperandWidth.rate G S r₀ 2) 4
local notation "gExp" => Nat.clog 2 G.b*(S.rounds+1)
local notation "σall" => shortExponent σ κ τ ε₀ e gExp
local notation "scan" => scanExponent κ e S.localCapacityExponent

include hp base b in
theorem original_fields (positive:0<J) (hb:0<B) (age:J=Nat.log 2 h₀/(2*B)) (grainFit:p≤h₀)
    (blockFit:k≤κ*(J+1)) (tailFit:tail=τ*(J+1)) (drift:R+1≤ scale J r₀)
    (large:max (τ+κ*(S.rounds+2)) (max (DescentOperandWidth.rate G S r₀ 2+1) (2*B))≤2^(J+1))
    (field:extent≤ scale J σ) (pub:Nat.clog 2 (boundary+1)≤ scale J ε₀) :
    (∀z∈(spec₀).shortFields,z≤ scale J σall) ∧ (spec₀).scanScale≤ scale J scan := by
  let bound:=σ+κ+τ+ε₀+e+gExp
  let Z:=scale J bound
  have mono (x y:ℕ) (xy:x≤y) : scale J x≤ scale J y :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ xy)
  have grow (v:ℕ) (small:v≤bound) : scale J v≤Z:=mono _ _ small
  have date:=pointer_exponents X G S b hp base τ κ r₀ B h₀ hb age grainFit blockFit tailFit drift large
  have shape:=preflight_caps X G S b (tail:=tail) fmt
  simp only [shape.1,shape.2.1,shape.2.2] at date
  change (∀z∈[N,initialWidth,frozen+1,2^cb,Nat.clog 2 (N+1),Nat.clog 2 (K+1),raw,side],
    z≤ scale J e) ∧ (∀z∈[cap,N,K],z≤ scale J e) at date
  have growth:scale J e≤Z:=grow _ (by dsimp only [bound];omega)
  have groupFit:G₀≤Z:=by
    simp only [AtomSchedule.groupCount,Nat.sub_self,pow_zero,Nat.mul_one,base,tailFit]
    exact grow τ (by dsimp only [bound];omega)
  have bitfit:2^k≤Z:=(Nat.pow_le_pow_right (by decide) blockFit).trans (grow κ (by dsimp only [bound];omega))
  have grainRoom:G.b^(S.rounds*J)*G.b≤Z:=by
    have base_le:=Nat.le_pow_clog (by decide : 1<2) G.b
    have lhs:=Nat.mul_le_mul (Nat.pow_le_pow_left base_le (S.rounds*J)) base_le
    apply lhs.trans
    rw [←pow_mul,←pow_add]
    apply (Nat.pow_le_pow_right (by decide : 0<2) ?_).trans (grow gExp (by dsimp only [bound];omega))
    ring_nf;omega
  have zpos:0<Z:=Nat.two_pow_pos _
  have all:=geometry_short_fields X G S hp base boundary op headers paid Z zpos
    (fun z hz=>(date.1 z hz).trans growth) (fun z hz=>(date.2 z hz).trans growth) groupFit bitfit
    (field.trans (grow σ (by dsimp only [bound];omega))) (pub.trans (grow ε₀ (by dsimp only [bound];omega))) grainRoom
  have inScale:16*Z^3≤ scale J σall:=by
    change 2^4*(2^(bound*(J+1)))^3≤2^((3*bound+4)*(J+1))
    rw [←pow_mul,←pow_add];apply Nat.pow_le_pow_right (by decide)
    nlinarith only [show 0≤4*J by omega]
  have form (j:ℕ) : (2*T J)^j=scale J j:=(DescentCompiler.TerminalScale.residual j J).symm
  have physical_bound (z : ℕ) (hz : z ∈ [cap,N,K]) : z ≤ (2*T J)^e :=
    (date.2 z hz).trans_eq (form e).symm
  have core := @column_bound (T J) cap N K e (Nat.two_pow_pos J)
    (physical_bound cap (by simp)) (physical_bound N (by simp)) (physical_bound K (by simp))
  rw [form] at core
  exact ⟨fun z hz=>(all z hz).trans inScale,preflight_scan_scale X G S b hp base fmt κ (2*e+4)
    positive blockFit core⟩

include hp base b in
theorem original_preflight (positive:0<J) (hb:0<B) (age:J=Nat.log 2 h₀/(2*B)) (grainFit:p≤h₀)
    (blockFit:k≤κ*(J+1)) (tailFit:tail=τ*(J+1)) (drift:R+1≤ scale J r₀)
    (large:max (τ+κ*(S.rounds+2)) (max (DescentOperandWidth.rate G S r₀ 2+1) (2*B))≤2^(J+1))
    (field:extent≤ scale J σ) (pub:Nat.clog 2 (boundary+1)≤ scale J ε₀)
    (budget:2*(6*σall+11)≤B) (sectionHeight:(2^J)^B≤h₀) (origin:ℕ) :
    (spec₀).registerBits≤h₀ ∧ (spec₀).scanScale≤ scale J scan ∧
      (spec₀).maskBase origin≤origin+512*(2^(h₀/2)+(S.hostSize S.length)*scale J scan+(paid+headers)+1) := by
  obtain ⟨short_,workers⟩:=original_fields X G S b hp base boundary op headers paid τ κ r₀ B h₀ σ ε₀
    positive hb age grainFit blockFit tailFit drift large field pub
  have pitch:=(preflight_grains X G S b hp base fmt).2
  have groups:0<(spec₀).groups:=by change 0<G₀;simp [AtomSchedule.groupCount,base]
  have reg:=(spec₀).register_original (scale J σall) (Nat.two_pow_pos _) short_ pitch groups
  have e₁:(6*σall+11)*(J+1)≤J*B:=by
    have a:=Nat.mul_le_mul_left (6*σall+11) (show J+1≤2*J by omega)
    have c:=Nat.mul_le_mul_left J budget;nlinarith only [a,c]
  have smaller:2048*(scale J σall)^6≤(2^J)^B:=by
    change 2^11*(2^(σall*(J+1)))^6≤(2^J)^B
    rw [←pow_mul,←pow_mul,←pow_add];apply Nat.pow_le_pow_right (by decide)
    nlinarith only [e₁,show 0≤11*J by omega]
  have keys:=reg.trans (smaller.trans sectionHeight)
  have done:=preflight_extent X G S b hp base fmt h₀ origin keys (by change 0<columns cap N K;unfold columns;omega)
  have total:=Nat.mul_le_mul_left (S.hostSize S.length) workers
  have scanBound := Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_left total (2^(h₀/2))) (paid+headers)) 1
  exact ⟨keys,workers,done.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 512 scanBound) origin)⟩
end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI

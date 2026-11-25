import OAI.Hierarchy.DescentResetUniformLocalWidth
import OAI.Hierarchy.DescentResetRootOutputScale
import OAI.Hierarchy.DescentScheduledResetChart
import OAI.Hierarchy.DescentPrimitivePaletteCounts

namespace OAI
/-! # Calibrating the common reset register width on the original cap and rotor calendars -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty DescentCompiler.TerminalScale DescentNamedFundedChart Filter
open LinearAlgebra.SpectralBooks ThreeFlat
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ D drift : ℕ)
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "Ht" => GroupStage.depthBound D n f g
local notation "R₀" => DescentNamedFundedChart.localRate G t f g reset D n
local notation "R₁" => ResetMiddle.outputRate G board Ht t f g reset op.C op.w (DescentPackedResetRotorRoles.roleBits n)
local notation "P₀" => 8+((capPeriod G.b t g).map (·+1)).prod
local notation "S₀" => stageNumbers G t 0 f g reset 0 0

/-- This exponent is selected before the word-height multiplier. -/
def localExponent := κ+P₀+13*R₀+R₁+(S₀).localTokenExponent+(1+operandExponent G S₀)+6

def originalSample (J sites age p degree payload e previous lanes nextM base : ℕ) (old : Prior) : Sample :=
  let S:=stageNumbers G t J f g reset sites (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let cap:=((capCalendar G.b t g J).take age).prod*256
  {sched:=S,k:=k,tail:=tail τ J,age:=age,p:=p,drift:=drift,degree:=degree,payload:=payload,
   root:=e,previous:=previous,lanes:=lanes,nextLanes:=nextM,base:=base,
   prior := { old with
     venue := { old.venue with degree := D, cap := cap, paidBits := S.censusBits p }
     printedBits := DescentPrimitivePalette.printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op }}

private theorem poly_room (B c m : ℕ) (positive : 0<B) :
    ∀ᶠ h : ℕ in atTop,let j:=Nat.log 2 h/(2*B); c*(j+1)^m≤ scale j (m+1) :=by
  filter_upwards [eventually_late c B positive] with h hc
  let j:=Nat.log 2 h/(2*B)
  have ones:j+1≤2^(j+1):=Nat.lt_two_pow_self.le
  calc
    _ ≤ 2^(j+1)*(2^(j+1))^m:=Nat.mul_le_mul ((hc.trans (Nat.le_succ _)).trans ones) (Nat.pow_le_pow_left ones _)
    _ = scale j (m+1):=by unfold scale;rw [←pow_mul,←pow_add];congr 1;ring

private theorem age_dim (t j τ gain k age : ℕ) (hk:k≤gain*(j+1)) :
    τ*(j+1)+k*((t+1)*j-age)+k≤(τ+gain*(t+2))*(j+1)^2 :=by
  have b:=Nat.mul_le_mul hk (Nat.sub_le ((t+1)*j) age)
  have a:=Nat.mul_le_mul_right (j+1) (show 1≤j+1 by omega)
  nlinarith only [b,hk,Nat.zero_le (τ*j),Nat.zero_le (τ*j*j),
    Nat.zero_le (gain*j),Nat.zero_le (gain*j*j),Nat.zero_le (gain*t*j),Nat.zero_le (gain*t)]

local notation "A₀" => localExponent G board op t f g reset D
local notation "samp" => originalSample G op t f g reset τ D drift

theorem original_fields (B : ℕ) (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (coefficientDegree : ℕ := D) :
    ∀ᶠ h : ℕ in atTop,let j:=Nat.log 2 h/(2*B);
    ∀sites age p degree e previous lanes nextM base old,p≤h→degree≤coefficientDegree→
      (samp j sites age p degree h e previous lanes nextM base old).LocalAt
        G board D f g op.C op.w j (A₀) :=by
  let z₀:=Nat.clog 2 (6+6*(G.C+2)^8+Fintype.card (DescentResetGates.CanonicalTag (2^op.n))+1)
  let c₀:=z₀+8*(2*B+capRate G t g*(t+1)+1)
  filter_upwards [eventually_late drift B positive,eventually_late 1 B positive,poly_room B (τ+κ*(t+2)) 2 positive,
    poly_room B c₀ 1 positive,ResetMiddle.root_controls_at G t f g reset τ B D n positive,
    DescentNamedFundedChart.scale_at G board t f g reset τ B D positive,
    DescentOperandWidth.issued G drift coefficientDegree t f g reset τ B positive] with h driftRoom agePos dim tag controls funding records
  dsimp only
  intro sites age p degree e previous lanes nextM base old hp hd
  let j:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t j f g reset sites (tail τ j)
  let k:=groupBits t j S.hostGain S.capGain (cutRate t f g)
  let z:=samp j sites age p degree h e previous lanes nextM base old
  let v:=z.output G board D f g op.C op.w
  let cap:=((capCalendar G.b t g j).take age).prod*256
  have enlarge {a σ : ℕ} (ae:a≤ scale j σ) (small:σ≤(A₀)) : a≤ scale j (A₀):=
    ae.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ small))
  have wk:k≤κ*(j+1):=groupBits_linear ..
  have funded:=funding sites age p e previous hp
  have census:=(funded.2)
  have wide:=DescentPrimitivePalette.paletteBits G S branch op positive rfl
    (show 0<S.height from agePos) hp
  have token : z.prior.printedBits≤ scale j 2 :=by
    apply le_trans wide
    apply le_trans _ tag
    change z₀+8*(2*B*(j+1)+j*(capRate G t g*(t+1))+1)≤c₀*(j+1)^1
    dsimp only [c₀]
    rw [pow_one]
    nlinarith only [Nat.zero_le (z₀*j),Nat.zero_le (8*j),Nat.zero_le (8*(capRate G t g*(t+1)))]
  have allowance : drift+1≤ scale j 1 :=by
    change drift+1≤2^(1*(j+1))
    rw [Nat.one_mul]
    exact (Nat.add_le_add_right driftRoom 1).trans Nat.lt_two_pow_self.le
  have fibre : v.setup.retained.donors=2^k :=by
    let c:=S.groupWidth k (tail τ j) age
    let shift:=S.retainedExponent G k (tail τ j) drift degree p age h
    have cut:shift≤c:=Nat.min_le_left ..
    change 2^(c-shift+(shift+k)-c)=2^k
    congr 1;omega
  have nodesExponent : S.localTokenExponent = (S₀).localTokenExponent := rfl
  have argumentsExponent : operandExponent G S = operandExponent G S₀ := rfl
  refine {
    block:=enlarge (Nat.pow_le_pow_right (by decide) wk) ?_
    cap:=enlarge (capPrefix G.b t g j age) ?_
    dim:=enlarge ((age_dim t j τ κ k age wk).trans dim) ?_
    root:=enlarge (controls sites age p e previous hp) ?_
    primaries:=enlarge (ResetMiddle.root_outputs_at G board t j f g reset sites (tail τ j) age (age+1)
        Ht op.C op.w (DescentPackedResetRotorRoles.roleBits n)) ?_
    quantities:=enlarge funded.1 ?_
    paid:=enlarge census ?_
    coefficient:=enlarge (records sites p degree hp hd) ?_
    token:=enlarge token ?_
    «arguments»:=enlarge (S.capacities_at_scale G drift 1 allowance).2 ?_
    nodes:=enlarge (S.capacities_scale G).1 ?_
    fibres:=fibre} <;>
    dsimp only [localExponent] <;> change _≤κ+P₀+13*R₀+R₁+(S₀).localTokenExponent+(1+operandExponent G S₀)+6 <;> omega

/-- Fixed once the original gadget, rotor and per-period gains are fixed. -/
noncomputable def receiverRate :=
  Classical.choose (uniform_width G board D f g op.C op.w (A₀))

local notation "E₀" => receiverRate G board op t f g reset D

theorem original_digit_scale (B : ℕ) (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (coefficientDegree : ℕ := D) :
    ∀ᶠ h : ℕ in atTop,let j:=Nat.log 2 h/(2*B);
    ∀sites age p degree e previous lanes nextM base old,p≤h→degree≤coefficientDegree→
    ((samp j sites age p degree h e previous lanes nextM base old).output G board D f g op.C op.w).groupWidth
      ≤ scale j (E₀) :=by
  obtain ⟨j₀,universal⟩:=eventually_atTop.1 (Classical.choose_spec (uniform_width G board D f g op.C op.w (A₀)))
  filter_upwards [eventually_late j₀ B positive,
    original_fields G board op t f g reset τ D drift B positive branch coefficientDegree] with h hj fieldBounds
  dsimp only
  intro sites age p degree e previous lanes nextM base old hp hd
  exact universal _ hj _ (fieldBounds sites age p degree e previous lanes nextM base old hp hd)

/-- A single height multiplier works on every reset instance, including empty or malformed inputs. -/
theorem original_room (branch : G.b≤2^(capRate G t g)) (coefficientDegree : ℕ := D) :
    ∃E : ℕ,∀B,0<B→2*E≤B→∀ᶠ h:ℕ in atTop,let j:=Nat.log 2 h/(2*B);
      ∀sites age p degree e previous lanes nextM base old,p≤h→degree≤coefficientDegree→
      8*((samp j sites age p degree h e previous lanes nextM base old).output G board D f g op.C op.w).groupWidth≤h :=by
  obtain ⟨E,small⟩:=uniform_half G board D f g op.C op.w (A₀)
  refine ⟨E,fun B hb he=>?_⟩
  filter_upwards [small B hb he,original_fields G board op t f g reset τ D drift B hb branch coefficientDegree] with h room fieldBounds
  dsimp only
  intro sites age p degree e previous lanes nextM base old hp hd
  exact room _ (fieldBounds sites age p degree e previous lanes nextM base old hp hd)

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

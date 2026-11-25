import OAI.Hierarchy.DescentUniformResetEntrance
import OAI.Hierarchy.DescentUniformResetPointSpace

namespace OAI
/-! # One complete reset-address exponent before both calendar parameters are chosen -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler TerminalScale
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (t f g reset drift degreeMax : ℕ)
local notation "Cut" h:arg => ResetArea G board op t f g reset drift degreeMax h
set_option quotPrecheck false in
local notation "Allowed" h:arg => {x:Cut h // x.Verified ∧ x.frozen≤Nat.log 2 h}

theorem ResetArea.pad_limits {h : ℕ} (x : Cut h) (r : x.Verified) :
    DatePorts.PriorPaddingAperture 3 h x.old x.k :=by
  have archive:=x.v.geometry.room.archive
  have token : 0<x.old.tokenBits:=by
    change 0 < x.v.position.ports.tokenBits
    rw [archive.token]
    apply Nat.clog_pos (by decide : 1<2)
    unfold DescentPrimitivePalette.colors
    omega
  have bits : 0<x.old.operandBits:=by
    change 0 < x.v.position.ports.operandBits
    rw [archive.digits]
    exact (Nat.succ_pos _).trans_le (Nat.le_max_right ..)
  have args : x.sched.retainedArgumentsAt G drift≤2^h :=
    r.localNumbers (x.sample.sched.retainedArgumentsAt G x.sample.drift) (by simp [ResetOutput.Sample.localNumbers])
  have large : 2^h≤2^(3*h):= Nat.pow_le_pow_right (by decide) (by omega)
  have dim : x.sched.groupWidth x.k x.frozen x.v.age+x.k≤h:=
    (Nat.le_mul_self _).trans (r.matrix.trans (Nat.div_le_self ..))
  have hLimit : h≤2^(3*h):=Nat.lt_two_pow_self.le.trans large
  have rolePaid : x.old.tokenBits*x.old.nodes*x.old.roleLanes ≤ h/2 := by
    change x.v.position.ports.tokenBits*x.v.position.ports.nodes*x.v.position.ports.roleLanes ≤ _
    rw [archive.token]
    exact archive.roles
  have half : h/2 ≤ 3*h := (Nat.div_le_self h 2).trans (by omega)
  constructor
  · exact x.current_host.trans_le r.oldHost
  · change x.v.position.ports.venue.groups ≤ _
    rw [x.v.geometry.room.population.groups]
    change x.sched.groupCount x.v.age ≤ _
    rw [←x.sched.group_power (k:=x.k) (tail:=x.frozen) rfl rfl x.v.age]
    exact (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right ..).trans dim)).trans large
  · exact x.v.geometry.room.args.trans (args.trans large)
  · exact (Nat.pow_le_pow_right (by decide) ((Nat.le_add_left ..).trans dim)).trans large
  · exact r.operandLanes.trans hLimit
  · exact r.roleLanes.trans hLimit
  · exact rolePaid.trans half
  · exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ token)).trans
      (rolePaid.trans half)
  · exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ bits)).trans
      (archive.operands.trans half)

theorem ProfiledPosition.uniform_reset_spans :
    ∃K:ℕ,∀τ B,0<B→G.b≤2^(capRate G t g)→
      2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B→
      2*degreeRate G board op t f g reset (maximumDegree (t+1))≤B→τ≤B→
      ∀ᶠ h:ℕ in atTop,∀x:ProfiledPosition G board op t f g reset τ drift degreeMax B h,
        x.IsReset→x.resetEnd-x.position.floor≤2^(K*h) :=by
  let x (h:ℕ) (i:Allowed h):=i.val
  have point (h : ℕ) (i : Allowed h) :=i.property.1
  obtain ⟨entry,raw⟩:=ResetArea.uniform_entrance G board op t f g reset drift degreeMax
  have room:=ResetOutput.uniform_point_space G board op t f g reset (atRound t) drift
    (fun h i=>(x h i).cost) (fun h i=>(x h i).ageHeight) (fun h i=>(x h i).v.sites)
    (fun h i=>(x h i).v.age) (fun h i=>(x h i).v.p) (fun h i=>(x h i).v.degree)
    (fun h i=>(x h i).e) (fun h i=>(x h i).previous) (fun h i=>(x h i).nextM)
    (fun h i=>(x h i).base) (fun h i=>(x h i).prior) (fun h i=>(x h i).stage) (fun h i=>(x h i).inside)
    entry point (fun h i=>(x h i).v.active) (fun h i=>(x h i).current_host)
    (fun h i=>(x h i).v.geometry.room.population.groups) (fun h i=>(x h i).v.geometry.format.width)
  have core:=complete_increment (fun h i=>(x h i).stage) (fun h i=>(x h i).inside) room raw
  obtain ⟨P,paid⟩:=DatePorts.uniform_prior_padding 3
  have prior : Bounded (fun h (i:Allowed h)=>(x h i).inside-(x h i).v.position.floor):=
    ⟨P,paid.mono fun h charges i=>charges (x h i).old (x h i).k (x h i).v.position.floor
      (ResetArea.pad_limits G board op t f g reset drift degreeMax (x h i) (point h i))⟩
  have all_ : Bounded (fun h (i:Allowed h)=>(x h i).v.resetEnd-(x h i).v.position.floor) :=by
    apply (prior.add core).of_le
    intro h i
    rw [(x h i).reset_end]
    change (x h i).stage.fullEnd (x h i).inside-(x h i).v.position.floor≤_
    omega
  obtain ⟨K,covered⟩:=all_
  refine ⟨K,?_⟩
  intro τ B den branch cutoff receiver bought
  filter_upwards [covered,ResetArea.eventually_verified G board op t f g reset drift degreeMax τ B den branch cutoff receiver bought,
    eventually_ge_atTop (2^(2*B))] with h fits points late
  intro v fresh
  let y:=ResetArea.atCut G board op t f g reset drift degreeMax v fresh
  have lg : 2*B≤Nat.log 2 h:=Nat.le_log_of_pow_le (by decide) late
  have active : 0<y.ageHeight:=by
    change 0 < Nat.log 2 h / (2*B)
    exact Nat.div_pos lg (by omega)
  have small : y.frozen≤Nat.log 2 h:=by
    change τ*(y.ageHeight+1)≤Nat.log 2 h
    calc
      _ ≤ B*(y.ageHeight+1):=Nat.mul_le_mul_right _ bought
      _ ≤ B*(y.ageHeight+y.ageHeight):=Nat.mul_le_mul_left _ (by omega)
      _ = y.ageHeight*(2*B):=by ring
      _ ≤ _ :=Nat.div_mul_le_self ..
  exact fits (⟨y,points v fresh,small⟩:Allowed h)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI

import OAI.Hierarchy.DescentProfiledPositionBudget
import OAI.Hierarchy.DescentScheduledAreaPoints
import OAI.Hierarchy.DescentUniformPriorPadding

namespace OAI
/-! # A common coordinate system for all the offered reset dates -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler TerminalScale
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Filter
noncomputable section

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (t f g reset drift degreeMax h : ℕ)

structure ResetArea where
  cost : ℕ
  divisor : ℕ
  v : ProfiledPosition G board op t f g reset cost drift degreeMax divisor h
  resetSlot : v.IsReset

namespace ResetArea
variable {G board op t f g reset drift degreeMax h}
variable (x : ResetArea G board op t f g reset drift degreeMax h)

def ageHeight := Nat.log 2 h/(2*x.divisor)
def frozen := tail x.cost x.ageHeight
def sched := stageNumbers G t x.ageHeight f g reset x.v.sites x.frozen
def k := groupBits t x.ageHeight (hostRate t reset) (capRate G t g) (cutRate t f g)
def old := x.v.position.ports
def token := DescentPrimitivePalette.printedBits G (x.sched.firstWidth G.b x.v.p) (x.sched.grainAt G.b x.v.p 0) op
def prior := ResetOutput.Prior.atDate G x.sched x.v.age x.v.p drift x.old.operandLanes x.old.roleLanes x.token x.old.venue
def previous := NativePitch.resetCut x.sched x.k x.frozen x.v.p f h x.v.age
def nextM := NativePitch.incoming x.sched x.k x.frozen x.v.p f h x.v.menu.ordinary (x.v.age+1)
def e := receiverCut G x.sched board x.k x.frozen x.v.age x.v.p f g drift x.v.degree h
  x.previous x.nextM op.C op.w x.old.operandLanes x.old.roleLanes x.token x.old.venue
def inside := x.old.priorStart x.k x.v.position.floor
def stage := PhysicalReset.scheduled G x.sched board x.k x.frozen x.v.age x.v.p f g drift x.v.degree h
  x.v.menu.ordinary op (x.sched.firstWidth G.b x.v.p) (x.sched.grainAt G.b x.v.p 0)
  x.old.operandLanes x.old.roleLanes x.old.venue x.old.io.wire x.old.io.roster x.inside
def base := x.stage.rebased (x.stage.stageStart x.inside)
def sample := ResetOutput.originalSample G op t f g reset x.cost (atRound t) drift x.ageHeight
  x.v.sites x.v.age x.v.p x.v.degree h x.e x.previous (2^x.e) x.nextM x.base x.prior
def Verified : Prop :=
  ResetOutput.AreaPoint G board (atRound t) f g op.C op.w h x.sample x.prior x.stage x.inside
def endAddress := x.stage.fullEnd x.inside

theorem reached_degree : x.old.venue.degree=atRound t :=by
  have slot : x.v.age%(t+1)=t:=x.resetSlot
  have rule := x.v.geometry.degree
  change x.old.venue.degree=atRound (x.v.age%(t+1)) at rule
  rwa [slot] at rule

theorem previous_pitch : x.old.venue.lanes=2^x.previous:=by
  have value : x.old.venue.lanes = NativePitch.incoming x.sched x.k x.frozen x.v.p f h x.v.menu.ordinary x.v.age :=
    x.v.geometry.format.pitch x.v.active
  have active : x.v.age < x.sched.length := x.v.active
  have fresh : x.v.age % (x.sched.rounds + 1) = x.sched.rounds := x.resetSlot
  simp only [NativePitch.incoming, active, fresh, ↓reduceIte] at value
  exact value

theorem current_host : x.old.venue.hosts=x.sched.hostSize x.v.age :=
  x.v.geometry.room.population.venue_eq x.sched x.v.geometry.room.initialSites.choose_spec x.v.geometry.room.radix

theorem reset_end : x.v.resetEnd=x.endAddress:=rfl

variable (G board op t f g reset drift degreeMax)
set_option quotPrecheck false
set_option hygiene false
local notation "A" h:arg => ResetArea G board op t f g reset drift degreeMax h
local notation "O" τ:arg B:arg h:arg => ProfiledPosition G board op t f g reset τ drift degreeMax B h
def atCut {τ B : ℕ} (v : O τ B h) (fresh : v.IsReset) : A h :=⟨τ,B,v,fresh⟩

theorem eventually_verified (τ B : ℕ) (den : 0<B) (branch : G.b≤2^(capRate G t g))
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B)
    (receiver : 2*degreeRate G board op t f g reset (maximumDegree (t+1))≤B) (tailBought : τ≤B) :
    ∀ᶠ h:ℕ in atTop,∀v:O τ B h,∀fresh:v.IsReset,(atCut G board op t f g reset drift degreeMax v fresh).Verified :=by
  let I (h:ℕ):={v:O τ B h //v.IsReset}
  let a (h:ℕ) (i:I h):A h :=atCut G board op t f g reset drift degreeMax i.val i.property
  have d : atRound t≤ maximumDegree (t+1):=by simpa only [Nat.mod_eq_of_lt (Nat.lt_succ_self t)] using round_degree_le t t
  have purchase := (Nat.mul_le_mul_left 2 (Finset.le_sup
    (f:=fun j:Fin (maximumDegree (t+1)+1)=>ResetOutput.receiverRate G board op t f g reset j.val)
    (Finset.mem_univ (⟨atRound t,Nat.lt_succ_of_le d⟩:Fin (maximumDegree (t+1)+1))))).trans receiver
  have earned := scheduled_area_points (ι := I) G board op t f g reset τ (atRound t) drift B
    (fun h (i:I h)=>i.val.sites) (fun h i=>i.val.age) (fun h i=>i.val.p) (fun h i=>i.val.degree)
    (fun h i=>(a h i).old.operandLanes) (fun h i=>(a h i).old.roleLanes) (fun h i=>(a h i).inside)
    (fun h i=>i.val.menu.ordinary) (fun h i=>(a h i).old.venue) (fun h i=>(a h i).old.io.wire)
    (fun h i=>(a h i).old.io.roster) den branch cutoff purchase tailBought (fun _ _ _=>rfl)
    degreeMax (fun _ i=>i.val.grainLimit) (fun _ i=>i.val.degreeLimit)
    (Bounded.restrict ProfiledPosition.site_room (fun _ v=>v.IsReset)) (fun _ i=>i.val.active)
    (fun h i=>(a h i).reached_degree) (fun _ i=>i.val.geometry.capacity) (fun _ i=>i.val.geometry.format.paid)
    (fun h i=>(a h i).current_host) (fun _ i=>i.val.geometry.room.population.groups)
    (fun _ i=>i.val.geometry.format.width) (fun h i=>(a h i).previous_pitch) (d.trans (maximumDegree_quota t))
    (Eventually.of_forall fun h i=>i.val.geometry.room.archive.previous G (a h i).sched op)
    (fun _ i=>i.val.siteLimit)
  exact earned.mono fun h all_ v fresh=>all_ ⟨v,fresh⟩
end ResetArea
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI

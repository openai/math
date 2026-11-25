import OAI.Hierarchy.DescentRegisteredPaddedIncrements
import OAI.Hierarchy.DescentRegisteredProfileMenu
import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentMaximumDegreeQuota
import OAI.Hierarchy.DescentRegisteredReceiverWidth

namespace OAI
/-! # Public positions offered to the selected machine at a given height -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentCompiler.TerminalScale
open DescentTerminalEpochChart DescentPacking.PackedMatch.Local.Stage Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d:ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
    (t f g reset τ drift degreeMax B h : ℕ)
set_option quotPrecheck false
set_option hygiene false
local notation "J_" => Nat.log 2 h/(2*B)
local notation "frozen_" => tail τ J_
local notation "cells_" => groupBits t J_ (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "sched_" m:arg => stageNumbers G t J_ f g reset m frozen_

/-- The register offered before a date is admitted. Its archive and profile
may vary over all input histories at this height. -/
structure ProfiledPosition where
  owners : Type
  entries : List (Source owners)
  sites : ℕ
  p : ℕ
  degree : ℕ
  lo : ℕ
  header : ℕ
  bus : ℕ
  age : ℕ
  position : Position
  siteLimit : sites≤(2^h)^2
  grainLimit : p≤h
  degreeLimit : degree≤degreeMax
  active : age<(sched_ sites).length
  geometry : Geometry G (sched_ sites)
    (fromProfiles G (sched_ sites) board op cells_ frozen_ p f g drift degree h lo header entries)
    cells_ bus age position

namespace ProfiledPosition
variable {G board op t f g reset τ drift degreeMax B h}
local notation "visits_" atH:arg => ProfiledPosition G board op t f g reset τ drift degreeMax B atH
variable (v : visits_ h)

def menu := fromProfiles G (sched_ v.sites) board op cells_ frozen_ v.p f g drift v.degree h v.lo v.header v.entries

def resetEnd := (scheduledAtPorts G (sched_ v.sites) board cells_ frozen_ v.age v.p f g drift v.degree h
  v.menu.ordinary op ((sched_ v.sites).firstWidth G.b v.p) ((sched_ v.sites).grainAt G.b v.p 0)
  v.position.ports v.position.floor).fullEnd

def IsReset : Prop := v.age%(t+1)=t

theorem site_room : Bounded (fun h (v : visits_ h)=>v.sites) :=
  ⟨2,Eventually.of_forall fun h v=>by simpa only [←pow_mul,Nat.mul_comm h 2] using v.siteLimit⟩

variable (G board op t f g reset τ drift degreeMax B)
theorem reset_spans (den : 0<B) (branch : G.b≤2^(capRate G t g))
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B)
    (receiver : 2*degreeRate G board op t f g reset (maximumDegree (t+1))≤B) (tailBought : τ≤B) :
    Bounded (fun h (v:{a:visits_ h // a.IsReset})=>v.val.resetEnd-v.val.position.floor) :=by
  refine registered_padded_increments (ι := fun h => {a : visits_ h // a.IsReset}) G board op t f g reset τ (maximumDegree (t+1)) drift B
    (fun h v=>v.val.sites) (fun h v=>v.val.age) (fun h v=>v.val.p) (fun h v=>v.val.degree)
    (fun h v=>v.val.position.floor) (fun h v=>v.val.menu.ordinary) (fun h v=>v.val.position.ports)
    den branch cutoff receiver tailBought (fun _ _ _=>rfl) degreeMax (fun _ v=>v.val.grainLimit)
    (fun _ v=>v.val.degreeLimit) (Bounded.restrict site_room (fun _ a=>a.IsReset))
    (fun _ v=>v.val.active) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun _ v=>v.val.geometry.degree.le.trans (round_degree_le t _)
  · exact fun _ v=>v.val.geometry.capacity
  · exact fun _ v=>v.val.geometry.format.paid
  · exact fun _ v=>v.val.geometry.room.population.venue_eq _ v.val.geometry.room.initialSites.choose_spec v.val.geometry.room.radix
  · exact fun _ v=>v.val.geometry.room.population.groups
  · exact fun _ v=>v.val.geometry.format.width
  · intro h v
    have incoming:=v.val.geometry.format.pitch v.val.active
    have fresh : v.val.age % ((sched_ v.val.sites).rounds + 1) = (sched_ v.val.sites).rounds := v.property
    simp only [NativePitch.incoming, v.val.active, fresh, ↓reduceIte] at incoming
    exact incoming
  · exact maximumDegree_quota t
  · exact Eventually.of_forall (fun h v=>v.val.geometry.room.archive)
  · exact Eventually.of_forall (fun h v=>v.val.geometry.room.args)

end ProfiledPosition
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI

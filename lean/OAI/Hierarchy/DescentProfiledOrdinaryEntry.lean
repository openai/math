import OAI.Hierarchy.DescentProfiledOrdinaryOffer
import OAI.Hierarchy.DescentRegisteredEntrySourceBounds

namespace OAI
/-! Address purchase for the signed intake, W books and predecessor roles on every actual profiled cut. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentInitialHost DescentCompiler DescentCompiler.TerminalScale DescentMixedRouter DescentResetInvoice
open Chronology Chronology.RegisterTimeline DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing ProtocolRAM Filter
open ThreeFlat Routing DescentRawCablePanel DescentPacking.PackedMatch.Local
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset τ drift degreeMax B : ℕ)
local notation "offer_" H:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B H
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (x).slot.sites (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "d_" h:arg x:arg => DonorDate.atDate G (S_ h x) g (k_ h) (x).slot.age (x).slot.p
local notation "P_" _h:arg x:arg => (x).slot.position.ports
local notation "shelter_" h:arg x:arg => (x).base.registeredEntry (P_ h x) (x).stageFloor
local notation "clip_" h:arg x:arg => (shelter_ h x).clip

theorem rect_amount (date : DonorDate) : 2^date.exponent+1 ≤ date.amount := by
  let F₀ := date.format
  have key : 1 ≤ Owners.digits F₀.blocks F₀.degree F₀.short := by
    exact (show 1≤date.exponent+3 by omega).trans ((le_max_left ..).trans (le_max_left ..))
  have full : 2^date.exponent ≤ DepotRAM.ownerBits F₀ := by
    exact (Nat.le_mul_of_pos_left F₀.blocks (Nat.mul_pos key (by decide : 0<3))).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have word : DepotRAM.ownerBits F₀ ≤ DepotRAM.totalBits F₀ := by
    unfold DepotRAM.totalBits
    omega
  have high : 2*DepotRAM.totalBits F₀+1 ≤ date.amount := (le_max_right ..).trans (le_max_right ..)
  omega

private theorem old_positive {h : ℕ} (x : offer_ h) :
    0 < (P_ h x).nodes ∧ (P_ h x).nodes ≤ (S_ h x).retainedNodes := by
  have nonzero : 0 < (S_ h x).retainedNodes := Nat.pow_pos (Nat.two_pow_pos _)
  rw [x.slot.geometry.room.archive.nodes]
  split <;> omega

variable {G board op t f g reset τ drift degreeMax B} in
theorem entry_words {h : ℕ} (x : offer_ h) :
    let p:=P_ h x
    let a:=shelter_ h x
    0 < p.nodes ∧ 2 ≤ p.operandBits ∧ p.operandBits*p.nodes*p.operandLanes ≤ h ∧
      0 < a.roleBits ∧ a.roleBits*p.nodes*p.roleLanes ≤ h ∧
      x.model.reference.oldNodes=p.nodes ∧ 2^x.base.area.k+1 ≤ x.base.area.unit :=by
  let archive:=x.slot.geometry.room.archive
  have two : 2 ≤ (P_ h x).operandBits := by
    rw [archive.digits]
    exact (Nat.le_max_left 2 _).trans (le_max_left ..)
  have positive : 0 < (shelter_ h x).roleBits := by
    apply Nat.clog_pos (by decide : 1 < 2)
    change 1 < DescentPrimitivePalette.censusCount _+(_+(1+_))+1
    omega
  refine ⟨(old_positive G board op t f g reset τ drift degreeMax B x).1,two,
    archive.operands.trans (Nat.div_le_self ..),positive,archive.roles.trans (Nat.div_le_self ..),rfl,?_⟩
  rw [show x.base.area=(d_ h x).schedule h (x.slot.menu.seats x.slot.age) ((S_ h x).censusBits x.slot.p)
      from congrArg PhysicalOrdinary.StaticCore.area x.core]
  exact rect_amount (d_ h x)

theorem entry (den : 0 < B) :
    PhysicalOrdinary.EntryAddressInputs (fun h (x : offer_ h) => x.base)
      (fun h (x : offer_ h) => P_ h x) (fun h (x : offer_ h) => x.stageFloor) := by
  let sites := fun h (x : offer_ h) => x.slot.sites
  let age := fun h (x : offer_ h) => x.slot.age
  let p := fun h (x : offer_ h) => x.slot.p
  let degree := fun h (x : offer_ h) => x.slot.degree
  let seats := fun h (x : offer_ h) => x.slot.menu.seats x.slot.age
  have supply : Bounded sites := ⟨2,Eventually.of_forall fun h x => by
    simpa only [←pow_mul,Nat.mul_comm h 2] using x.slot.siteLimit⟩
  have geo := PhysicalOrdinary.ordinary_geometry G t f g reset τ B sites age p supply (fun _ x => x.slot.active.le)
  have trueBits : ∀ᶠ h : ℕ in atTop, ∀ x : offer_ h, p h x≤h ∧ degree h x≤degreeMax ∧
      (P_ h x).nodes≤(S_ h x).retainedNodes ∧ (S_ h x).firstWidth G.b (p h x)≤h :=
    Eventually.of_forall fun _ x => ⟨x.slot.grainLimit,x.slot.degreeLimit,(old_positive G board op t f g reset τ drift degreeMax B x).2,x.firstWidth⟩
  have primitive := (PhysicalOrdinary.registered_primitive_rate G op t f g reset τ B drift degreeMax
    sites age p degree seats (fun _ x => x.stageFloor) (fun h x => P_ h x) (fun _ x => x.base)
    den geo (fun _ x => x.primitive_shape) trueBits).1
  have area (h : ℕ) (x : offer_ h) : x.base.area=(d_ h x).schedule h (seats h x) ((S_ h x).censusBits (p h x)) :=
    congrArg PhysicalOrdinary.StaticCore.area x.core
  have form (h : ℕ) (x : offer_ h) : (clip_ h x).venue.socket=(d_ h x).format :=
    congrArg PhysicalOrdinary.StaticCore.format x.core
  have hdim (h : ℕ) (x : offer_ h) : (clip_ h x).venue.hosts=hostRows ((S_ h x).hostSize x.slot.age) :=
    congrArg Dated.Ordinary.H (area h x)
  have gdim (h : ℕ) (x : offer_ h) : (clip_ h x).venue.groups=(S_ h x).groupCount x.slot.age :=
    congrArg Dated.Ordinary.G (area h x)
  have ageWidth (h : ℕ) (x : offer_ h) : x.base.area.k=k_ h := congrArg Dated.Ordinary.k (area h x)
  have args : Bounded (fun h (x : offer_ h) => (P_ h x).argumentsPerNode) := by
    have sizes : SmallAt (fun h => J_ h) (fun h (x : offer_ h) => (P_ h x).argumentsPerNode) := by
      refine ⟨(drift+1) + operandExponent G (stageNumbers G t 0 f g reset 0 0),Eventually.of_forall ?_⟩
      intro h x
      have driftFit : drift+1 ≤ DescentCompiler.TerminalScale.scale (J_ h) (drift+1) :=
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans Nat.lt_two_pow_self.le
      exact x.slot.geometry.room.args.trans (((S_ h x).capacities_at_scale G drift (drift+1) driftFit).2)
    exact sizes.bounded (Eventually.of_forall fun h => (Nat.div_le_self ..).trans (Nat.log_le_self ..))
  apply PhysicalOrdinary.registered_entry_source_bounds
  · exact geo.axis.oldHost.padded.of_le (fun h x => (hdim h x).le)
  · exact geo.axis.oldGroup.of_le (fun h x => (gdim h x).le)
  · exact geo.degree.of_le (fun h x => (congrArg DepotRAM.Shape.degree (form h x)).le)
  · exact geo.blocks.of_le (fun h x => (congrArg DepotRAM.Shape.blocks (form h x)).le)
  · exact geo.cap.of_le (fun h x => (congrArg DepotRAM.Shape.cap (form h x)).le)
  · exact primitive.lows
  · exact geo.blocks.of_le (fun h x => (congrArg (2^·) (ageWidth h x)).le)
  · exact primitive.old
  · exact args
  · exact geo.axis.oldHost.padded.of_le (fun _ x =>
      x.slot.geometry.room.population.earlier.trans x.slot.geometry.room.population.venue_high)
  · exact geo.axis.oldGroup.of_le (fun _ x => x.slot.geometry.room.population.groups.le)
  · intros; rfl
  · exact Eventually.of_forall fun _ x => x.entry_words

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI

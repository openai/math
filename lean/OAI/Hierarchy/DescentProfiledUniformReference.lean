import OAI.Hierarchy.DescentProfiledUniformEntry
import OAI.Hierarchy.DescentUniformSurvivorGeometry
import OAI.Hierarchy.DescentProfiledOrdinaryReference

namespace OAI
/-! The full ordinary reference address exponent is chosen before the tail and height denominator. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentPacking.PackedMatch.Local.Stage DescentInitialHost Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)
local notation "offer" τ:arg B:arg h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h

private structure ReferenceSample (h : ℕ) where
  tailRate : ℕ
  budget : ℕ
  point : offer tailRate budget h
  entry : point.EntryAdmission
  signed : SignedAdmission G board op t f g reset drift degreeMax tailRate budget h point
  short : point.model.operandShortBits ≤ h

theorem uniform_reference :
    ∃e : ℕ,∀τ B : ℕ, SignedStage.unitRate G t f g reset < B →
      ∀ᶠ h : ℕ in atTop,∀x : offer τ B h, x.model.referenceWords ≤ 2^(e*h) := by
  let I := ReferenceSample G board op t f g reset drift degreeMax
  let tailRate (h : ℕ) (i : I h) := i.tailRate
  let den (h : ℕ) (i : I h) := i.budget
  let pt (h : ℕ) (i : I h) := i.point
  let base (h : ℕ) (i : I h) := i.point.base
  let prior (h : ℕ) (i : I h) := i.point.slot.position.ports
  let floor (h : ℕ) (i : I h) := i.point.stageFloor
  let J (h : ℕ) (i : I h):=Nat.log 2 h/(2*i.budget)
  let sched (h : ℕ) (i : I h):=stageNumbers G t (J h i) f g reset i.point.slot.sites (tail i.tailRate (J h i))
  let k (h : ℕ) (i : I h):=groupBits t (J h i) (hostRate t reset) (capRate G t g) (cutRate t f g)
  let DD (h : ℕ) (i : I h) := DonorDate.atDate G (sched h i) g (k h i) i.point.slot.age i.point.slot.p
  have axis {a : ∀ h,I h→ℕ} (fitted : ∀h i,a h i≤2^h) : Bounded a :=
    ⟨1,Eventually.of_forall fun h i=>by simpa only [Nat.one_mul] using fitted h i⟩
  have original (h) (i : I h) : (base h i).area=(DD h i).schedule h
      (i.point.slot.menu.seats i.point.slot.age) ((sched h i).censusBits i.point.slot.p) :=
    congrArg PhysicalOrdinary.StaticCore.area i.point.core
  have hhost : Bounded (fun h (i : I h)=>i.point.model.vector.hosts) := by
    refine ⟨4,Eventually.of_forall fun h i=>?_⟩
    apply Nat.pow_le_pow_right (by decide : 0<2)
    exact (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr i.entry.raw.oldHost
  have block : Bounded (fun h (i : I h)=>i.point.model.vector.radix) := axis (fun _ i=>i.entry.raw.blocks)
  have time : Bounded (fun h (_ : I h)=>h) := axis (fun _ _=>Nat.lt_two_pow_self.le)
  have resolver := (PhysicalOrdinary.operand_rooms (fun _ (i : I _)=>i.point.model)
    (Eventually.of_forall fun _ i=>i.point.prices)
    (fun h i=>i.point.base.registered_geometry (prior h i) (floor h i))
    (fun h i=>(i.point.base.registered_node_chart (prior h i) (floor h i)).2) (fun _ _=>rfl)
    hhost (axis fun _ i=>i.entry.low) (axis fun _ i=>i.entry.freshNodes) (axis fun _ i=>i.entry.freshArgs)
    block (axis fun _ i=>i.entry.raw.newGroup)
    (time.of_le fun h i=>(pitch G board op t f g reset i.tailRate drift degreeMax i.budget h i.point).1)).resolver
  have registered := uniform_entry G board op t f g reset drift degreeMax (ι:=I) tailRate den pt (fun _ i=>i.entry)
  have material := (material_and_survivor G board op t f g reset drift degreeMax (ι:=I) tailRate den pt (fun _ i=>i.signed)).1
  have dims : PhysicalOrdinary.ReferenceAddressInputs base prior floor := by
    refine ⟨registered,material,resolver,?_,?_,axis (fun _ i=>i.entry.raw.wires),axis (fun _ i=>i.entry.nodes),
      hhost,hhost,?_,Eventually.of_forall (fun _ _=>le_rfl),?_,⟨1,Eventually.of_forall fun h i=>by rw [Nat.one_mul]; exact i.short⟩⟩
    · apply axis
      intro h i
      exact (congrArg Dated.Ordinary.D (original h i)).le.trans i.entry.raw.degree
    · apply axis
      intro h i
      exact (congrArg (fun a : Dated.Ordinary=>2^a.k) (original h i)).le.trans i.entry.raw.blocks
    · intro h i
      let x:=i.point
      exact ((prior h i).ordinary_header_dimensions x.cut.ticket op g (tail i.tailRate (J h i)) x.slot.p f drift
        x.slot.degree h (x.slot.menu.seats x.slot.age) x.slot.position.floor x.slot.menu.ordinary x.slot.active x.cut.radix).2.2.2
    · intro h i
      let x:=i.point
      exact (Branch.signed_at x.cut.original G (sched h i) x.cut.branch x.cut.ticket x.cut.before x.cut.after x.cut.joined h).symm
  obtain ⟨e,fit⟩:=PhysicalOrdinary.registered_reference_rate base prior floor dims
  refine ⟨e,fun τ B slack=>?_⟩
  filter_upwards [fit,entry_admission G board op t f g reset τ drift degreeMax B (by omega),
    signed_admission G board op t f g reset drift degreeMax τ B slack,
    short_digits G board op t f g reset τ drift degreeMax B slack] with h bound a b c
  exact fun x=>bound (⟨τ,B,x,a x,b x,c x⟩ : I h)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI

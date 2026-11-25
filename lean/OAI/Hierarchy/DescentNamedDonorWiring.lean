import OAI.Hierarchy.DescentPhysicalOriginalDonorDirectory
import OAI.Hierarchy.DescentCalendarOriginalDonorSeen

namespace OAI
/-! Transport of the three authentic sensor columns from the physical date to the geometric row names. -/
namespace Hierarchy.DescentResetOriginalDonors.Layout
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
variable {L K : DescentResetOriginalDonors.Layout}

theorem relocate_exhibits (shape : L=K) (base : ℕ) (v : K.Values) {w : ℕ} (m : Memory w)
    (src : Sensors L.slots) (src' : Sensors K.slots) (same : HEq src src')
    (ready : L.Ready base src w) (seen : K.Seen src' v m) :
    K.Exhibits base v (L.after base src m):=by
  subst K
  cases eq_of_heq same
  exact L.exhibits base src v m ready seen

theorem denseLabel_transport {used H : ℕ} (eqn : L=K) (name : Fin used→Fin K.sparseHosts) (v : K.Values)
    (x : Fin L.blocks) (side : Bool) (i : Fin L.slots) (y : Fin H) (g : Fin L.groups) :
    (L.denseLabel (fun j=>(name j).cast (congrArg (·.sparseHosts) eqn).symm)
       (cast (congrArg Values eqn.symm) v) x side i y g).val=
    (K.denseLabel name v (x.cast (congrArg (·.blocks) eqn)) side (i.cast (congrArg (·.slots) eqn)) y
       (g.cast (congrArg (·.groups) eqn))).val:=by
  subst K
  rfl

theorem denseCargo_transport {used H : ℕ} (eqn : L=K) (name : Fin used→Fin K.sparseHosts) (v : K.Values)
    (x : Fin L.blocks) (side : Bool) (f : Fin 2) (i : Fin L.slots) (y : Fin H) (g : Fin L.groups) :
    (L.denseCargo (fun j=>(name j).cast (congrArg (·.sparseHosts) eqn).symm)
       (cast (congrArg Values eqn.symm) v) x side f i y g).val=
    (K.denseCargo name v (x.cast (congrArg (·.blocks) eqn)) side f (i.cast (congrArg (·.slots) eqn)) y
       (g.cast (congrArg (·.groups) eqn))).val:=by
  subst K
  rfl
end Hierarchy.DescentResetOriginalDonors.Layout

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open ProtocolRAM DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {a : PhysicalReset} {floor w : ℕ} (I : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "s" => (v).sheets
local notation "r" => ((v).remap b).endAddress
local notation "A" => (v).contactShape
local notation "lo" => (v).front.donorStart ((v).actorEnd b)
local notation "first" => (v).trunkEnd b
local notation "scene" => (v).issuedScene b I.earlier
local notation "deck" => (v).originalDonorLayout I.numbered.signedSlots
local notation "selected" => (A).numberingLayout (s).selectorBits (s).shortBits
local notation "fields" => (A).originalSensors lo first (scene).donor
local notation "dir" => (v).actor.directory ((v).middle.stop b)
local notation "pre" m:arg => I.numbered.prefixOutput r (I.masked.image (I.privateResult m))
local notation "P" => I.numbered.publicSide r

/-- These five identities refer only to the numerical program and its projected operands. -/
structure DonorWiring : Prop where
  original : (s).originalDonors=deck
  projected : deck=selected
  sensor : HEq I.numbered.sensor fields
  label : (P).old.label=((v).originalPrior b I.numbered.signedSlots).label
  cargo : (P).old.cargo=((v).originalPrior b I.numbered.signedSlots).cargo

private theorem received {L K : DescentResetOriginalDonors.Layout} (eqn : L=K) (vals : K.Values)
    (src : DescentResetOriginalDonors.Sensors K.slots) (m : Memory w) (seen : K.Seen src vals m) :
    L.Seen (cast (congrArg (fun n : DescentResetOriginalDonors.Layout=>DescentResetOriginalDonors.Sensors n.slots)
      eqn.symm) src) (cast (congrArg DescentResetOriginalDonors.Layout.Values eqn.symm) vals) m:=by
  subst K
  exact seen

theorem donor_fields_of_seen {used : ℕ} (wiring : I.DonorWiring) (ok : I.Ready) (m : Memory w)
    (name : Fin used→Fin (v).front.peer.hosts) (value : (selected).Values) (seen : (selected).Seen fields value (I.donorDeckEntry m))
    (count : m (dir).count.base=(used:Word w))
    (inverse : ∀i:Fin used,m ((dir).inverse.base+i.val)=((name i).val:Word w))
    (countFits : used<2^w) (hostFits : (s).hosts≤2^w) (size : used≤(dir).inverse.size) :
    let actual:=cast (congrArg DescentResetOriginalDonors.Layout.Values wiring.projected.symm) value
    (∀x side j,Source ((P).old.label x side j) ((deck).denseLabel (H:=(s).hosts) name actual x side j) (s).lanes (pre m)) ∧
    (∀x side f j,Source ((P).old.cargo x side f j) ((deck).denseCargo (H:=(s).hosts) name actual x side f j) (s).lanes (pre m)) :=by
  let ready:=received wiring.projected value fields (I.donorDeckEntry m) seen
  have pub:=DescentResetOriginalDonors.Layout.relocate_exhibits wiring.original ((s).inputDonorsBase r)
    _ (I.donorDeckEntry m) I.numbered.sensor _ (wiring.sensor.trans (cast_heq _ _).symm) ok.numbers.donor ready
  have directory:=I.donor_prefix_directory ok m name count inverse countFits hostFits size
  have both:=(deck).dense_sources name _ (pre m) ((s).inputDonorsBase r) ((v).remap b).first (dir).count
    (dir).inverse r directory pub
  constructor
  · intro x side slot
    rw [wiring.label]
    exact both.1 x side slot
  · intro x side field slot
    rw [wiring.cargo]
    exact both.2 x side field slot

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI

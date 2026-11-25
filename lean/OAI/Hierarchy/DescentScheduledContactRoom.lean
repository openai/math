import OAI.Hierarchy.DescentCalibratedResetChart
import OAI.Hierarchy.DescentContactPreROMBounds
import OAI.Hierarchy.DescentContactOutputRate

namespace OAI
/-! # Every contact dictionary width at the selected reset pitch -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup Filter
noncomputable section
variable {ι : ℕ→Type*} (p : ∀h,ι h→ResetOutput)

/-- The two group counts are the previous coarse groups and the reached reset groups.
The socket count is taken from the actual candidate sheet. -/
structure ContactDimensions : Prop where
  hosts : Bounded (fun h i=>(p h i).front.donor.hosts)
  oldGroups : Bounded (fun h i=>(p h i).front.donor.groups)
  newGroups : Bounded (fun h i=>(p h i).sheets.groups)
  lanes : Bounded (fun h i=>(p h i).receiver.lanes)
  degree : Bounded (fun h i=>(p h i).front.donor.degree)
  lows : Bounded (fun h i=>(p h i).front.donor.lows)
  cap : Bounded (fun h i=>(p h i).front.donor.cap)
  shapes : Bounded (fun h i=>(p h i).front.peer.shapes)
  sockets : Bounded (fun h i=>(p h i).sheets.contacts)

structure ContactAligned (v : ResetOutput) : Prop where
  donorLanes : v.front.donor.batch=v.receiver.lanes
  probeLanes : v.front.contact.batch=v.receiver.lanes
  newLanes : v.sheets.lanes=v.receiver.lanes
  oldHosts : v.front.contact.hosts=v.front.donor.hosts
  oldGroups : v.front.contact.groups=v.front.donor.groups
  oldLows : v.front.contact.lows=v.front.donor.lows
  oldCap : v.front.contact.cap=v.front.donor.cap
  shapeCount : v.front.contact.shapes=v.front.peer.shapes
  contacts : v.front.contact.sockets=v.sheets.contacts
  maskedContacts : v.contactShape.sockets=v.sheets.contacts
  blocks : v.sheets.blocks=v.front.donor.lows
  lanes : 0<v.receiver.lanes
  inputField : 0<v.front.donor.fieldBits
  probeField : 0<v.front.contact.fieldBits

theorem fromBoard_contact_aligned {F : Type} [Field F] {n d : ℕ} (G : DescentSixParty.PoweredGadget F)
    (S : DescentCompiler.AtomSchedule) (board : NonlinearExpanders.Graph n d)
    (k tail age p f g drift degree payload e previous nextM C packet : ℕ) (prior : Prior) (base : ℕ) :
    ContactAligned (fromBoard G S board k tail age p f g drift degree payload e previous (2^e) nextM C packet prior base):=by
  let cap := ((DescentCompiler.capCalendar G.b S.rounds g S.height).take age).prod * 256
  let height := DescentSixParty.GroupStage.depthBound prior.venue.degree n f g
  have field : 0 < ResetMiddle.fieldWidth prior.venue.degree cap n k height := by
    unfold ResetMiddle.fieldWidth
    exact (Nat.zero_lt_succ k).trans_le ((Nat.le_max_left ..).trans (Nat.le_max_right ..))
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,Nat.two_pow_pos e,field,field⟩

private structure ContactWidths (v : ResetOutput) (h : ℕ) : Prop where
  board : (v.front.donor.fieldBits*v.front.donor.boardFields+v.front.donor.fieldBits)*v.front.donor.batch≤h
  split : (v.front.donor.fieldBits*v.front.donor.laneFields*2+
    v.front.donor.fieldBits*v.front.donor.laneFields)*v.front.donor.batch≤h
  opposite : (v.front.donor.fieldBits*v.front.donor.returnFields+v.front.donor.fieldBits)*v.front.donor.batch≤h
  field : v.front.donor.fieldBits*v.front.donor.batch≤h
  halo : (v.front.donor.queryBits+v.front.donor.cargoBits)*v.front.donor.batch≤h
  returned : (v.front.donor.cargoBits+v.front.donor.cargoBits)*v.front.donor.batch≤h
  old : (v.front.contact.fieldBits*v.front.contact.oldFields+v.front.contact.fieldBits)*v.front.contact.batch≤h
  view : (v.front.contact.viewBits+v.front.contact.viewBits)*v.front.contact.batch≤h
  mark : (v.front.contact.fieldBits*8+v.front.contact.fieldBits)*v.front.contact.batch≤h
  marker : v.front.contact.outputBits*v.front.donor.batch≤h
  «meta» : v.sheets.metaBits*v.front.donor.batch≤h
  masked : (v.sheets.metaBits*v.sheets.blocks)*v.sheets.lanes≤h

private theorem contact_widths (v : ResetOutput) (a : ContactAligned v) (h : ℕ)
    (paid : ∀b,b∈v.rootUnits ∨ b∈v.receiverUnits→b*v.receiver.lanes≤h/2) : ContactWidths v h:=by
  have take (b : ℕ) (mem : b∈v.rootUnits ∨ b∈v.receiverUnits) : b*v.receiver.lanes≤h:=
    (paid b mem).trans (Nat.div_le_self ..)
  constructor <;> first | rw [a.donorLanes] | rw [a.probeLanes] | rw [a.newLanes]
  all_goals apply take
  case masked => exact Or.inr (by simp [receiverUnits])
  all_goals exact Or.inl (by simp [rootUnits])

private theorem arity_le (b z M h : ℕ) (hb : 0<b) (hm : 0<M) (paid : (b*z+b)*M≤h) : z≤h:=
  (Nat.le_mul_of_pos_left z hb).trans ((Nat.le_add_right ..).trans ((Nat.le_mul_of_pos_right _ hm).trans paid))

private theorem bounded_arity {f : ∀h,ι h→ℕ} (cap : ∀ᶠ h:ℕ in atTop,∀i,f h i≤h) : Bounded f:=
  ⟨1,cap.mono fun h levels i=>by simpa only [one_mul] using (levels i).trans (Nat.le_of_lt (Nat.lt_two_pow_self (n:=h)))⟩

/-- The list of bought root and receiver lookup widths supplies all three native
room certificates. The logarithm of the old raster is charged to its host/group footprint. -/
theorem scheduled_contact_rooms (dims : ContactDimensions p) (aligned : ∀h i,ContactAligned (p h i))
    (room : ∀ᶠ h:ℕ in atTop,∀i b,b∈(p h i).rootUnits ∨ b∈(p h i).receiverUnits→b*(p h i).receiver.lanes≤h/2) :
    DescentContactDonorFront.Shape.ScalarRoom (fun h i=>(p h i).front.donor) ∧
    DescentContactPreROM.Layout.ScalarRoom (fun h i=>(p h i).front.contact) ∧
    DescentContactOutputShape.Shape.ScalarRoom (fun h i=>(p h i).contactShape):=by
  have keys : ∀ᶠ h:ℕ in atTop,∀i,ContactWidths (p h i) h:=room.mono fun h r i=>contact_widths _ (aligned h i) _ (r i)
  have lanes:=dims.lanes.of_le (y:=fun h i=>(p h i).front.donor.batch) fun h i=>(aligned h i).donorLanes.le
  have board:=bounded_arity (keys.mono fun h pay i=>arity_le _ _ _ _ (aligned h i).inputField
    ((aligned h i).donorLanes.symm ▸ (aligned h i).lanes) (pay i).board)
  have opposite:=bounded_arity (keys.mono fun h pay i=>arity_le _ _ _ _ (aligned h i).inputField
    ((aligned h i).donorLanes.symm ▸ (aligned h i).lanes) (pay i).opposite)
  have old:=bounded_arity (keys.mono fun h pay i=>arity_le _ _ _ _ (aligned h i).probeField
    ((aligned h i).probeLanes.symm ▸ (aligned h i).lanes) (pay i).old)
  have donor : DescentContactDonorFront.Shape.ScalarRoom (fun h i=>(p h i).front.donor):=by
    refine ⟨dims.hosts,dims.oldGroups,lanes,dims.degree,dims.lows,dims.cap,board,opposite,1,?_⟩
    filter_upwards [keys] with h pay i
    let d:=(p h i).front.donor
    have halo : d.queryBits*d.batch+d.cargoBits*d.batch≤h:=by simpa only [Nat.add_mul] using (pay i).halo
    have positive : 0<d.batch:=(aligned h i).donorLanes.symm ▸ (aligned h i).lanes
    have plus : d.queryBits*d.batch+d.cargoBits≤h:=(Nat.add_le_add_left (Nat.le_mul_of_pos_right _ positive) _).trans halo
    simp only [Nat.one_mul]
    exact ⟨(pay i).board,(pay i).split,(pay i).opposite,(pay i).field,(Nat.le_add_right ..).trans halo,
      plus,(Nat.le_add_left ..).trans halo,(pay i).returned⟩
  have H:=dims.hosts.of_le (y:=fun h i=>(p h i).front.contact.hosts) fun h i=>(aligned h i).oldHosts.le
  have groups:=dims.oldGroups.of_le (y:=fun h i=>(p h i).front.contact.groups) fun h i=>(aligned h i).oldGroups.le
  have batch:=dims.lanes.of_le (y:=fun h i=>(p h i).front.contact.batch) fun h i=>(aligned h i).probeLanes.le
  have blocks:=dims.lows.of_le (y:=fun h i=>(p h i).sheets.blocks) fun h i=>(aligned h i).blocks.le
  have chunks_ : Bounded (fun h i=>chunks (p h i).front.contact.groups (p h i).front.contact.batch):=
    (groups.add batch).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  obtain ⟨K,raster⟩:=H.mul chunks_
  refine ⟨donor,?_,?_⟩
  · refine ⟨H,dims.shapes.of_le (fun h i=>(aligned h i).shapeCount.le),chunks_,
      dims.lows.of_le (fun h i=>(aligned h i).oldLows.le),dims.cap.of_le (fun h i=>(aligned h i).oldCap.le),
      dims.sockets.of_le (fun h i=>(aligned h i).contacts.le),old,⟨max 1 K,?_⟩,⟨1,?_⟩,⟨1,?_⟩⟩
    · filter_upwards [keys,raster] with h win count i
      apply max_le
      · exact (win i).old.trans (by simpa only [one_mul] using Nat.mul_le_mul_right h (le_max_left 1 K))
      · exact ((Nat.clog_le_iff_le_pow (by decide : 1<2)).2 (count i)).trans
          (Nat.mul_le_mul_right h (le_max_right 1 K))
    · exact keys.mono fun h win i=>by simpa only [Nat.mul_one,Nat.one_mul] using (win i).view
    · exact keys.mono fun h win i=>by simpa only [Nat.one_mul] using (win i).mark
  · refine ⟨donor,dims.sockets.of_le (fun h i=>(aligned h i).maskedContacts.le),dims.shapes,dims.newGroups,
      blocks,dims.lanes.of_le (fun h i=>(aligned h i).newLanes.le),1,?_⟩
    exact keys.mono fun h win i=>by simpa only [Nat.one_mul, contactShape] using And.intro (win i).marker ⟨(win i).meta,(win i).masked⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

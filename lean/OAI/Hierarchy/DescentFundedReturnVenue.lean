import OAI.Hierarchy.DescentFundedReturnShelves
import OAI.Hierarchy.DescentSignedVenueDensity
import OAI.Hierarchy.DescentIssuedOrdinaryVenuePitch
import OAI.Hierarchy.DescentTerminalWingPitch

namespace OAI
/-! # The three source pitches of the final venue publisher on the actual funded ordinary date -/
namespace Hierarchy.DescentSixParty
open DescentSIMDLookup DescentCompiler DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage.Dated
noncomputable section
set_option quotPrecheck false

namespace StageVenueTail.Date
variable (d : Date)

/-- The last roster uses one physical word per occupied host. -/
theorem last_rows {u h : ℕ} (pos : 0<d.groups) (covers : d.groups≤d.lanes) :
    d.hosts*chunks d.groups d.lanes*h≤d.hosts*h+d.hosts*d.groups*u :=by
  rw [covered_chunks pos covers,Nat.mul_one]
  exact Nat.le_add_right ..
end StageVenueTail.Date

namespace Chronology.PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)
variable (gain frozen p f priorM extra : ℕ) (orig : ℕ→Ordinary)
local notation "q" => SignedStage.atDate v.gadget v.schedule gain v.k v.age (NativePitch.incomingHosts v.schedule (v.age+1))
local notation "W" => v.withFundedArguments extra A
local notation "z" => (W).venue
local notation "h" => v.payload

theorem funded_venue_rows (u : ℕ)
    (date : v.venue=StageVenueTail.Date.atOrdinary v.gadget v.schedule gain v.k frozen p f h orig v.age priorM)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤v.area.unit)
    (wide : 4*v.fundedMaxUnit extra*(2^v.area.k)≤h)
    (signed : 2*(q).unit≤h) (su : 4*(q).unit≤u) (pu : (2^v.area.k)*v.fundedWorkingUnit extra≤u)
    (pos : 0<(z).lanes) (small : (z).lanes≤h/2) (next : (z).hosts*chunks (z).groups (z).lanes*h≤(z).hosts*h+(z).hosts*(z).groups*u) :
    (z).SourceRows h u :=by
  let x:=StageVenueTail.Date.atOrdinary v.gadget v.schedule gain v.k frozen p f h orig v.age priorM
  obtain ⟨sp,sf,sc,sb⟩:=StageVenueTail.Date.atOrdinary_signed_caps v.gadget v.schedule gain v.k frozen p f h orig v.age priorM signed
  have packs:=v.funded_argument_bounds extra A paid input wide
  have ss : (z).signedLanes=x.signedLanes:=by
    change v.venue.signedLanes = x.signedLanes
    exact congrArg StageVenueTail.Date.signedLanes date
  have sd : (z).degree=x.degree:=by
    change v.venue.degree = x.degree
    exact congrArg StageVenueTail.Date.degree date
  have sa : (z).cap=x.cap:=by
    change v.venue.cap = x.cap
    exact congrArg StageVenueTail.Date.cap date
  have alive : (z).aliveLanes=(z).paidLanes:=rfl
  have payFill : h≤(z).paidLanes*u:=packs.fill₂.trans (Nat.mul_le_mul_left _ pu)
  have signFill : h≤(z).signedLanes*u:=ss.symm ▸ sf.trans (Nat.mul_le_mul_left _ su)
  have grain : (z).paidBits≤(z).paidBits*2^v.area.k:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have paySmall : (z).paidBits*(z).paidLanes≤h/2:=(Nat.mul_le_mul_right _ grain).trans packs.outBits
  have laneSmall : (z).paidLanes≤h/2:=(Nat.le_mul_of_pos_left _ paid).trans paySmall
  refine ⟨⟨ss.symm ▸ sp,packs.out,alive.symm ▸ packs.out,pos⟩,?_,
    ⟨ss.symm ▸ sc.trans (Nat.div_le_self ..),laneSmall.trans (Nat.div_le_self ..),small⟩,
    ?_,paySmall,alive.symm ▸ laneSmall⟩
  · intro m hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with eq|eq|eq|eq
    · subst m;exact DescentDatedSeedStartup.chunk_work _ _ _ _ _ signFill
    · subst m;exact DescentDatedSeedStartup.chunk_work _ _ _ _ _ payFill
    · subst m;rw [alive];exact DescentDatedSeedStartup.chunk_work _ _ _ _ _ payFill
    · subst m;exact next
  · rw [sd,sa,ss]
    exact sb

end Chronology.PhysicalOrdinary
end
end Hierarchy.DescentSixParty

end OAI

import OAI.Hierarchy.DescentRegisteredWindow
import OAI.Hierarchy.DescentSeedChosenLayout

namespace OAI
/-! # The actual block width, paid precision and packed input pitch at each date -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedSeedStartup DescentCompiler DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree)

structure VenueFormat (S : AtomSchedule) (b : Menu n degree) (k i : ℕ) (pos : Position) : Prop where
  width : pos.ports.venue.k=k
  paid : pos.ports.venue.paidBits=S.censusBits b.p
  pitch : i<S.length→pos.ports.venue.lanes=NativePitch.incoming S k b.tail b.p b.f b.payload b.ordinary i

variable {cp p' : ℕ} (X : Catalyst.Approximation F cp p')
open DescentSIMDLookup DescentPackedWalsh
set_option quotPrecheck false
local notation "layout" base:arg wire:arg hist:arg => selectedLayout G S b.payload k b.tail b.gain b.p b.drift b.degreeLimit
  b.f (quota S.rounds) base (S.censusBits b.p) wire hist

theorem seed_venue_format (R H groups base wire hist Z roof : ℕ)
    (first : S.rounds≠0 → (b.ordinary 0).lanesAt=lanes b.payload (firstDonor G S b.gain k b.p)) :
    VenueFormat S b k 0 ⟨DatePorts.initial G b.op X R (layout base wire hist) k H groups b.payload Z,roof⟩ :=by
  refine ⟨rfl,rfl,?_⟩
  intro alive
  change venuePitch G S b.payload b.gain k b.tail b.p b.f (quota S.rounds)=_
  by_cases zero:S.rounds=0
  · simp [venuePitch,NativePitch.incoming,alive,zero,NativePitch.resetCut,firstPrecision]
  · have nz : 0≠S.rounds := Ne.symm zero
    simp [venuePitch, NativePitch.incoming, alive, zero, nz, first zero]

omit [Fintype P] in
theorem step_venue_format (i : ℕ) (e : RunTrace.Events traces i) (a : Position) (move : Move w)
    (hit : issued traces b i e a move) (old : VenueFormat S b k i a) : VenueFormat S b k (i+1) move.next :=by
  rcases e with ⟨c,e⟩
  cases e with
  | ordinary before t after eqn=>
    obtain ⟨pos,space,rfl⟩:=hit
    exact ⟨rfl,rfl,fun _=>rfl⟩
  | reset before z after eqn=>
    obtain ⟨cap,space,rfl⟩:=hit
    exact ⟨old.width,old.paid,fun _=>rfl⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI

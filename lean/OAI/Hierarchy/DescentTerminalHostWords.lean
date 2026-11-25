import OAI.Hierarchy.DescentTerminalSnapshotBitRoom
import OAI.Hierarchy.DescentTerminalPrivateWordRoom
import OAI.Hierarchy.DescentChosenExteriorHeadWidths
import OAI.Hierarchy.DescentWideSeedCalendarFee
import OAI.Hierarchy.DescentTerminalScheduleScale

namespace OAI
/-! # Physical payload and register widths for the original terminal stage host -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentPackedEpochShelves DescentSeedRoot Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

structure HostWordRoom (S : AtomSchedule) (k tail p j W h : ℕ) : Prop where
  height : 4≤h
  ratio : 3≤W
  wide : 3*h≤W*h
  seedWord : 2*digitsNeeded (S.firstWidth G.b p)≤h
  epochWord : 2*unit G.C≤h/2
  edgeWord : 2^j*S.firstWidth G.b p≤W*h
  seatsWord : S.batch+2*grain (h/2) G.C<2^(W*h)
  retainedWidth : j≤S.groupWidth k tail S.length+k
  replayPayload : (k*S.length+1)*2^(8+S.capGain*S.length)≤W*h
  batchFit : S.batch<2^(W*h)
  word : Nat.log 2 (NativeBranch.privateMax G S p)+1≤W*h

/-- The purchased census word has a concrete lower bound even when all printed
tables happen to be very small. The height cutoff is independent of the data. -/
theorem terminal_host_words (t f g reset τ B : ℕ) (large : 20≤B)
    (reserve : 2*localSocketRate G t g≤τ)
    (packing : 2*(localSocketRate G t g+(τ+groupRate G t f g reset+4))+Nat.clog 2 G.b*(t+1)≤B) :
    ∀ᶠ h : ℕ in atTop,∀ M W last : ℕ,2^h≤M→M≤(2^h)^2→(2*last+7)*h≤W*h→
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      HostWordRoom G S k (tail τ J) (headGrain G S k h) (headChunk G S) W h :=by
  have replayBudget : 2*(localSocketRate G t g+3)≤B:=by omega
  filter_upwards [eventually_ge_atTop (4+4*unit G.C),
    chosen_exterior_full_widths G t f g reset τ B large reserve packing,
    early_native_packing G t f g reset τ B large reserve packing,
    terminal_snapshot_bit_room G t f g reset τ B reserve replayBudget,
    terminal_private_word_room G t f g reset τ] with h height first copy carry meter
  intro M W last low high funds J S k
  let p:=headGrain G S k h
  let j:=headChunk G S
  let s:=S.firstWidth G.b p
  have age : J≤Nat.log 2 h:=Nat.div_le_self ..
  have positive : 0<h:=by omega
  have factor : 2*last+7≤W:=Nat.le_of_mul_le_mul_right funds positive
  have ratio : 3≤W:=by omega
  have wide:=Nat.mul_le_mul_right h ratio
  have bw : h≤W*h:=(by omega : h≤3*h).trans wide
  have digit : 16*digitsNeeded s≤h:=(first M).1
  have tile : 16*(2^j*s)≤h:=(copy M).2.2.2.1
  have size : s≤h:=(Nat.le_mul_of_pos_left _ (Nat.two_pow_pos j)).trans (by omega)
  have pack : grain (h/2) G.C≤h:=(Nat.div_le_self ..).trans (Nat.div_le_self ..)
  obtain ⟨counter,seats,batch⟩:=meter J M p _ (W*h) age low high size pack wide
  obtain ⟨replay,retained⟩:=carry M
  have seed : 2*digitsNeeded s≤h:=(Nat.mul_le_mul_right _ (by decide : 2≤16)).trans digit
  refine ⟨by omega,ratio,wide,seed,by omega,?_,seats,retained,?_,batch,counter⟩
  · change 2^j*s≤W*h
    omega
  · change 32*((k*S.length+1)*2^(8+S.capGain*S.length))≤h at replay
    omega

end Hierarchy.DescentSixParty.SeedNamed

end OAI

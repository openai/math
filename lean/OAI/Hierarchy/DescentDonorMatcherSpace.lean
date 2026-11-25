import OAI.Hierarchy.DescentCapCalendarPositive
import OAI.Hierarchy.DescentMatcherLaneWidths
import OAI.Hierarchy.DescentDatedDonorOutputs
import OAI.Hierarchy.DescentNamedDonorCode
import OAI.Hierarchy.DescentDatedOrdinaryAny
import OAI.Hierarchy.DescentCensusPrecision

namespace OAI
/-! # The original private and matching programs share one genuine packed lane width -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentPacking.PackedMatch DescentCompiler DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentRawCablePanel DescentSIMDLookup ProtocolRAM
noncomputable section

theorem dated_cap_pos {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (gain k i p : ℕ) :
    0<(atDate G S gain k i p).cap := by
  have hg:=G.paid
  have positive : 0<G.b:=by omega
  exact Nat.mul_pos (prefix_cap_pos G.b S.rounds gain S.height i positive) (by decide)

variable (d : DonorDate) (payload seats board : ℕ)
local notation "a" => d.schedule payload seats board
local notation "rad" => 2^d.exponent

theorem matcher_widths (cap : 0<d.cap) (boardFits : board≤rad) :
    Phase.recordWidth d.exponent board (2*d.cap)≤d.amount ∧
    rad+(d.exponent+3)≤d.amount ∧
    DescentSignedCableCodec.width d.degree d.cap≤d.amount ∧
    Gather.matchUnit d.matcher d.format.short rad d.degree (2*d.cap)≤d.amount ∧
    SixBirths.unit d.matcher≤d.amount :=
  matching_widths d.format d.exponent (DescentTerminalEpochBits.width d.colors) board d.amount rfl cap
    boardFits (le_max_left ..) ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..))

theorem matcher_space (input : Dated.Operands) (w floor : ℕ)
    (cap : 0<d.cap) (boardFits : board≤rad) (homes : 0<d.hosts)
    (lane : 2*d.amount≤payload) (embed : payload≤w)
    (ports : Accessible (input.ports d.degree) input.actors d.hosts d.groups (lanes payload d.amount) w floor)
    (signed : ∀(x : Fin rad) (j : Fin (2*d.cap)),(input.wire x.val j.val).Fits w floor ∧
      (a).rows≤(input.wire x.val j.val).size)
    (hubs : input.hubs.Fits w floor) (atoms : ∀x : Fin rad,(input.atoms x.val).Fits w floor)
    (last : (a).rotationEnd input.roster floor<2^w) : (a).Space input w floor := by
  obtain ⟨census,gates,cables,matcher,birth⟩:=d.matcher_widths board cap boardFits
  have live:=Nat.two_pow_pos d.exponent
  have inputMax : max 1 (max board (DescentSignedCableCodec.width d.degree d.cap))≤d.amount :=
    max_le (by omega) (max_le (by omega) cables)
  exact ⟨homes,census,inputMax,matcher,birth,lane,embed,ports,signed,hubs,atoms,last⟩

end
end Hierarchy.DescentSixParty.Chronology.DonorDate

end OAI

import OAI.Hierarchy.DescentPackedEpochShelfLayout

namespace OAI
/-! # The entire power-of-two original shelf lies in the retained input prefix -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileInstall
open ProtocolRAM
variable {Pin : Type}

theorem shelf_fits {grain lo index base w : ℕ} {ss : List (Source Pin)} (s : Shelf Pin)
    (present : s∈shelves grain lo index ss) (before : lo+extent grain ss≤base) (room : base<2^w) :
    (sourceBank s.base s.src.seats grain).Fits w base := by
  have placed_ := (placed grain lo index ss s present).2.trans before
  change s.base+2*DescentDyadicSpan.span (slots s.src.seats grain)≤base at placed_
  change 0<DescentDyadicSpan.span (slots s.src.seats grain) ∧
    DescentDyadicSpan.span (slots s.src.seats grain)<2^w ∧
    s.base+DescentDyadicSpan.span (slots s.src.seats grain)≤base
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

end Hierarchy.DescentPackedEpochShelves

end OAI

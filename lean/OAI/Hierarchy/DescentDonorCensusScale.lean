import OAI.Hierarchy.DescentMatcherCensusRoom
import OAI.Hierarchy.DescentPrivateDonorUniform

namespace OAI
/-! # The authentic native matcher pitch accommodates the current signed census field -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentSixParty Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem block_le_donor (k D cap b C pad : ℕ) : 2^k≤donorAmount k D cap b C pad := by
  let r:=2^k
  let short:=max (k+3) (Nat.clog 2 (D+1))
  let raw:=1+short*(r+(r*(2*cap)+D*r))
  have live : 0<short := (Nat.succ_pos _).trans_le (Nat.le_max_left (k+3) _)
  have row : r≤r+(r*(2*cap)+D*r):=Nat.le_add_right ..
  have data : r≤raw :=
    (row.trans (Nat.le_mul_of_pos_left _ live)).trans (Nat.le_add_left ..)
  unfold donorAmount AgeBound.laneAmount
  dsimp only
  apply le_trans _ (Nat.le_max_right _ _)
  apply le_trans _ (Nat.le_max_left _ _)
  change r≤1+raw+_+_
  exact (((data.trans (Nat.le_add_left ..)).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..))

theorem census_donor_amount (t f g reset B : ℕ) (positive : 0<B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀M tail p D cap : ℕ, p≤h →
        let S:=stageNumbers G t J f g reset M tail
        let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
        S.censusBits p≤donorAmount k D cap G.b G.C G.k := by
  filter_upwards [census_board_room G t f g reset B positive] with h board
  dsimp only
  intro M tail p D cap occupied
  exact (board M tail p occupied).trans (block_le_donor _ D cap G.b G.C G.k)

end Hierarchy.DescentCompiler.TerminalScale

end OAI

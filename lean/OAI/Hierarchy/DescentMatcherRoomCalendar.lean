import OAI.Hierarchy.DescentMatcherCensusRoom
import OAI.Hierarchy.DescentPrivateDonorActual
import OAI.Hierarchy.DescentIssuedPublicDonor

namespace OAI
/-! # The signed census, matched rows, and donor rows share one width at every date -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale Filter

noncomputable section
variable {F : Type} [Field F]

structure MatcherRoom (G : PoweredGadget F) (S : AtomSchedule) (k p h : ℕ) : Prop where
  census : S.censusBits p≤2^k
  groups : 0<S.baseGroups
  hosts (i : ℕ) : 0<S.hostSize i
  table (i : ℕ) : 2^(h/2)≤S.hostSize i
  packed {P : Type} {dim : ℕ} {bits : P→ℕ} {W : MarkedWorld F dim P bits}
      {u q ε : ℝ} {i z z' D D' wire hist : ℕ}
      {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
      {c : (T.result he).Choice} {nrm : Normalize ((T.result he).state c)}
      {target : Reached nrm.result G q ε S k (i+1) z' D' wire hist}
      (ticket : OrdinaryLink source he T c nrm target) :
      0<ticket.donorDate.amount ∧ 2*ticket.donorDate.amount≤h

theorem matcher_room_at (G : PoweredGadget F) (t f g reset e τ B : ℕ) (positive : 0<B)
    (big : 2*((2+hostRate t reset*(t+1)+
      ((donorRates G t f g reset).amount+(donorRates G t f g reset).work)+1+1)+5+e)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M p : ℕ, 2^h≤2*M → p≤h →
        MatcherRoom G (stageNumbers G t J f g reset M (tail τ J))
          (groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)) p h := by
  filter_upwards [census_board_room G t f g reset B positive,
    NativeBranch.dates_grain_room G t f g reset τ B,
    selected_word_room_at G t f g reset e τ B positive big] with h census dates widths
  dsimp only
  intro M p source grain
  let J:=Nat.log 2 h/(2*B)
  exact {
    census:=census M (tail τ J) p grain
    groups:=Nat.two_pow_pos _
    hosts:=fun i=>(dates M p i source grain).1
    table:=fun i=>(dates M p i source grain).2.1
    packed:=fun ticket=>widths M ticket }

end
end Hierarchy.DescentSixParty.Chronology

end OAI

import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentStemCoordinateBook

namespace OAI
/-! # Word room for the old host and both fallback coordinates on a named reset -/
namespace Hierarchy.DescentStemCoordinateBook.Shape
open DescentColonies
noncomputable section

theorem donor_bound (C : Shape) (μ : DescentGL.Layout C.dim) (axis : Fin 2) (x : Block C.fine)
    (l : Block C.residual) (band : Fin C.groups) :
    C.value μ axis.castSucc x l band ≤ max (2^C.residual) (2^C.fine) :=by
  fin_cases axis
  · let digit:=fun t : Block C.residual=>(C.original μ band x t).val/2^C.fine
    change ((Finset.univ.image digit).filter (·<digit l)).card≤_
    have dom : (Finset.univ.image digit).card≤2^C.residual:=by
      simpa using (Finset.card_image_le (f:=digit) (s:=Finset.univ))
    exact (Finset.card_le_card (Finset.filter_subset ..)).trans (dom.trans (Nat.le_max_left ..))
  · exact (Nat.mod_lt (C.original μ band x l).val (Nat.two_pow_pos C.fine)).le.trans (Nat.le_max_right ..)

end
end Hierarchy.DescentStemCoordinateBook.Shape

namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentCompiler DescentResetLocalRoster
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet : ℕ) (old : Prior) (base : ℕ)
local notation "out" => fromBoard G S board k tail age p f g drift degree payload e previous M nextM C packet old base
local notation "H" => GroupStage.depthBound old.venue.degree n f g
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "s" => CandidateSheets.fromBoard S board k tail age old.venue.degree f g cap M

/-- The public menu query already distinguishes more than twice the number of
low blocks. This gives strict room for every compressed group rank even at cap one. -/
theorem fromBoard_tree_caps (occupied : 0<cap) :
    2^k<2^(out).sheets.stemBits ∧
    2^k<2^(out).setup.fallbackBits ∧ (out).sheets.metaBits≤(out).setup.fallbackBits :=by
  have source:=CandidateSheets.stem_width S board k tail age old.venue.degree f g cap M
  have total:=CandidateSheets.roster S board k tail age old.venue.degree f g cap M
  have amount : 2^k≤2^k*(2*cap):=Nat.le_mul_of_pos_right _ (by omega)
  have scored : 2^k<2*(s).candidates+1:=by rw [total];omega
  have query : Nat.clog 2 (2*(s).candidates+1)≤(out).setup.fallbackBits:=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have metadataWidth : (s).metaBits≤(out).setup.fallbackBits:=
    (Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_left ..)))
  exact ⟨source.2.1,scored.trans_le ((Nat.le_pow_clog (by decide) _).trans
    (Nat.pow_le_pow_right (by decide) query)), metadataWidth⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

import OAI.Hierarchy.DescentNamedOriginalInputs
import OAI.Hierarchy.DescentResetLocalRosterPrice
import OAI.Hierarchy.DescentResetPublicDonorRead
import OAI.Hierarchy.DescentResetStemOriginalSlots

namespace OAI
/-! # The numerical original-cable chart identifies every actual reserved slot -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentResetLocalRoster DescentDatedAddressBook DescentResetPublicParentWord
open DescentResetCableSlots
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (M : ℕ)
local notation "sheet" => CandidateSheets.fromBoard S ctl.board k tail i D f g input.placement.cap M
local notation "a" => input.placement
local notation "height" => GroupStage.depthBound D n f g
local notation "N" => 2^k*(2*(a).cap)
local notation "J" => 2*N

theorem original_chart_shape : publicShape B=CandidateSheets.OriginalInputs.geometryFor ctl.board k D f g (a).cap:=by
  have old : S.groupWidth k tail i+k-B.terminals.commonDepth=k:=by rw [B.commonDepth];omega
  have dyadic : B.reset.k-B.terminals.commonDepth=k:=by rw [B.keyWidth,B.commonDepth];omega
  have board := same_count B.reset.graph ctl.board B.dimension B.graph height
  change Shape.mk ((a).degree+2) _ _ _ _ _ (programCount B.reset.graph height)=_
  rw [board,old,dyadic,input.branch,B.dimension]
  rfl

theorem original_stems_count : stemsCount B=J:=by
  unfold stemsCount
  rw [B.commonDepth]
  simp

theorem original_contacts_count : contactCount B=(sheet).contacts:=by
  unfold contactCount
  have dyadic : B.reset.k-B.terminals.commonDepth=k:=by rw [B.keyWidth,B.commonDepth];omega
  rw [dyadic,B.dimension]
  rfl

theorem original_private_count : privateCount B=(sheet).privates:=by
  have cc:=same_count B.reset.graph ctl.board B.dimension B.graph height
  have dyadic : B.reset.k-B.terminals.commonDepth=k:=by rw [B.keyWidth,B.commonDepth];omega
  change 2*(rootSlots (B.reset.k-B.terminals.commonDepth) (2^B.reset.n)*programCount B.reset.graph height)=_
  rw [cc,dyadic,B.dimension]
  rfl

/-- The numerical sector positions select the same parent as each original
stem, direct/trunk, or private-root publication. -/
theorem original_places :
    (∀j,(CandidateSheets.OriginalInputs.stemAt S ctl.board k tail i D f g (a).cap M (Fin.cast (original_stems_count B) j)).val=
      (stemShelf B j).val) ∧
    (∀j,(CandidateSheets.OriginalInputs.publicAt S ctl.board k tail i D f g (a).cap M
      (Fin.cast (congrArg (·+1) (original_contacts_count B M)) j)).val=(publicShelf B j).val) ∧
    (∀j,(CandidateSheets.OriginalInputs.privateAt S ctl.board k tail i D f g (a).cap M
      (Fin.cast (original_private_count B M) j)).val=(privateShelf B j).val) :=by
  refine ⟨fun _=>rfl,?_,?_⟩
  · intro j
    change J+j.val=stemsCount B+j.val
    rw [original_stems_count]
  · intro j
    change J+1+(sheet).contacts+j.val=stemsCount B+1+contactCount B+j.val
    rw [original_stems_count,original_contacts_count B M]

private theorem request_cast {m n : ℕ} (h : m=n) (j : Fin (2*m)) :
    CandidateSheets.OriginalInputs.requestAt n (Fin.cast (congrArg (fun slots=>2*slots) h) j)=
    CandidateSheets.OriginalInputs.requestAt m j:=by subst n;rfl

private theorem side_cast {m n : ℕ} (h : m=n) (c : ℕ) (j : Fin (2*(m*(2*c)))) :
    CandidateSheets.OriginalInputs.sideAt n c (Fin.cast (congrArg (fun slots=>2*(slots*(2*c))) h) j)=
    CandidateSheets.OriginalInputs.sideAt m c j:=by subst n;rfl

/-- A reached direct-contact lookup selects its measured source side and
the one-based local socket in precisely the same row as the dated compiler. -/
theorem original_request (j : Fin (contactCount B)) :
    CandidateSheets.OriginalInputs.requestAt (rootSlots k (2^n)*(2^n+2^height))
      (Fin.cast (original_contacts_count B M) j)=donor_query B j:=by
  have half : rootSlots (B.reset.k-B.terminals.commonDepth) (2^B.reset.n)*(2^B.reset.n+2^height)=
      rootSlots k (2^n)*(2^n+2^height):=by
    rw [B.keyWidth,B.commonDepth,B.dimension,Nat.add_sub_cancel_left]
  exact request_cast half j

/-- The prefix for the old incoming stems uses the same signed incidence
coordinate before and after assigning the final candidate slot. -/
theorem original_side (j : Fin (stemsCount B)) :
    CandidateSheets.OriginalInputs.sideAt (2^k) (a).cap
      (Fin.cast (original_stems_count B) j)=(stemTag B j).1:=by
  have width : 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)=2^k:=by rw [B.commonDepth];congr 1;omega
  exact side_cast width (a).cap j

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

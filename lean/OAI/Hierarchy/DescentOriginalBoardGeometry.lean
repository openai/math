import OAI.Hierarchy.DescentResetOriginalDonorMeasured
import OAI.Hierarchy.DescentPhysicalNamedOriginals
import OAI.Hierarchy.DescentResetPublicParentPosted
import OAI.Hierarchy.DescentCalendarMixedGeometry
import OAI.Hierarchy.DescentResetStemOriginalSlots

namespace OAI
/-! The seven entries of the numerical original-word law are the actual reached board dimensions. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentDatedAddressBook DescentCompiler DescentColonies DescentResetPublicParentWord DescentDenseHostOrder
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Ht" => GroupStage.depthBound D n f g
local notation "Z" => B.reset
local notation "r" => (Z).k-B.terminals.commonDepth
local notation "count" => 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)

theorem original_board_geometry {capacity : ℕ} (paid : input.placement.cap=capacity) :
    CandidateSheets.OriginalInputs.geometryFor ctl.board k D f g capacity=publicShape B:=by
  have prog:=same_count (Z).graph ctl.board B.dimension B.graph Ht
  have size : S.groupWidth k tail i+k-B.terminals.commonDepth=k:=by rw [B.commonDepth];omega
  unfold CandidateSheets.OriginalInputs.geometryFor publicShape
  rw [input.branch,calendar_residual B,paid,size]
  congr 1 <;> first | exact prog.symm | rw [B.dimension]

private theorem side_cast {L cap L' cap' : ℕ} (l : L=L') (c : cap=cap') (j : Fin (2*(L*(2*cap)))) :
    CandidateSheets.OriginalInputs.sideAt L' cap' (j.cast (by rw [l,c]))=
      ((DescentResetStemPackedIssue.ordinal L cap).symm j).1:=by
  subst L';subst cap';rfl

theorem original_stem_side {capacity : ℕ} (paid : input.placement.cap=capacity)
    (j : Fin (stemsCount B)) :
    CandidateSheets.OriginalInputs.sideAt (2^k) capacity (j.cast (by
      change 2*(count*(2*input.placement.cap))=_
      rw [B.commonDepth,paid];simp))=(stemTag B j).1:=by
  apply side_cast (cap:=input.placement.cap)
  · rw [B.commonDepth];simp
  · exact paid

private theorem original_fn_eq {d₀ d₁ n₀ n₁ : ℕ}
    (A₀ : NonlinearExpanders.Graph n₀ d₀) (A₁ : NonlinearExpanders.Graph n₁ d₁)
    (nEq : n₀=n₁) (dEq : d₀=d₁) (same : HEq A₀ A₁) (shape : Shape) (ht : ℕ) (mode : Fin 2) :
    (if mode=0 then trunkWord A₀ shape.halo shape.depth shape.span shape.cap shape.sockets shape.program ht
      else fun v z h j=>directWord shape ht v z (h-1) j)=
    (if mode=0 then trunkWord A₁ shape.halo shape.depth shape.span shape.cap shape.sockets shape.program ht
      else fun v z h j=>directWord shape ht v z (h-1) j):=by
  subst n₁;subst d₁;rw [eq_of_heq same]

theorem original_public_fn {s : CandidateSheets} (u : s.OriginalInputs) (base : ℕ)
    (geometry : u.geometry=publicShape B) (height : u.treeHeight=Ht)
    (nodes : u.boardBits=(Z).n) (arity : u.boardPorts=h) (same : HEq u.board (Z).graph) :
    (u.publicSide base).fn=publicFn B:=by
  funext mode
  unfold CandidateSheets.OriginalInputs.publicSide publicFn
  dsimp only
  rw [geometry,height]
  exact original_fn_eq _ _ nodes arity same _ _ mode

theorem original_donor_domain {capacity : ℕ} (paid : input.placement.cap=capacity) :
    (2^k)*(2*capacity)=count*(2*input.placement.cap):=by rw [paid,B.commonDepth];simp

theorem original_choices : originalChoices B=DescentResetLocalRoster.rootSlots k (2^n)*(2^n+2^Ht):=by
  change DescentResetLocalRoster.rootSlots r (2^(Z).n)*(2^(Z).n+2^Ht)=_
  rw [calendar_residual B,B.dimension]

private theorem request_cast {a b : ℕ} (h:a=b) (j:Fin (2*b)) :
    CandidateSheets.OriginalInputs.requestAt a (j.cast (by rw [h]))=
    CandidateSheets.OriginalInputs.requestAt b j:=by subst b;rfl

theorem original_donor_request (j : Fin (contactCount B)) :
    CandidateSheets.OriginalInputs.requestAt (DescentResetLocalRoster.rootSlots k (2^n)*(2^n+2^Ht))
      (j.cast (by change 2*(DescentResetLocalRoster.rootSlots r (2^(Z).n)*(2^(Z).n+2^Ht))=_
                  rw [calendar_residual B,B.dimension]))=donor_query B j:=by
  exact request_cast (original_choices B).symm j

theorem original_short_room {X : ℕ} (choices : originalChoices B≤X) (halo : D+2≤X) :
    (∀c,(Z).senderJoint B.terminals false c<2^Nat.clog 2 (X+1)) ∧
    ∀u c,haloNumber B u ((Z).rootVertex B.terminals ((Z).placement.owner false c))+1<2^Nat.clog 2 (X+1):=by
  have maxLt:X<2^Nat.clog 2 (X+1):=(Nat.lt_succ_self X).trans_le (Nat.le_pow_clog (by decide) _)
  refine ⟨fun c=>(original_joint_room B false c).trans_lt (choices.trans_lt maxLt),?_⟩
  intro u c
  have h:=haloNumber_room B u ((Z).rootVertex B.terminals ((Z).placement.owner false c))
  rw [input.branch] at h
  omega

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

import OAI.Hierarchy.DescentMixedPrivateRoots
import OAI.Hierarchy.DescentResetHeaderPlacement

namespace OAI
/-! # Private rotor and tree cables incident to a fixed post-reset receiver -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))

/-- The coarse block is recovered from the high and low public reset digits.
The physical host name remembers the input vertex of each private device. -/
def receiverRoot (u : Host) : (Z).V × Block (T).commonDepth :=
  (position (Z).graph u.1.2.val, (digits).symm (u.1.1,u.2))

abbrev PrivateOccurrence := Σr : Bool×(placement).Site, (dev (sel r.1 r.2)).Edge

def privateWire (x : PrivateOccurrence B) : (coarse).graph.Edge :=
  (Z).privateWireAt T x.1.1 x.1.2 x.2

def privateTicket (x : PrivateOccurrence B) :
    Bool × ResetInput.RootTicket Z T × Fin capacity :=
  (x.1.1,(Z).rootTicket T x.1.2,
    DescentResetCableSlots.privateWire placement height (T).bookHeight (Z).graph
      (Z).positive (Z).pay (Z).circuit d x.1 x.2)

theorem root_at_private_site (side : Bool) (g₀ : (placement).Site)
    (v : (dev (sel side g₀)).Site) :
    (position (Z).graph ((Z).placed T ((Z).privateSiteAt T side g₀ v)).val,
      (Z).blockId T ((Z).privateSiteAt T side g₀ v)) =
    ((Z).rootVertex T g₀,(Z).rootBlock T g₀) := by
  apply Prod.ext
  · change position (Z).graph ((Z).commonName T ((Z).privateSiteAt T side g₀ v)) = _
    have name := congrArg (rawName placement (Z).graph (T).commonDepth (T).code (Z).positive (Z).pay (Z).circuit d)
      (((Z).resetNames T).apply_symm_apply (.inr ⟨(side,g₀),v⟩))
    refine (congrArg (position (Z).graph) name).trans ?_
    cases g₀ <;> rfl
  · exact Fin.ext ((Z).private_block T side g₀ v)

theorem receiverRoot_site (v : (coarse).graph.Site) :
      receiverRoot B (((digits ((Z).blockId T v)).1,(Z).placed T v),(digits ((Z).blockId T v)).2) =
        (position (Z).graph ((Z).placed T v).val,(Z).blockId T v) := by
    change (_, (digits).symm (digits ((Z).blockId T v))) = _
    rw [Equiv.symm_apply_apply]

/-- Concrete bank attachments and both ends of every contact bridge are
dependent pairs over their physical side and placement root. -/
theorem root_at_bank_site (v : (Z).bank.Site) :
    let a := ((Z).resetNames T).symm (.inr v)
    (position (Z).graph ((Z).placed T a).val,(Z).blockId T a) =
      ((Z).rootVertex T v.1.2,(Z).rootBlock T v.1.2) := by
  rcases v with ⟨⟨s,g₀⟩,x⟩
  exact root_at_private_site B s g₀ x

theorem private_endpoint_roots (x : PrivateOccurrence B) :
    receiverRoot B ((blocks B).src (privateWire B x)) =
        ((Z).rootVertex T x.1.2,(Z).rootBlock T x.1.2) ∧
    receiverRoot B ((blocks B).dst (privateWire B x)) =
        ((Z).rootVertex T x.1.2,(Z).rootBlock T x.1.2) := by
  rcases x with ⟨⟨side,g₀⟩,e⟩
  let edge := (Z).privateWireAt T side g₀ e
  let board := dev (sel side g₀)
  have data := (Z).private_geometry T side g₀ e
  have source : (coarse).graph.src edge = (Z).privateSiteAt T side g₀ (board.src e) :=
    (Equiv.eq_symm_apply _).2 (congrArg RawFields.src data)
  have target : (coarse).graph.dst edge = (Z).privateSiteAt T side g₀ (board.dst e) :=
    (Equiv.eq_symm_apply _).2 (congrArg RawFields.dst data)
  let root (v : (coarse).graph.Site) := (position (Z).graph ((Z).placed T v).val,(Z).blockId T v)
  constructor
  · exact ((congrArg (receiverRoot B) (named_home B ((coarse).graph.src edge))).trans
      (receiverRoot_site B _)).trans ((congrArg root source).trans (root_at_private_site B side g₀ _))
  · exact ((congrArg (receiverRoot B) (named_home B ((coarse).graph.dst edge))).trans
      (receiverRoot_site B _)).trans ((congrArg root target).trans (root_at_private_site B side g₀ _))

theorem private_owner (u : Host) (x : PrivateOccurrence B)
    (atEnd : (blocks B).src (privateWire B x)=u ∨ (blocks B).dst (privateWire B x)=u) :
    receiverRoot B u=((Z).rootVertex T x.1.2,(Z).rootBlock T x.1.2) := by
  obtain ⟨left,right⟩ := private_endpoint_roots B x
  rcases atEnd with eqn | eqn
  · rwa [eqn] at left
  · rwa [eqn] at right

/-- At one receiver, side, relative root ticket and local cable slot identify the
same physical wire, whether the receiver occurs at its source or destination. -/
def private_local_chart (u : Host) :
    {x : PrivateOccurrence B // (blocks B).src (privateWire B x)=u ∨ (blocks B).dst (privateWire B x)=u}
      ↪ Bool × ResetInput.RootTicket Z T × Fin capacity where
  toFun x := privateTicket B x.val
  inj' := by
    rintro ⟨⟨⟨s₁,g₁⟩,e₁⟩,h₁⟩ ⟨⟨⟨s₂,g₂⟩,e₂⟩,h₂⟩ eqn
    have side : s₁=s₂ := congrArg Prod.fst eqn
    have ticket : (Z).rootTicket T g₁=(Z).rootTicket T g₂ := congrArg (fun x=>x.2.1) eqn
    have same := (private_owner B u _ h₁).symm.trans (private_owner B u _ h₂)
    have root : g₁=g₂ := by
      apply ((Z).rootLocation T vertexCode).injective
      exact Prod.ext (congrArg vertexCode (congrArg Prod.fst same))
        (Prod.ext (congrArg Prod.snd same) ticket)
    subst s₂
    subst g₂
    have edge : e₁=e₂ := (DescentResetCableSlots.privateWire placement height (T).bookHeight
      (Z).graph (Z).positive (Z).pay (Z).circuit d (s₁,g₁)).injective (congrArg (fun x=>x.2.2) eqn)
    cases edge
    rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

import OAI.Hierarchy.DescentResetPublicWordLookup
import OAI.Hierarchy.DescentContactSenderTicket
import OAI.Hierarchy.DescentContactCandidateShelf

namespace OAI
/-! # Actual directed endpoint shapes from short old root, socket and tree height -/
namespace Hierarchy.DescentResetPublicParentWord
open DescentResetLocalRoster DescentDenseHostOrder DescentCommonHost DescentContacts
open DescentSIMDLookup DescentSharedCableNames
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {n ports : ℕ} (board : NonlinearExpanders.Graph n ports)
local notation "Y"=>2^n
local notation "X"=>Node Unit (Unit×Endpoint Y) (DescentCommonPalette.rotor board).Site

/-- Fallback sockets with the same numerical leaf may have different depths.
The height comes from the same measured sender book which produced the leaf. -/
def shapeFrom (r : ℕ) (side : Bool) : Root r Y→ℕ→ℕ→Option X
  | .inl q,z,_=>if row : z<Y then some (.good side ((),q.val.2) ((DescentCommonPalette.rotor board).attach (⟨z,row⟩,true))) else none
  | .inr (q,p),z,depth=>if Y≤z then
      if fit : z-Y<2^depth then some (.fall side ((),q.val,p) (List.ofFn ((DescentRotor.bitWord depth).symm ⟨z-Y,fit⟩))) else none
    else none

def outputShape (r height : ℕ) (side : Bool) (sender depth : ℕ) : ℕ :=
  let s : Shape:=⟨0,r,Y,0,0,0,0⟩
  match unpack s height sender with
  | none=>0
  | some (q,z)=>match shapeFrom board r side q z depth with
    | none=>0
    | some rx=>if yes : rx∈roster board r height then (localRank board r height ⟨rx,yes⟩).val+1 else 0

theorem shape_read (r height : ℕ) (side : Bool) (q : Root r Y) (j : Fin (Y+2^height)) (depth : ℕ) (rx : ↥(roster board r height))
    (formed : shapeFrom board r side q j.val depth=some rx.val) :
    outputShape board r height side (send ⟨0,r,Y,0,0,0,0⟩ height q j) depth=(localRank board r height rx).val+1 :=by
  simp [outputShape,unpacked,formed,rx.property]

theorem blank_shape (r height : ℕ) (side : Bool) (depth : ℕ) : outputShape board r height side 0 depth=0:=by
  simp [outputShape,unpack]
end
end Hierarchy.DescentResetPublicParentWord

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetPublicParentWord DescentDenseHostOrder DescentCommonHost DescentContacts DescentChosenRouter DescentRelativeContacts
open DescentResetLocalRoster
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bw : P→ℕ} {A : MarkedWorld F d P bw}
  {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "R"=>Z.placement
local notation "Y"=>2^Z.n
local notation "r"=>Z.k-T.commonDepth
local notation "lab"=>fun t=>shortName T.commonDepth (T.code t)
local notation "sock"=>fun s c=>direct Z.graph s (linkSocket (R) lab T.commonDepth s c)

def contactDepth (s : Bool) : (R).Contact→ℕ
  | .inl _=>0
  | .inr c=>((R).fallbackBook s (fallEnd (R) s c)).height

theorem sender_shape (s : Bool) (c : (R).Contact) :
    shapeFrom Z.graph r s (Z.rootTicket T ((R).owner s c)) (Z.contactSlotWord T s c) (Z.contactDepth s c)=
      some (shape Z.graph (sock s c)):=by
  cases c with
  | inl p=>
    cases s <;>
      change (if ok : _<Y then some _ else none)=_ <;>
      rw [dite_eq_left (by apply Fin.isLt)] <;> rfl
  | inr p=>
    let sites:=fun side=>fallEnd (R) side p
    let tree:=fun side=>(R).fallbackBook side (sites side)
    let digits:=fun side=>(tree side).codes (fallLeg (R) side p)
    have leaf (side : Bool) :
        (Z).contactSlotWord T side (.inr p)=Y+(DescentRotor.bitWord (tree side).height (digits side)).val:=rfl
    have small (side : Bool) : (DescentRotor.bitWord (tree side).height (digits side)).val < 2^(Z.contactDepth side (.inr p)) :=
      (DescentRotor.bitWord (tree side).height (digits side)).isLt
    rw [leaf]
    cases s <;>
      change (if Y≤Y+_ then (if bound : Y+_-Y<_ then some _ else none) else none)=_ <;>
      rw [ite_eq_left (Nat.le_add_right _ _),Nat.add_sub_cancel_left,dite_eq_left (small _)] <;>
      simp [digits,tree,sites,DescentCommonHost.direct,linkSocket,fallSocket,shape,fallLabel]
    all_goals
      constructor
      · rfl
      · exact congrArg List.ofFn ((DescentRotor.bitWord _).symm_apply_apply _)

def senderJoint (s : Bool) (c : (R).Contact) : ℕ :=
  send ⟨0,r,Y,0,0,0,0⟩ Ht (Z.rootTicket T ((R).owner s c)) ⟨_,Z.contactSlotWord_lt T s c⟩

theorem joint_shape (s : Bool) (c : (R).Contact) :
    outputShape Z.graph r Ht s (Z.senderJoint T s c) (Z.contactDepth s c)=
      (localRank Z.graph r Ht ⟨shape Z.graph (sock s c),Z.contact_shape_member T s c⟩).val+1:=
  shape_read Z.graph r Ht s _ _ _ _ (Z.sender_shape T s c)

end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentResetPublicParentWord DescentDenseHostOrder DescentCommonHost
open DescentChosenRouter DescentRelativeContacts
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "old" => (Z).orderedReentry T (DescentOrderedReset.grains W B.count B.order)
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "lab"=>fun t=>shortName (T).commonDepth ((T).code t)
local notation "sock"=>fun side c=>direct (Z).graph side (linkSocket (R) lab (T).commonDepth side c)

theorem joint_endpoint (side : Bool) (c : (R).Contact) :
    let e:=contactParent B c
    let v:=if side then (blocks B).dst e else (blocks B).src e
    outputShape (Z).graph r Ht side ((Z).senderJoint T side c) ((Z).contactDepth side c)=relativeShape B v+1:=by
  intro e v
  rw [(Z).joint_shape T side c]
  apply congrArg (fun a : ℕ=>a+1)
  change (localRank (Z).graph r Ht _).val=(localRank (Z).graph r Ht ((Z).localShape T v.1.2)).val
  apply congrArg (fun a=>(localRank (Z).graph r Ht a).val)
  apply Subtype.ext
  change shape (Z).graph (sock side c)=shape (Z).graph v.1.2.val
  apply congrArg (shape (Z).graph)
  let shapeAt (u : (old).graph.Site) :=congrArg (fun (h : Host)=>h.1.2.val) (named_home B u)
  have rawFields:=(Z).contactFields T c
  cases side
  · exact (congrArg DescentResetTrunks.RawFields.src rawFields).symm.trans (shapeAt ((old).graph.src e)).symm
  · exact (congrArg DescentResetTrunks.RawFields.dst rawFields).symm.trans (shapeAt ((old).graph.dst e)).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

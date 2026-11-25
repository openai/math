import OAI.Hierarchy.DescentCalibratedResetChart
import OAI.Hierarchy.DescentDatedCandidateFrontRate
import OAI.Hierarchy.DescentPrivateMaskRate
import OAI.Hierarchy.DescentDatedSmallAddress

namespace OAI
/-! # Reusing the selected reset word size for peer queries and private operands -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentResetMixedWordRAM Filter
set_option quotPrecheck false
variable {ι : ℕ→Type*} (p : ∀h,ι h→ResetOutput)
local notation "F₀" => fun h i=>(p h i).front
local notation "S₀" => fun h i=>(p h i).sheets
abbrev Installed := ∀ᶠ h:ℕ in atTop,∀i b,
  b∈(p h i).rootUnits ∨ b∈(p h i).receiverUnits → b*(p h i).receiver.lanes≤h/2

structure PeerAxes (v : ResetOutput) : Prop where
  origin : v.front.oldLanes=v.receiver.lanes
  mask : v.front.peer.lanes=v.receiver.lanes
  evidence : v.front.peer.evidenceLanes=v.receiver.lanes
  numbered : v.sheets.lanes=v.receiver.lanes
  blocks : v.front.blocks=v.sheets.blocks
  width : v.front.metaBits=v.sheets.metaBits
  positive : 0<v.receiver.lanes

structure PeerDimensions : Prop where
  oldHosts : Bounded fun h i=>(F₀ h i).peer.oldHosts
  shapes : Bounded fun h i=>(F₀ h i).peer.shapes
  degree : Bounded fun h i=>(F₀ h i).peer.oldDegree
  evidence : Bounded fun h i=>(F₀ h i).peer.evidence
  groups : Bounded fun h i=>(F₀ h i).peer.groups
  lanes : Bounded fun h i=>(p h i).receiver.lanes
  oldGroups : Bounded fun h i=>(F₀ h i).oldGroups
  keys : Bounded fun h i=>(F₀ h i).oldKeysCount
  cap : Bounded fun h i=>(F₀ h i).wireCap
  tickets : Bounded fun h i=>(F₀ h i).oldTicketCount
  hosts : Bounded fun h i=>(F₀ h i).newHosts
  projections : Bounded fun h i=>(F₀ h i).projectionCount
  blocks : Bounded fun h i=>(F₀ h i).blocks
  signed : Bounded fun h i=>(F₀ h i).signedQueries

theorem projected_words (same : ∀h i,(p h i).PeerAxes) (dim : PeerDimensions p) (words : Installed p)
    (donor : DescentContactDonorFront.Shape.ScalarRoom (fun h i=>(F₀ h i).donor))
    (contacts : DescentContactPreROM.Layout.ScalarRoom (fun h i=>(F₀ h i).contact)) :
    CandidateFront.ScalarRoom (F₀) :=by
  have oldM : Bounded (fun h i=>(F₀ h i).oldLanes) :=dim.lanes.of_le fun h i=>(same h i).origin.le
  have M : Bounded (fun h i=>(F₀ h i).peer.lanes) :=dim.lanes.of_le fun h i=>(same h i).mask.le
  refine {
    oldHosts:=dim.oldHosts,shapes:=dim.shapes,degree:=dim.degree,evidence:=dim.evidence,groups:=dim.groups,
    lanes:=M,oldGroups:=dim.oldGroups,oldLanes:=oldM,oldKeys:=dim.keys,cap:=dim.cap,tickets:=dim.tickets,
    live:=dim.hosts,project:=dim.projections,blocks:=dim.blocks,signed:=dim.signed,donor:=donor,contact:=contacts,
    key0:=?_,key1:=?_,port:=?_,sign:=?_,peer:=?_,trunk:=?_,oldWord:=?_,newWord:=?_,
    «meta»:=?_,mux:=?_,joined:=?_} <;>
    refine ⟨1,?_⟩ <;> filter_upwards [words] with h allWords <;> intro i
  all_goals
    let v:=p h i
    have room (b:ℕ) (hit:b∈v.rootUnits ∨ b∈v.receiverUnits) : b*v.receiver.lanes≤h :=
      (allWords i b hit).trans (Nat.div_le_self ..)
    have hw:=same h i
    simp only [Nat.one_mul,hw.origin,hw.mask,hw.evidence,hw.blocks,hw.width]
  all_goals first
    | apply room; (solve | left; simp [v,rootUnits] | right; simp [v,receiverUnits])
    | have unit:=room (v.setup.rotorBits+1) (.inr (by simp [receiverUnits]))
      exact (Nat.le_mul_of_pos_left _ (by omega : 0<v.setup.rotorBits+1)).trans unit
    | have raw:=room (v.sheets.metaBits*7+v.sheets.metaBits) (.inr (by simp [receiverUnits]))
      exact (Nat.le_add_right _ _).trans ((Nat.le_mul_of_pos_right _ hw.positive).trans raw)

theorem private_words (same : ∀h i,(p h i).PeerAxes) (dim : PeerDimensions p) (words : Installed p)
    (group : ∀h i,(S₀ h i).groups=(F₀ h i).peer.groups)
    (keys : Bounded (fun h i=>(p h i).privateShape.keys)) :
    DescentPrivateMaskDeck.Shape.ScalarRoom (fun h i=>(p h i).privateShape) :=by
  refine {
    oldHosts:=dim.oldHosts,shapes:=dim.shapes,
    groups:=dim.groups.of_le (fun h i=>(group h i).le),
    blocks:=dim.blocks.of_le (fun h i=>(same h i).blocks.ge),
    oldBatch:=dim.lanes.of_le (fun h i=>(same h i).origin.le),batch:=dim.lanes.of_le (fun h i=>(same h i).numbered.le),
    cap:=dim.cap,keys:=keys,raw:=?_,«meta»:=?_,projected:=?_} <;>
    refine ⟨1,?_⟩ <;> filter_upwards [words] with h actual <;> intro i
  all_goals
    let v:=p h i
    have room (b:ℕ) (hit:b∈v.rootUnits ∨ b∈v.receiverUnits) : b*v.receiver.lanes≤h :=
      (actual i b hit).trans (Nat.div_le_self ..)
    have hw:=same h i
    simp only [privateShape,DescentPrivateMaskDeck.Shape.panels,hw.origin,hw.numbered,Nat.one_mul]
    apply room
    (solve | left; simp [v,rootUnits] | right; simp [v,receiverUnits])


end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

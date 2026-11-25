import OAI.Hierarchy.DescentResetStemMetadata

namespace OAI
/-! # The exact seven stem fields at every signed slot, including holes -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
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



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit


local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)


local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "R" => blocks B
local notation "rank" => (Z).rawHostRank T vertexCode
local notation "shapeId" => (Z).codeHost T vertexCode
local notation "lab" => DescentRelativeContacts.shortName c
local notation "End" => (old).graph.Edge

local notation "center" u:arg => (receiverRoot B u)
local notation "actor" u:arg => B.frame.host.symm (center u).1
local notation "rack" u:arg => (center u).2
local notation "site" s:arg j:arg => endSite A s (beforeStem B j)

def stemDonor (u : Host) (s : Bool) (at_ : Slot) :=
  atSlot A before S input.valid s (donor digitsIn B.frame.basis fits (actor u) (rack u) at_.1) at_.2

/-- The prior tape returns actual granular grain names, which differ from the
reset's stored grain indices only by transport along the recorded count. -/
def priorGrain : (old).graph.Edge≃Grain A :=
  Equiv.sigmaCongrRight (fun e=>finCongr (congrFun B.count_eq e))

def oldStemAt (u : Host) (s : Bool) (at_ : Slot) : Option (old).graph.Edge :=
  (stemDonor B u s at_).map (priorGrain B).symm

private theorem grain_at (u : Host) (s : Bool) (at_ : Slot) (j : End) :
    oldStemAt B u s at_=some j ↔ stemDonor B u s at_=some (beforeStem B j) := by
  cases got : stemDonor B u s at_ with
  | none=>simp [oldStemAt,got]
  | some a=>
    simp only [oldStemAt,got,Option.map_some,Option.some.injEq]
    exact (priorGrain B).symm_apply_eq

private theorem donor_coordinates (u : Host) (s : Bool) (slot : Slot) (a : Grain A)
    (found : stemDonor B u s slot=some a) :
    ((A).pos (endSite A s a)).2=actor u ∧
      group c (rearrange B.frame.basis (oldBlock digitsIn (Stage.home A (endSite A s a))))=(rack u).val := by
  have place:=(atSlot_iff A before S input.valid s _ slot.2 a).mp found
  have cell:=(port_fst A s a).symm.trans (congrArg Prod.fst place)
  refine ⟨congrArg (fun h:Stage.Host _ _ k=>h.1.2) cell,?_⟩
  rw [cell]
  have loc : rearrange B.frame.basis
      (oldBlock digitsIn (donor digitsIn B.frame.basis fits (actor u) (rack u) slot.1))=join fits (rack u) slot.1 := by
    simp [donor,oldBlock]
  rw [loc]
  exact congrArg Fin.val (DescentPlainTerminal.high_join fits (rack u) slot.1)

private theorem old_panel (u : Host) (s : Bool) (slot : Slot) :
    priorStemPanel B u s slot=stemDonor B u s slot := by
  change (stemDonor B u s slot).filter _=_
  cases haveOld : stemDonor B u s slot with
  | none=>rfl
  | some a=>
    have eligible:=donor_coordinates B u s slot a haveOld
    simp [Option.filter_some, eligible]

theorem donor_root (u : Host) (s : Bool) (slot : Slot) (j : End)
    (found : oldStemAt B u s slot=some j) :
    receiverRoot B ((R).src (stemParent B (s,j)))=receiverRoot B u := by
  have loc:=donor_coordinates B u s slot (beforeStem B j) ((grain_at B u s slot j).mp found)
  rw [beforeStem_end B] at loc
  have whole:=stem_receiver_root B s j
  rw [whole.1]
  refine Prod.ext ?_ (Fin.ext ?_)
  · exact (B.frame.homeHost _).trans ((congrArg B.frame.host loc.1).trans (Equiv.apply_symm_apply ..))
  · exact (B.frame.homeHigh _).trans loc.2

theorem stem_at_iff (u : Host) (s : Bool) (slot : Slot) (x : Local (R) u) :
    localOrigin B u (stemIndex B s slot)=some x ↔
      ∃j, x.val=stemParent B (s,j) ∧ oldStemAt B u s slot=some j := by
  rw [stem_slot_iff,old_panel]
  exact exists_congr (fun j=>and_congr_right (fun _=>(grain_at B u s slot j).symm))

/-- Zero-inclusive public endpoints on a native signed source, before applying
the receiver's positive-edge filter or reading its neighbour directory. -/
def stemPair (s : Bool) (j : End) : ℕ×ℕ :=
  let t:=(T).home (ends (old).graph s j)
  (shapeId (.trunk s (lab ((T).code t))),shapeId
    (DescentCommonHost.publicNode placement (Z).graph c (T).code s ((placement).input s j)))

theorem stem_read (u : Host) (s : Bool) (slot : Slot) :
    stemWord (rank u.1.2).val (stemNeighbors B u) s ((A).hub (actor u))
      ((oldStemAt B u s slot).map (stemPair B s)) =
      «meta» B u (localOrigin B u (stemIndex B s slot)) := by
  cases donorRead : oldStemAt B u s slot with
  | none=>
    have none : localOrigin B u (stemIndex B s slot)=none := by
      cases hit : localOrigin B u (stemIndex B s slot) with
      | none=>rfl
      | some x=>
        obtain ⟨_,_,same⟩:=(stem_at_iff B u s slot x).mp hit
        rw [donorRead] at same
        contradiction
    rw [none]
    rfl
  | some j=>
    let e:=stemParent B (s,j)
    have root:=donor_root B u s slot j donorRead
    have payload:=stem_word_at B u s j (congrArg Prod.snd root) (congrArg Prod.fst root)
    obtain ⟨start,stop,_,_⟩:=stem_fields_read B s j
    simp only [Option.map_some,stemPair,←start,←stop]
    rw [payload]
    split
    next live=>
      rw [(stem_at_iff B u s slot ⟨e,live⟩).mpr ⟨j,rfl,donorRead⟩]
    next dead=>
      cases hit : localOrigin B u (stemIndex B s slot) with
      | none=>rfl
      | some x=>
        obtain ⟨j',same,found⟩:=(stem_at_iff B u s slot x).mp hit
        have equal:=Option.some.inj (found.symm.trans donorRead)
        subst j'
        exact False.elim (dead (same ▸ x.property))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

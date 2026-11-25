import OAI.Hierarchy.DescentResetStemRead

namespace OAI
/-! # The small stem ticket addresses one shared descriptor per receiver -/
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

open DescentResetStemDecoder DescentRelativeContacts
local notation "Y" => 2^(Z).n
local notation "r" => (Z).k-c
local notation "use" => useRotor (placement).b (placement).depth (placement).L (placement).keys (placement).hub (placement).old
local notation "label" s:arg j:arg => lab ((T).code ((T).home (ends (old).graph s j)))

def stemTicket (s : Bool) (j : End) :=
  (DescentFallbackShapeTable.cell r (label s j).2,decide (use j))

/-- One entry is shared over all common blocks of a new receiver; its old
physical actor and its short shape are sufficient to reconstruct both hosts. -/
def stemTable (u : Host) (s : Bool) (ticket : Option (ℕ×Bool)) : Meta :=
  let host:=(center u).1
  let wires:=ticket.bind (fun key=>
    (nodes (Z).graph s host (DescentFallbackShapeTable.decode r Y key.1,key.2)).map
      (fun nodes=>(shapeId nodes.1,shapeId nodes.2)))
  stemWord (rank u.1.2).val (stemNeighbors B u) s ((A).hub (actor u)) wires

theorem stem_table_same (u v : Host) (host : u.1.2=v.1.2) (s : Bool) (ticket : Option (ℕ×Bool)) :
    stemTable B u s ticket=stemTable B v s ticket := by
  rcases u with ⟨⟨ug,uv⟩,ub⟩
  rcases v with ⟨⟨vg,vv⟩,vb⟩
  change uv=vv at host
  subst vv
  rfl

/-- Numerical address of a genuine input. This identity is upstream of the
neighbour scan. It also applies at nonincident receivers with the same root. -/
theorem stem_table_names (u : Host) (s : Bool) (slot : Slot) (j : End)
    (got : oldStemAt B u s slot=some j) :
    (nodes (Z).graph s (center u).1
      (DescentFallbackShapeTable.decode r Y (stemTicket B s j).1,(stemTicket B s j).2)).map
      (fun pair=>(shapeId pair.1,shapeId pair.2))=some (stemPair B s j) := by
  let t:=(T).home (ends (old).graph s j)
  have roots:=stem_receiver_root B s j
  have here : (center u).1=((T).code t).1 :=
    (congrArg Prod.fst (donor_root B u s slot j got)).symm.trans (congrArg Prod.fst roots.1)
  have bounds:=(T).codeLegal t
  have key : DescentFallbackShapeTable.decode r Y (stemTicket B s j).1=(label s j).2 :=
    DescentFallbackShapeTable.decode_cell _ _ (Nat.sub_le_sub_right bounds.2.1 _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  have origin:=DescentChosenRouter.public_read placement (T).code (T).source s j
  rw [←(T).attach] at origin
  have labelAt := congrArg (DescentRelativeContacts.shortName c) origin
  have side : ((placement).input s j).isLeft=(stemTicket B s j).2 := by
    by_cases paid : use j <;> simp [DescentChosenRouter.Placement.input,DescentChosenRouter.pub,stemTicket,paid]
  have yes:=nodes_public placement (Z).graph c (T).code s ((placement).input s j)
  dsimp only at yes
  rw [labelAt,side] at yes
  rw [key,here]
  exact congrArg (Option.map (fun pair=>(shapeId pair.1,shapeId pair.2))) yes

theorem stem_table_read (u : Host) (s : Bool) (slot : Slot) :
    stemTable B u s ((oldStemAt B u s slot).map (stemTicket B s))=
      «meta» B u (localOrigin B u (stemIndex B s slot)) := by
  rw [←stem_read]
  unfold stemTable
  cases got : oldStemAt B u s slot with
  | none=>rfl
  | some j=>
    simp only [Option.map_some,Option.bind_some,stem_table_names B u s slot j got]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

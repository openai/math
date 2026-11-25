import OAI.Hierarchy.DescentObservedPublicRotorRows
import OAI.Hierarchy.DescentMeasuredPublicBoard
import OAI.Hierarchy.DescentRotorActualAperture

namespace OAI
/-! # Recovering the unique original carrier at a physical public rotor socket -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open DescentRotorWindowScore DescentPackedTicketChronology DescentPacking
open DescentRotorWindowArchive DescentCanonicalPorts
open DescentPackedRotorMatrix DescentResetTrunks DescentPackedResetRotorRoles
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 800000
variable {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃Fin groups×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
local notation "native" => order.trans Fin.valEmbedding
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : Fin groups↪ℕ) (shortVertex : V↪Fin (Fintype.card V)) (padded : Fintype.card V ≤ H)
local notation "vertex" => (shortVertex.trans (Fin.castLEEmb padded))
local notation "ids" => (vertex).trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank groupKey ids)
local notation "c" => T.commonDepth
local notation "remain" => Z.k-c
local notation "Y" => 2^Z.n
local notation "L" => 2^(m-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "points" => Fin (L*(2*A.cap))
local notation "old" => Host (Fin groups) V k
local notation "here" => donor digits frm.basis fit
local notation "shelved" => signedPanel A native S ready names
local notation "short" => fun t=>shortName c (T.code t)
local notation "term" => fallbackCell A S ready digits Z T frm
local notation "bad" => exceptionalCell A S ready digits Z T frm
local notation "shape" => chartShape A S ready Z T
local notation "wireWord" => peerShapeWord A S ready digits Z T frm
local notation "arrive" => chartArrival A S ready native groupKey vertex
local notation "hostAt" => fun t=>frm.host.symm (T.code t).1
local notation "rootAt" => selectedRoot A S ready Z T
local notation "hs" => hostRoster A ids
local notation "ticketAt" => chartTicket A S ready digits native Z T frm groupKey vertex
local notation "rankAt" => leafRankAt A S ready Z T
variable (word : Host (Fin groups) V k → ℕ) (rank : Fin H→Fin (width (Z.k-T.commonDepth) (2^Z.n) A.degree)→Cell (Ht+2))


local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank
local notation "use" => useRotor Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old
local notation "endAt" => DescentIssuedFallbackPanel.endSite A
variable (room : ∀u,word u+1<2^field) (signBits : DescentSignedCableCodec.width A.degree A.cap≤field)
variable (onWire : ∀s : Bool, ∀e : Grain A,
  word (home A (DescentIssuedFallbackPanel.endSite A s e))=
    peerShapeWord A S ready digits Z T frm s (home A (DescentIssuedFallbackPanel.endSite A s e)))




variable (f B wire K : ℕ) (traffic : V→V→Block m→ℕ) (weight : V→Block m→ℕ)
variable (roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g frm ((shortVertex.trans (Fin.castLEEmb padded)).trans Fin.valEmbedding) A.near Z.n f B wire K (fun v z i=>(traffic v z i:ℝ)) A.degree weight)
local notation "slots" => previousPeers A S ready digits Z T frm vertex f B wire K traffic weight roster
local notation "hostFields" => peerData (a:=field) A S ready digits Z T frm vertex
local notation "chart" => rotorEntry A S ready digits native Z T frm groupKey vertex
local notation "oldKey" => DescentOrderedReset.grains W A.grainCount order
local notation "book" => T.columns
local notation "R" => Z.placement

local notation "board" => boardFor (field := field) A S ready digits order Z T frm groupKey vertex word rank
local notation "headAt" => base (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "bankV" => fun g : (R).Good=>frm.host.symm g.val.1
local notation "bankH" => fun g : (R).Good=>Z.rootBlock T (.inl g)
local notation "landing" => localAddress («c» := T.commonDepth) A native S ready digits frm.basis

variable (law : DonorOrder A digits) (sorted : SourceSorted W order) (tickets : Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order))
    (wide : max (max (Z.k-T.commonDepth) (2^Z.n)) (2^(Z.k-T.commonDepth))<2^field) (nWide : Z.n<field)

variable (model : DescentResetPublicOperandBook.Config)
local notation "sample" => ({model with residual:=remain,multiplicity:=C,packetWidth:=Z.width,gain:=f}:DescentResetPublicOperandBook.Config)
local notation "cfg" => matrixConfig sample A.degree A.cap L k field
variable (side : Bool) (root : Z.placement.Good)
local notation "src" => source R side root
local notation "dst" => target R side root
local notation "grains" => (Function.Embedding.subtype (fun e=>(R).owner side ((R).contact e)=.inl root))
local notation "chron" => (grains).trans oldKey
local notation "slot" => (physicalRoster A S ready digits order Z T frm side root).index
local notation "label" => Z.goodLabel T root
local notation "circuit" => Z.circuit side root
local notation "ord" => DescentRotor.Ordered.orderedAddress chron src dst Z.positive
variable (req : DescentRotorOperandQueryROM.Shape.Mouth Z.n)
    (x : (matrixConfig ({model with residual:=Z.k-T.commonDepth,multiplicity:=C,packetWidth:=Z.width,gain:=f} :
      DescentResetPublicOperandBook.Config) A.degree A.cap (2^(m-T.commonDepth)) k field).Data Z.n)
local notation:max "attached" e:arg => ((if req.pin then dst e else src e)=req.vertex ∧
  ((circuit).choose (ord e).1).val=req.layer ∧ (ord e).2.val=req.digit)
local notation "measured" => MeasuredPublicRows (r:=remain) A S ready digits frm.basis fit order groupKey shortVertex padded
  sample side (bankV root) (bankH root) x grains

private theorem carrier_of_occupied {E Location : Type} (eligible : E → Prop) (address : E → Location)
    [Decidable (∃ e, eligible e)] (value : Option Location)
    (occupied : ∀ e, eligible e → value = some (address e))
    (empty : (∀ e, ¬eligible e) → value = none) :
    value = if live : ∃ e, eligible e then some (address live.choose) else none := by
  split
  · next h => exact occupied h.choose h.choose_spec
  · next h => exact empty fun e yes => h ⟨e,yes⟩

private theorem map_covered {test : Prop} [Decidable test]
    {coveredResult : test → Prop} {missingResult : ¬test → Prop}
    {coveredConclusion : test → Prop} {missingConclusion : ¬test → Prop}
    (answer : dite test coveredResult missingResult)
    (onHit : ∀h,coveredResult h → coveredConclusion h)
    (onMiss : ∀h,missingResult h → missingConclusion h) : dite test coveredConclusion missingConclusion := by
  by_cases h : test
  · simpa only [dite_eq_left h] using onHit h (by simpa only [dite_eq_left h] using answer)
  · simpa only [dite_eq_right h] using onMiss h (by simpa only [dite_eq_right h] using answer)

include room signBits onWire roster law sorted tickets wide nWide in
/-- The true previous panel supplies the chronological key comparison as well as
its occupied, missing and measured traffic fields. -/
theorem observed_socket_support (obs : measured)
    (snapshot : (cfg).oldData x=board (bankV root) (bankH root))
    (indexed : ∀u,originalId W.graph.Site u=(A.site shortVertex ready.coordinates u).val) :
    (∀e,(cfg).endpoints side label x (slot e)=some (src e,dst e)) ∧
    (∀j,(¬∃e,slot e=j)→(cfg).endpoints side label x j=none) ∧
    (∀a b : Cells R side root,DescentFallbackItemSelect.before ((cfg).oldItem x side) (slot a) (slot b)↔chron a<chron b) ∧
    (cfg).traffic x side label=DescentBaseProfile.matrixOfBundles src dst :=by
  obtain ⟨known,missing,mass⟩:=observed_public_rotor_rows A S ready digits order Z T frm groupKey vertex word rank
    room signBits onWire f B wire K traffic weight roster law sorted tickets wide nWide sample side root x snapshot
  refine ⟨known,missing,?_,mass⟩
  intro a b
  exact public_operand_order A S ready digits frm.basis fit order groupKey shortVertex padded sample side (bankV root) (bankH root)
    x grains obs indexed sorted a b

include room signBits onWire roster law sorted tickets wide nWide in
/-- The carrier and its incident column measure are determined by the same installed
previous socket directory and comparison fields as the original rotor. -/
theorem observed_socket_carrier (obs : measured)
    (snapshot : (cfg).oldData x=board (bankV root) (bankH root))
    (indexed : ∀u,originalId W.graph.Site u=(A.site shortVertex ready.coordinates u).val)
    (depth : DescentRecordedRotorLayers.layers Z.n Z.width f (((cfg).reg x) 0).val= (circuit).layers) :
    ((cfg).carrier x side label req=if live : ∃e : Cells R side root,attached e then some (slot live.choose) else none) ∧
    ∀e : DescentRotorOperandRanks.At src dst (fun a=>(if req.pin then a.2 else a.1)=req.vertex),
      DescentFallbackItemSelect.rank ((cfg).oldItem x side) ((cfg).portRows x side label req) (slot e.val)=
        (Finset.univ.filter (fun j : DescentRotorOperandRanks.At src dst
          (fun a=>(if req.pin then a.2 else a.1)=req.vertex)=>chron j.val<chron e.val)).card ∧
      ((cfg).portRows x side label req).card=Fintype.card (DescentRotorOperandRanks.At src dst
        (fun a=>(if req.pin then a.2 else a.1)=req.vertex)) :=by
  obtain ⟨known,missing,earlier,mass⟩:=observed_socket_support A S ready digits order Z T frm groupKey shortVertex padded word rank
    room signBits onWire f B wire K traffic weight roster law sorted tickets wide nWide model side root x obs snapshot indexed
  constructor
  · apply carrier_of_occupied (fun e : Cells R side root=>attached e) (fun e=>slot e)
    · exact (cfg).carrier_old Z.graph circuit chron x side label req slot known missing earlier mass depth
    · exact (cfg).carrier_empty Z.graph circuit chron x side label req slot known missing earlier mass depth
  · exact (cfg).physical_port (x:=x) (side:=side) (root:=label) (req:=req) («slot»:=slot)
      (key:=chron) known missing earlier

local notation "fiber" => DescentRotorOperandRanks.At src dst (fun a=>(if req.pin then a.2 else a.1)=req.vertex)
local notation "prior" => DescentResetPublicOperandBook.Config.earlierCount src dst chron req
local notation "lo" => (cfg).oldConfig
local notation "records" => (cfg).oldItem x side

include room signBits onWire roster law sorted tickets wide nWide in
/-- The mixed dispatch itself, before any bounded packet field is projected. -/
theorem issued_public_mixed (obs : measured)
    (own : ∀v hi j,obs.own (vertex v) hi j=word (here v hi j))
    (near : ∀v j,obs.peers (vertex v) j=(hs v j).map vertex)
    (ranked : ∀v j,obs.ranks (vertex v) j=(rank (vertex v) j).val)
    (comparison : ∀v hi,obs.comparison (vertex v) hi=previousDigit frm.basis fit hi)
    (paid : ∀v j l s,obs.reserved (vertex v) j l s=hostFields v j l s)
    (indexed : ∀u,originalId W.graph.Site u=(A.site shortVertex ready.coordinates u).val)
    (depth : DescentRecordedRotorLayers.layers Z.n Z.width f (((cfg).reg x) 0).val= (circuit).layers)
    (arg : Fin (lo).args) (node : Fin (lo).nodes)
    (active : ((lo).header ((cfg).basic x) 0).val≠0)
    (port : (cfg).rotor.public_selector Z.graph C (cfg).grain node.val arg.val ((cfg).reg x)=some (side,label,req))
    (e : Cells R side root) (selected : attached e) (positive : 0<(cfg).batches) :
    let first:=prior e*(cfg).batches+req.batch
    let amount:=min 2 (Fintype.card fiber*(cfg).batches-first)
    let pos:=first+req.within
    if _covered : req.within<amount then
      ∃ donor : fiber,prior donor.val=pos/(cfg).batches ∧
        (∀other : fiber,prior other.val=pos/(cfg).batches→ other=donor) ∧
        (cfg).mixed Z.graph node.val arg.val x=some
          (if req.pin then (cfg).rotorContactAt side (((cfg).reg x) 0).val label req.vertex
           else (lo).stemAt side (((cfg).reg x) 0).val (records (slot donor.val)),
           if req.pin then pos else pos%(cfg).batches,amount,req.pin)
    else (cfg).mixed Z.graph node.val arg.val x=none :=by
  have snapshot := measured_public_board A S ready digits order Z T frm groupKey shortVertex padded
    word rank f model side root x obs own near ranked comparison paid
  obtain ⟨known,missing,earlier,mass⟩:=observed_socket_support A S ready digits order Z T frm groupKey shortVertex padded word rank
    room signBits onWire f B wire K traffic weight roster law sorted tickets wide nWide model side root x obs snapshot indexed
  have returned:=(cfg).public_word Z.graph circuit chron x side label req slot known missing earlier mass depth e selected positive
  have dispatch:=(cfg).public_dispatch Z.graph node.val arg.val x side label req active port
  let answers (value : Option (ℕ×ℕ×ℕ×Bool)) : Prop :=
    let first:=prior e*(cfg).batches+req.batch
    let amount:=min 2 (Fintype.card fiber*(cfg).batches-first)
    let pos:=first+req.within
    if _covered : req.within<amount then
      ∃ donor : fiber,prior donor.val=pos/(cfg).batches ∧
        (∀other : fiber,prior other.val=pos/(cfg).batches→ other=donor) ∧
        value=some
          (if req.pin then (cfg).rotorContactAt side (((cfg).reg x) 0).val label req.vertex
           else (lo).stemAt side (((cfg).reg x) 0).val (records (slot donor.val)),
           if req.pin then pos else pos%(cfg).batches,amount,req.pin)
    else value=none
  exact Eq.mp (congrArg answers dispatch.symm) returned

include room signBits onWire roster law sorted tickets wide nWide in
/-- The original prepared-board columns determine all eight public operand pages.
The donor of a covered word is unique both on a public contact and on an old stem. -/
theorem issued_public_word (obs : measured)
    (own : ∀v hi j,obs.own (vertex v) hi j=word (here v hi j))
    (near : ∀v j,obs.peers (vertex v) j=(hs v j).map vertex)
    (ranked : ∀v j,obs.ranks (vertex v) j=(rank (vertex v) j).val)
    (comparison : ∀v hi,obs.comparison (vertex v) hi=previousDigit frm.basis fit hi)
    (paid : ∀v j l s,obs.reserved (vertex v) j l s=hostFields v j l s)
    (indexed : ∀u,originalId W.graph.Site u=(A.site shortVertex ready.coordinates u).val)
    (depth : DescentRecordedRotorLayers.layers Z.n Z.width f (((cfg).reg x) 0).val= (circuit).layers)
    (arg : Fin (lo).args) (node : Fin (lo).nodes) (outBits : ℕ)
    (active : ((lo).header ((cfg).basic x) 0).val≠0)
    (port : (cfg).rotor.public_selector Z.graph C (cfg).grain node.val arg.val ((cfg).reg x)=some (side,label,req))
    (e : Cells R side root) (selected : attached e) (positive : 0<(cfg).batches) :
    let first:=prior e*(cfg).batches+req.batch
    let amount:=min 2 (Fintype.card fiber*(cfg).batches-first)
    let pos:=first+req.within
    let address:=finProdFinEquiv (arg,node)
    if _covered : req.within<amount then
      ∃ donor : fiber,prior donor.val=pos/(cfg).batches ∧
        (∀other : fiber,prior other.val=pos/(cfg).batches→ other=donor) ∧
        let q:=if req.pin then (cfg).rotorContactAt side (((cfg).reg x) 0).val label req.vertex
          else (lo).stemAt side (((cfg).reg x) 0).val (records (slot donor.val))
        let word:=if req.pin then pos else pos%(cfg).batches
        (cfg).column Z.graph outBits none address x=(q:ℕ) ∧ ∀t:Fin 7,
          (cfg).column Z.graph outBits (some t) address x=
            ((![0,0,if req.pin then word/(cfg).split else 0,
              if req.pin then word%(cfg).split else word,0,1,amount] t:ℕ):Cell outBits)
    else ∀field,(cfg).column Z.graph outBits field address x=0 :=by
  have returned := issued_public_mixed A S ready digits order Z T frm groupKey shortVertex padded
    word rank room signBits onWire f B wire K traffic weight roster law sorted tickets wide nWide
    model side root req x obs own near ranked comparison paid indexed depth arg node active port e selected positive
  let first := prior e*(cfg).batches+req.batch
  let amount := min 2 (Fintype.card fiber*(cfg).batches-first)
  refine map_covered (test:=req.within < amount) returned ?_ ?_
  · rintro _ ⟨donor,rankedWord,unique,answer⟩
    exact ⟨donor,rankedWord,unique,(cfg).column_at Z.graph outBits x arg node _ _ _ _ answer⟩
  · intro _ empty
    exact (cfg).column_empty Z.graph outBits x arg node empty

end
end Hierarchy.DescentSixParty.GroupStage

end OAI

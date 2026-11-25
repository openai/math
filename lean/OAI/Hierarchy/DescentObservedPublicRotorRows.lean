import OAI.Hierarchy.DescentRotorInstalledMatrix
import OAI.Hierarchy.DescentMeasuredPublicOrder

namespace OAI
/-! # Exact public-tap socket and traffic reads from the original measured rotor inputs -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentPackedRotorMatrix DescentResetLocalRoster
noncomputable section

theorem endpoints_empty (C : Config) {n : ℕ} (side : Bool) (root : code C.residual) (x : C.Data n)
    (j : Fin C.oldConfig.count)
    (absent : DescentRotorWindowArchive.pairCode (n:=n) (r:=C.residual) side root.val (C.oldData x)
      (finProdFinEquiv.symm j)=0) : C.endpoints side root x j=none :=by
  have empty : ¬∃p : Fin (2^n)×Fin (2^n),pair p.1 p.2=
        DescentRotorWindowArchive.pairCode (n:=n) (r:=C.residual) side root.val (C.oldData x) (finProdFinEquiv.symm j):=by
    rintro ⟨p,same⟩
    exact pair_nonzero _ _ (same.trans absent)
  rw [endpoints,dite_eq_right empty]

end
end Hierarchy.DescentResetPublicOperandBook.Config

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
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
local notation "native" => order.trans Fin.valEmbedding
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank groupKey ids)
local notation "c" => T.commonDepth
local notation "remain" => Z.k-c
local notation "Y" => 2^Z.n
local notation "L" => 2^(m-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "points" => Fin (L*(2*A.cap))
local notation "old" => Host J V k
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
variable (word : Host J V k → ℕ) (rank : Fin H→Fin (width (Z.k-T.commonDepth) (2^Z.n) A.degree)→Cell (Ht+2))


local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank
local notation "use" => useRotor Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old
local notation "endAt" => DescentIssuedFallbackPanel.endSite A
variable (room : ∀u,word u+1<2^field) (signBits : DescentSignedCableCodec.width A.degree A.cap≤field)
variable (onWire : ∀s : Bool, ∀e : Grain A,
  word (home A (DescentIssuedFallbackPanel.endSite A s e))=
    peerShapeWord A S ready digits Z T frm s (home A (DescentIssuedFallbackPanel.endSite A s e)))




variable (f B wire K : ℕ) (traffic : V→V→Block m→ℕ) (weight : V→Block m→ℕ)
variable (roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (vertex.trans Fin.valEmbedding) A.near Z.n f B wire K (fun v z i=>(traffic v z i:ℝ)) A.degree weight)
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

local notation:max "cfg" model:arg => matrixConfig
  ({model with residual:=remain} : DescentResetPublicOperandBook.Config) A.degree A.cap L k field

include room signBits onWire roster law sorted tickets wide nWide in
/-- Both support and column mass come from the original measured matrix, with zero on every gap. -/
theorem observed_public_rotor_rows (sample : DescentResetPublicOperandBook.Config) (side : Bool) (root : (R).Good)
    (x : (cfg sample).Data Z.n)
    (snapshot : (cfg sample).oldData x=board (bankV root) (bankH root)) :
    let directory:=physicalRoster A S ready digits order Z T frm side root
    let label:=Z.goodLabel T root
    (∀e,(cfg sample).endpoints side label x (directory.index e)=some (source R side root e,target R side root e)) ∧
    (∀j,(¬∃e,directory.index e=j)→(cfg sample).endpoints side label x j=none) ∧
    (cfg sample).traffic x side label=DescentBaseProfile.matrixOfBundles (source R side root) (target R side root) :=by
  intro directory label
  have support:=all_pairs A S ready digits order Z T frm groupKey vertex word rank room signBits onWire
    f B wire K traffic weight roster law sorted tickets wide nWide side root
  constructor
  · intro e
    apply (cfg sample).endpoints_read
    rw [snapshot]
    exact (congrFun support (directory.index e)).trans (physical_at R side root directory e)
  constructor
  · intro j absent
    apply (cfg sample).endpoints_empty
    rw [snapshot]
    apply (congrFun support j).trans
    unfold DescentPackedRotorMatrix.physical
    exact dite_eq_right absent
  · funext j k
    unfold DescentResetPublicOperandBook.Config.traffic
    rw [snapshot]
    exact installed_matrix A S ready digits order Z T frm groupKey vertex word rank room signBits onWire
      f B wire K traffic weight roster law sorted tickets wide nWide side root j k

end
end Hierarchy.DescentSixParty.GroupStage

end OAI

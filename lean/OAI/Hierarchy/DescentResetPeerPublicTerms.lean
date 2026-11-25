import OAI.Hierarchy.DescentResetPeerOperands

namespace OAI
/-! # Compiling physical reset peer operands from public date dimensions -/
namespace Hierarchy.DescentResetPeerUnionRAM.PeerCatalog
open DescentSIMDLookup DescentResetLocalRoster DescentDyadicSpan ProtocolRAM
open scoped Classical
noncomputable section
variable (L : RawTables.Layout) (A : DescentContactPreROM.Layout)

/-- Original array locations, with one static page for every possible root and signed donor. -/
structure Banks where
  keys : Fin A.donors→Bank
  pages : Bool→Root A.residual (2^A.n)→Bank
  actorStarts : Bank
  actorData : Bank

def privateAxis := 2*(rootSlots A.residual (2^A.n)*L.privateSlots)

def terms (old : Banks A) :
    Axes.Fields A.donors A.sockets (privateAxis L A) (Fin (chunks A.groups A.batch)→Expr) where
  stem j c:=RawTables.stemOperand L (finTwoEquiv (finProdFinEquiv.symm j).1)
    (PrivateEvidence.atOld L.base L.hosts L.shapes (old.keys j) c.val)
  trunk c:=.lookup ⟨L.trunk+span (L.hosts*L.shapes),Nat.clog 2 (L.shapes*2^L.lanes)⟩
    (.op .add (.lookup ⟨L.trunk,Nat.clog 2 (L.hosts*L.shapes)⟩ .row)
      (RawTables.actorOperand old.actorStarts old.actorData c.val))
  contact j donor c:=DescentContactProbePitch.atChunk A.hosts A.shapes A.groups A.batch A.fieldBits
    A.pitchBase c (.lookup (A.output (A.index j donor).val) .row)
  privateEdge j c:=if use : ∃p,localPrivateId A.residual (2^A.n) L.privateSlots p=j then
    let p:=use.choose
    PrivateEvidence.operand L.base L.hosts L.shapes L.privateSlots L.privateBits L.lanes
      (old.pages p.1 p.2.1) p.2.2 c.val
    else .lit 0

end
end Hierarchy.DescentResetPeerUnionRAM.PeerCatalog

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentGroupPeerOrder
open DescentPackedColony DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "J" => 2^(T).commonDepth
local notation "D₀" => input.placement.degree
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Slot" => Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*input.placement.cap)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)

variable (base H M field keyBits bits contactBits contactStart : ℕ) (old : PeerInputs B)
local notation "L" => peerLayout B base H M field keyBits bits
local notation "A" => contactLayout B contactStart H M contactBits bits

theorem peerTerms_public : peerTerms B base H M field keyBits bits contactBits contactStart old=
    PeerCatalog.terms L A ⟨old.keys,old.privatePages,old.actorStarts,old.actorData⟩ := by
  let inputs : PeerCatalog.Banks A := ⟨old.keys,old.privatePages,old.actorStarts,old.actorData⟩
  let actual := peerTerms B base H M field keyBits bits contactBits contactStart old
  let catalog := PeerCatalog.terms L A inputs
  have pages : actual.privateEdge = catalog.privateEdge := by
    funext j c
    let ix := DescentResetLocalRoster.localPrivateId (A).residual (2^(A).n) (L).privateSlots
    by_cases found : ∃p,privateProbeId B p=j
    · obtain ⟨p,rfl⟩ := found
      have left : ∃q,privateProbeId B q=privateProbeId B p := ⟨p,rfl⟩
      have right : ∃q,ix q=privateProbeId B p := ⟨p,rfl⟩
      have sameL := (privateProbeId B).injective left.choose_spec
      have sameR : right.choose=p := ix.injective right.choose_spec
      dsimp only [ix] at right sameR
      simp only [actual,catalog,peerTerms,PeerCatalog.terms,dite_eq_left left,dite_eq_left right,sameL,sameR]
      rfl
    · have gone : ¬ ∃q,ix q=j := found
      dsimp only [ix] at gone
      simp only [actual,catalog,peerTerms,PeerCatalog.terms,dite_eq_right found,dite_eq_right gone]
  exact congrArg (fun row => Axes.Fields.mk actual.stem actual.trunk actual.contact row) pages

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

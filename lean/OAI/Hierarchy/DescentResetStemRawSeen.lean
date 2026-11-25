import OAI.Hierarchy.DescentResetStemTicketBook
import OAI.Hierarchy.DescentResetPeerFamilySupport

namespace OAI
/-! # The raw stem evidence occurs in an actual signed slot at one common block -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open private Hierarchy.DescentSixParty.ClosedReset.Window.old_panel
  Hierarchy.DescentSixParty.ClosedReset.Window.grain_at
  from OAI.Hierarchy.DescentResetStemRead
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k

local notation "grainWorld" => W.granular B.count (z*G.b) B.fit

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "rank" => (Z).rawHostRank T vertexCode
local notation "End" => (grainWorld).graph.Edge

open DescentResetStemDecoder DescentRelativeContacts

def eitherDirection (v x : ℕ) (pair : ℕ×ℕ) :=
  (pair.1=v ∧ pair.2=x) ∨ (pair.2=v ∧ pair.1=x)

private theorem raw_endpoints (e : (B.reset.orderedReentry B.terminals (DescentOrderedReset.grains W B.count B.order)).graph.Edge) (v x : ℕ) :
    rawPeer B e v x ↔ eitherDirection v x ((rank ((blocks B).src e).1.2).val,(rank ((blocks B).dst e).1.2).val) := by
  let row := B.reset.actualRecord B.terminals (B.frame.host.symm.toEmbedding.trans input.vertex) e
  have src : (rank ((blocks B).src e).1.2).val = row 1 := (signed_header B e false).2.1
  have dst : (rank ((blocks B).dst e).1.2).val = row 2 := (signed_header B e true).2.1
  change row 0=1 ∧ _ ↔ _
  exact (and_iff_right ((signed_header B e false).1)).trans
    (show eitherDirection v x (row 1,row 2) ↔ eitherDirection v x _ by rw [src,dst])

theorem stem_raw_pair (s : Bool) (j : End) (v x : ℕ) :
    rawPeer B (stemParent B (s,j)) v x ↔ eitherDirection v x (stemPair B s j) := by
  have endpoint := stem_fields_read B s j
  exact (raw_endpoints B _ v x).trans (by
    unfold stemPair
    rw [endpoint.1,endpoint.2.1])

theorem donor_at_physical_endpoint (s : Bool) (j : End) (u : Host)
    (atCell : (blocks B).src (stemParent B (s,j))=u ∨ (blocks B).dst (stemParent B (s,j))=u) :
    oldStemAt B u s (priorStemSlot B s j)=some j := by
  apply (Hierarchy.DescentSixParty.ClosedReset.Window.grain_at B u s _ j).2
  rw [←Hierarchy.DescentSixParty.ClosedReset.Window.old_panel]
  exact priorStemPanel_read B u s j atCell

/-- Every raw stem lies at one of the previous signed rows of its receiver's underlying
vertex; the witness uses its physical group and slot, including when its two endpoints agree. -/
theorem stem_raw_seen (v : B.next.V) (x : ℕ) :
    (∃u : Host, ∃s slot j,u.1.2=v ∧ oldStemAt B u s slot=some j ∧
      eitherDirection (rank v).val x (stemPair B s j)) ↔
    ∃t,rawPeer B (stemParent B t) (rank v).val x := by
  constructor
  · rintro ⟨_,s,_,j,_,_,edge⟩
    exact ⟨(s,j),(stem_raw_pair B s j _ _).2 edge⟩
  · rintro ⟨⟨s,j⟩,hit⟩
    let e:=stemParent B (s,j)
    have pair:=(stem_raw_pair B s j _ _).1 hit
    have make (u : Host) (eqn : (rank u.1.2).val=(rank v).val)
        (atCell : (blocks B).src e=u ∨ (blocks B).dst e=u) :
        ∃u : Host, ∃s slot j,u.1.2=v ∧ oldStemAt B u s slot=some j ∧
          eitherDirection (rank v).val x (stemPair B s j) :=
      ⟨u,s,priorStemSlot B s j,j,(rank).injective (Fin.ext eqn),donor_at_physical_endpoint B s j u atCell,pair⟩
    rcases (raw_endpoints B e (rank v).val x).mp hit with h|h
    · exact make _ h.1 (.inl rfl)
    · exact make _ h.1 (.inr rfl)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

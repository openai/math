import OAI.Hierarchy.DescentObservedPublicRotorRows
import OAI.Hierarchy.DescentPreparedRotorInputs

namespace OAI
/-! # The state published by the preceding matrix gather supplies the public rotor board -/
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
set_option maxHeartbeats 1600000
/-- Pointwise identification of the preceding packet with the row sampled by the
public rotor. Only addresses occupied by old hosts enter the statement. -/
theorem issued_padded_board
    {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
    (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)
    (groupKey : Fin groups↪ℕ) (shortVertex : V↪Fin (Fintype.card V)) (padded : Fintype.card V≤H)
    (word : Host (Fin groups) V k → ℕ)
    (rank : Fin H → Fin (width (Z.k-T.commonDepth) (2^Z.n) A.degree) → Cell (Ht+2))
    (stencil : Fin H→Block T.commonDepth→Fin (2^(m-T.commonDepth))→ℕ) (peers : Fin H→Fin A.degree→Option (Fin H))
    (marks : Fin H→Block T.commonDepth→Fin (2^(m-T.commonDepth))→Fin (2*A.cap)→Option (DescentSharedCableNames.Stage.Live A.degree A.cap))
    (reserved : Fin H→Fin A.degree→Fin A.degree→Fin 6→Cell field)
    (own : ∀v hi j,stencil ((shortVertex.trans (Fin.castLEEmb padded)) v) hi j=word ((donor digits frm.basis (frm.enough.trans (Nat.sub_le ..))) v hi j))
    (near : ∀v j,peers ((shortVertex.trans (Fin.castLEEmb padded)) v) j=((hostRoster A ((shortVertex.trans (Fin.castLEEmb padded)).trans Fin.valEmbedding)) v j).map (shortVertex.trans (Fin.castLEEmb padded)))
    (marked : ∀v hi i j,marks ((shortVertex.trans (Fin.castLEEmb padded)) v) hi i j=(signedPanel A (order.trans Fin.valEmbedding) S ready (cableNames k (groupRank groupKey ((shortVertex.trans (Fin.castLEEmb padded)).trans Fin.valEmbedding)))) ((donor digits frm.basis (frm.enough.trans (Nat.sub_le ..))) v hi i) j)
    (paid : ∀v j l s,reserved ((shortVertex.trans (Fin.castLEEmb padded)) v) j l s=(peerData (a:=field) A S ready digits Z T frm (shortVertex.trans (Fin.castLEEmb padded))) v j l s)
    (v : V) (hi : Block T.commonDepth) (j : DescentRotorWindowArchive.Input A.degree (2^(m-T.commonDepth)) A.cap) :
    DescentFallbackPeriod.Projected.RootSources.paddedRow (r:=Z.k-T.commonDepth) (n:=Z.n) (field:=field) (G:=2^T.commonDepth) stencil peers marks
      (fun h j=>(rank h j).val) (fun _=>previousDigit frm.basis (frm.enough.trans (Nat.sub_le ..))) reserved ((shortVertex.trans (Fin.castLEEmb padded)) v) hi (ix j)=(boardFor (field:=field) A S ready digits order Z T frm groupKey (shortVertex.trans (Fin.castLEEmb padded)) word rank) v hi j := by
  exact DescentFallbackPeriod.Projected.RootSources.paddedRow_at (r:=Z.k-T.commonDepth) (n:=Z.n) (field:=field) (G:=2^T.commonDepth) stencil peers marks
    (fun h j=>(rank h j).val) (fun _=>previousDigit frm.basis (frm.enough.trans (Nat.sub_le ..))) reserved (shortVertex.trans (Fin.castLEEmb padded)) (fallbackWindow (field:=field) A S ready digits (order.trans Fin.valEmbedding) Z T frm groupKey (shortVertex.trans (Fin.castLEEmb padded)) word rank)
    (fun _=>previousDigit frm.basis (frm.enough.trans (Nat.sub_le ..))) (peerData (a:=field) A S ready digits Z T frm (shortVertex.trans (Fin.castLEEmb padded)))
    (window_input (field:=field) A S ready digits (order.trans Fin.valEmbedding) Z T frm groupKey (shortVertex.trans (Fin.castLEEmb padded)) word rank own near marked)
    (fun _ _=>rfl) (fun v=>funext fun j=>funext fun l=>funext fun s=>paid v j l s) v hi j

/-- The gathered stencil, ranked window, and six reservation columns establish
the complete board on a real public root, including unoccupied signed slots. -/
theorem measured_public_board
    {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
    (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)
    (groupKey : Fin groups↪ℕ) (shortVertex : V↪Fin (Fintype.card V)) (padded : Fintype.card V≤H)
    (word : Host (Fin groups) V k → ℕ)
    (rank : Fin H → Fin (width (Z.k-T.commonDepth) (2^Z.n) A.degree) → Cell (Ht+2))
        (f : ℕ) (model : DescentResetPublicOperandBook.Config) (side : Bool) (root : Z.placement.Good)
    (x : ((matrixConfig ({model with residual:=Z.k-T.commonDepth, multiplicity:=C, packetWidth:=Z.width, gain:=f} : DescentResetPublicOperandBook.Config) A.degree A.cap (2^(m-T.commonDepth)) k field)).Data Z.n)
    (obs : (MeasuredPublicRows (r:=Z.k-T.commonDepth) (n:=Z.n) (field:=field) A S ready digits frm.basis (frm.enough.trans (Nat.sub_le ..)) order groupKey shortVertex padded ({model with residual:=Z.k-T.commonDepth, multiplicity:=C, packetWidth:=Z.width, gain:=f} : DescentResetPublicOperandBook.Config) side (frm.host.symm root.val.1) (Z.rootBlock T (.inl root)) x (Function.Embedding.subtype (fun e=>Z.placement.owner side (Z.placement.contact e)=.inl root))))
    (own : ∀v hi j,obs.own ((shortVertex.trans (Fin.castLEEmb padded)) v) hi j=word ((donor digits frm.basis (frm.enough.trans (Nat.sub_le ..))) v hi j))
    (near : ∀v j,obs.peers ((shortVertex.trans (Fin.castLEEmb padded)) v) j=((hostRoster A ((shortVertex.trans (Fin.castLEEmb padded)).trans Fin.valEmbedding)) v j).map (shortVertex.trans (Fin.castLEEmb padded)))
    (ranked : ∀v j,obs.ranks ((shortVertex.trans (Fin.castLEEmb padded)) v) j=(rank ((shortVertex.trans (Fin.castLEEmb padded)) v) j).val)
    (comparison : ∀v hi,obs.comparison ((shortVertex.trans (Fin.castLEEmb padded)) v) hi=previousDigit frm.basis (frm.enough.trans (Nat.sub_le ..)) hi)
    (paid : ∀v j l s,obs.reserved ((shortVertex.trans (Fin.castLEEmb padded)) v) j l s=(peerData (a:=field) A S ready digits Z T frm (shortVertex.trans (Fin.castLEEmb padded))) v j l s) :
    ((matrixConfig ({model with residual:=Z.k-T.commonDepth, multiplicity:=C, packetWidth:=Z.width, gain:=f} : DescentResetPublicOperandBook.Config) A.degree A.cap (2^(m-T.commonDepth)) k field)).oldData x=(boardFor (field:=field) A S ready digits order Z T frm groupKey (shortVertex.trans (Fin.castLEEmb padded)) word rank) (frm.host.symm root.val.1) (Z.rootBlock T (.inl root)) := by
  have pkt (v : V) (hi : Block T.commonDepth) :
      DescentFallbackPeriod.inputs (r:=Z.k-T.commonDepth) (n:=Z.n) (field:=field) (G:=2^T.commonDepth) obs.own obs.peers obs.marks obs.ranks ((shortVertex.trans (Fin.castLEEmb padded)) v) hi=(fallbackWindow (field:=field) A S ready digits (order.trans Fin.valEmbedding) Z T frm groupKey (shortVertex.trans (Fin.castLEEmb padded)) word rank) v hi := by
    have actual := window_input (field:=field) A S ready digits (order.trans Fin.valEmbedding) Z T frm groupKey (shortVertex.trans (Fin.castLEEmb padded)) word rank
      own near obs.reached v hi
    refine Eq.trans ?_ actual
    funext j
    rcases j with (i|⟨k,i⟩)|(⟨i,z⟩|i)
    · rfl
    · rfl
    · rfl
    · exact congrArg (fun m : ℕ=>(m:Cell field)) (ranked v i)
  have quotaAt (v : V) : obs.reserved ((shortVertex.trans (Fin.castLEEmb padded)) v)=(peerData (a:=field) A S ready digits Z T frm (shortVertex.trans (Fin.castLEEmb padded))) v :=
    funext fun j=>funext fun l=>funext fun s=>paid v j l s
  funext j
  refine (obs.matrix j).trans ?_
  exact DescentFallbackPeriod.Projected.RootSources.paddedRow_at (r:=Z.k-T.commonDepth) (n:=Z.n) (field:=field) (G:=2^T.commonDepth) obs.own obs.peers obs.marks obs.ranks
    obs.comparison obs.reserved (shortVertex.trans (Fin.castLEEmb padded)) (fallbackWindow (field:=field) A S ready digits (order.trans Fin.valEmbedding) Z T frm groupKey (shortVertex.trans (Fin.castLEEmb padded)) word rank) (fun _=>previousDigit frm.basis (frm.enough.trans (Nat.sub_le ..))) (peerData (a:=field) A S ready digits Z T frm (shortVertex.trans (Fin.castLEEmb padded)))
    pkt comparison quotaAt (frm.host.symm root.val.1) (Z.rootBlock T (.inl root)) j

end
end Hierarchy.DescentSixParty.GroupStage

end OAI

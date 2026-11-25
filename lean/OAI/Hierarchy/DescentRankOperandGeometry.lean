import OAI.Hierarchy.DescentPackedRankReadout
import OAI.Hierarchy.DescentPackedMatchTerrain

namespace OAI
/-! # Interpreting the compiled short rank operation at a true fall-tree site -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentSharedBookScan DescentPackedLeafAddress
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "code" => vertex.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank groupKey code)
local notation "sites" => Host J V k
local notation "arrive" => chartArrival A S ready native groupKey vertex
local notation "ticketAt" => chartTicket A S ready digits native Z T frame groupKey vertex
local notation "banked" => hostRotor vertex (hostRoster A code)
local notation "normal" => chartShape A S ready Z T
local notation "value" => peerShapeWord A S ready digits Z T frame

theorem chart_wire (s : Bool) (t : Z.Fallback) (u : sites) (q : Fin (2*A.cap))
    (word : Fin H→ℕ)
    (trueEnd : ∀e : Grain A,∀j : Fin A.degree,arrive s u q=some (j,home A (endSite A (!s) e))→
      word (vertex (A.pos (endSite A (!s) e)).2)=value (!s) (home A (endSite A (!s) e))) :
    ((signedPanel A native S ready names u q).bind fun z=>if z.target=s then
      (banked (vertex u.1.2) z.neighbor).map (fun v=>(z.neighbor,v)) else none).elim 0
        (fun y=>remote (normal t) (some y.1) (word y.2))=ticketAt s t u q := by
  have hostRead j : banked (vertex u.1.2) j=((hostRoster A code u.1.2 j).map vertex) := by
    have live : ∃z,vertex z=vertex u.1.2:=⟨u.1.2,rfl⟩
    simp only [hostRotor,dite_eq_left live,vertex.injective live.choose_spec]
  have operand : ((signedPanel A native S ready names u q).bind fun z=>if z.target=s then
      (banked (vertex u.1.2) z.neighbor).map (fun v=>(z.neighbor,v)) else none)=
      (arrive s u q).map (fun p=>(p.1,vertex p.2.1.2)) := by
    unfold chartArrival
    cases chip:signedPanel A native S ready names u q with
    | none=>rfl
    | some z=>
      simp only [bind,Option.bind_some,Option.pure_def]
      split
      · rw [hostRead]
        cases sel:hostRoster A code u.1.2 z.neighbor <;> rfl
      · rfl
  rw [operand]
  unfold chartTicket
  cases pick:arrive s u q with
  | none=>rfl
  | some a=>
    rcases a with ⟨j,b⟩
    have real:=(chartArrival_peer A S ready native groupKey vertex s u q).symm.trans
      (congrArg (Option.map Prod.snd) pick)
    rw [signedPeer_slot] at real
    obtain ⟨e,_,rfl⟩:=Option.map_eq_some_iff.mp real
    change remote _ (some _) (word _)=remote _ (some _) _
    exact congrArg (remote (normal t) (some j)) (trueEnd e j pick)

end
end Hierarchy.DescentSixParty.GroupStage

end OAI

import OAI.Hierarchy.DescentGroupPeerOrder
import OAI.Hierarchy.DescentIssuedLeafSelector
import OAI.Hierarchy.DescentBookChartTickets

namespace OAI
/-! # The shared rank-table row selected by a real signed old-grain address -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGroupPeerOrder DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt
open scoped Classical Fin.CommRing
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
local notation "Y" => 2^Z.n
local notation "r" => Z.k-T.commonDepth
local notation "term" => fallbackCell A S ready digits Z T frame
local notation "shape" => fun t : Z.Fallback=>shortName T.commonDepth (T.code t)
local notation "bad" => exceptionalCell A S ready digits Z T frame
local notation "sites" => Host J V k
local notation "actual" => signedPeer A native S ready names
local notation "roster" => hostRoster A code

/-- Every occupied slot retains its local ordinal as well as its former remote host.
Empty cells, wrong directions and missing peers produce the zero ticket. -/
def chartArrival (s : Bool) (u : sites) (q : Fin (2*A.cap)) : Option (Fin A.degree×sites) := do
  let z←signedPanel A native S ready names u q
  if z.target=s then do
    let v←roster u.1.2 z.neighbor
    return (z.neighbor,((u.1.1,v),u.2))
  else none

theorem chartArrival_peer (s : Bool) (u : sites) (q : Fin (2*A.cap)) :
    (chartArrival A S ready native groupKey vertex s u q).map Prod.snd=actual s u q := by
  unfold chartArrival signedPeer
  cases hit : signedPanel A native S ready names u q with
  | none=>rfl
  | some z=>
    simp only [bind,Option.bind_some,Option.pure_def]
    split
    · rw [physicalPeer_group]
      cases hit:roster u.1.2 z.neighbor <;> rfl
    · rfl

theorem chartArrival_host (s : Bool) (u : sites) (q : Fin (2*A.cap)) (j : Fin A.degree) (b : sites)
    (read : chartArrival A S ready native groupKey vertex s u q=some (j,b)) :
    roster u.1.2 j=some b.1.2 ∧ (shape (term (!s) b)).1=frame.host b.1.2 := by
  have reached : actual s u q=some b := (chartArrival_peer A S ready native groupKey vertex s u q).symm.trans (congrArg (Option.map Prod.snd) read)
  rw [signedPeer_slot] at reached
  obtain ⟨e,_,rfl⟩:=Option.map_eq_some_iff.mp reached
  constructor
  · unfold chartArrival at read
    cases taken : signedPanel A native S ready names u q with
    | none=>simp [taken] at read
    | some z=>
      simp only [taken,bind,Option.bind_some] at read
      split at read
      · cases dest:roster u.1.2 z.neighbor with
        | none=>simp [dest] at read
        | some w=>simp [dest] at read;rcases read with ⟨rfl,eq⟩;exact eq ▸ dest
      · contradiction
  · exact (congrArg (fun t : Z.Fallback => (T.code t).1)
      (cell_home A S ready digits Z T frame (!s) e)).trans (frame.homeHost _)

def chartShape (t : Z.Fallback) : Fin (DescentFallbackShapeTable.rows r Y) :=
  shapeCell (shape t).2 (Nat.sub_le_sub_right (T.codeLegal t).2.1 _) (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem chartShape_read (t : Z.Fallback) :
    DescentFallbackShapeTable.decode r Y (chartShape A S ready Z T t).val=(shape t).2 :=
  DescentFallbackShapeTable.decode_cell r _ (Nat.sub_le_sub_right (T.codeLegal t).2.1 _) (Nat.mod_lt _ (Nat.two_pow_pos _))

def peerShapeWord (s : Bool) (u : sites) :=
  2*(chartShape A S ready Z T (term s u)).val+(bad u).toNat

def chartTicket (s : Bool) (t : Z.Fallback) (u : sites) (q : Fin (2*A.cap)) :
    Cell (DescentSharedBookScan.bits r Y A.degree) :=
  match chartArrival A S ready native groupKey vertex s u q with
  | none=>0
  | some (j,b)=>remote (chartShape A S ready Z T t) (some j) (peerShapeWord A S ready digits Z T frame (!s) b)

theorem chartTicket_read (s : Bool) (t : Z.Fallback) (u : sites) (q : Fin (2*A.cap)) :
    chartTicket A S ready digits native Z T frame groupKey vertex s t u q=
      (chartArrival A S ready native groupKey vertex s u q).elim 0 (fun p=>ticket
        (chartShape A S ready Z T t,p.1.succ,chartShape A S ready Z T (term (!s) p.2))) := by
  unfold chartTicket
  cases h:chartArrival A S ready native groupKey vertex s u q with
  | none=>rfl
  | some z=>
    rcases z with ⟨j,b⟩
    exact remote_read _ _ _ _ _ _

end
end Hierarchy.DescentSixParty.GroupStage

end OAI

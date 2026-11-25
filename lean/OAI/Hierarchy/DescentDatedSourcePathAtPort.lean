import OAI.Hierarchy.DescentDatedSourcePathHeaders
import OAI.Hierarchy.DescentOrdinaryCompactPeerRank

namespace OAI
/-! # The source rotor step recorded in an actual inherited operand -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentSixParty DescentSharedCableNames DescentGroupPeerOrder DescentIssuedFallbackPanel
open DescentPacking.PackedMatch.Local.Stage DescentHostDirectory DescentHaloWalkRAM DescentStageEdgeReceipt
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (ord : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (group : J↪ℕ) (host : V↪Fin H)
local notation "vertex" => host.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank group vertex)
local notation "B" => Stage.source A ord
local notation "wing" => Stage.live A ord S ready names
local notation "R" => hostRotor host (hostRoster A vertex)

private theorem stream_read (h : Stage.Host J V k) (u : A.CellPorts h.1.1 h.1.2 h.2) :
    (Stage.ofPort A ord h u).val=Stage.stream A ord (Stage.recover A h u) := by cases u <;> rfl

theorem source_at_wing (h:Stage.Host J V k) (u:A.CellPorts h.1.1 h.1.2 h.2) :
    Stage.home A (W.graph.src (Stage.recover A h u).1)=
      if (wing h u).target then (B).peer h (Stage.ofPort A ord h u).val else h := by
  rcases h with ⟨⟨g,v⟩,b⟩
  rcases u with ⟨e,j⟩|⟨e,j⟩
  · simpa [Stage.live,Stage.signedBit,Stage.recover,Stage.home] using
      (Prod.ext e.property.1 e.property.2 : (A.pos (W.graph.src e.val),A.block (W.graph.src e.val))=((g,v),b))
  · have dst:Stage.home A (W.graph.dst e.val)=((g,v),b):=Prod.ext e.property.1 e.property.2
    simp only [Stage.live,Stage.signedBit,Sum.elim_inr,Fin.val_one,decide_true,ite_true,
      Stage.recover,Ends.peer,stream_read,Stage.source,Equiv.symm_apply_apply]
    split
    · rename_i eqn
      exact eqn.trans dst.symm
    · rfl

/-- The selector is the true previous actor path or its real one-step
continuation, according to the sign of the source-preferred registered wire. -/
theorem previous_source (h : Stage.Host J V k) (u : A.CellPorts h.1.1 h.1.2 h.2)
    (recv : Fin H) (p q : Fin (breadth A.degree))
    (actor : Gather.reaching R recv p=some (host h.1.2))
    (issued : Gather.select (Gather.reaching R) recv q=
      some (host (A.pos (W.graph.src (Stage.recover A h u).1)).2)) :
    let r:=wing h u
    value (Gather.reaching R) recv p (shortPath (if r.target then r.neighbor.castSucc else Fin.last A.degree))=q.val+1 := by
  rcases h with ⟨⟨j,a⟩,x⟩
  let h:=((j,a),x)
  let z:=(B).peer h (Stage.ofPort A ord h u).val
  let r:=wing h u
  have src:=source_at_wing A ord S ready group host h u
  change value (Gather.reaching R) recv p (shortPath (if r.target then r.neighbor.castSucc else Fin.last A.degree))=_
  cases flag : r.target with
  | false =>
    rw [ite_eq_right (by simp)]
    apply located_stay R recv (host a) p q actor
    have placed : Stage.home A (W.graph.src (Stage.recover A h u).1)=h := by
      simpa only [r,flag,Bool.false_eq_true,ite_false] using src
    have atHost:=congrArg (fun t : Stage.Host J V k=>host t.1.2) placed
    exact issued.trans (congrArg some atHost)
  | true =>
    rw [ite_eq_left rfl]
    have placed : Stage.home A (W.graph.src (Stage.recover A h u).1)=z := by
      simpa only [r,flag,ite_true] using src
    have keep : (hostRoster A vertex a r.neighbor).map (fun t=>((j,t),x))=some z :=
      (physicalPeer_group A group vertex j a x r.neighbor).symm.trans (physicalPeer_read A ord S ready names h u)
    obtain ⟨peer,atPeer,same⟩:=Option.map_eq_some_iff.mp keep
    have physical : R (host a) r.neighbor=some (host z.1.2) := by
      have yes : ∃v,host v=host a:=⟨a,rfl⟩
      rw [hostRotor,dite_eq_left yes,host.injective yes.choose_spec,atPeer,Option.map_some]
      exact congrArg (fun t=>some (host t)) (congrArg (fun t : Stage.Host J V k=>t.1.2) same)
    apply located_peer R recv (host a) (host z.1.2) p q r.neighbor actor physical
    exact issued.trans (congrArg some (congrArg (fun t : Stage.Host J V k=>host t.1.2) placed))

end
end Hierarchy.DescentDatedSourcePathDirectory

end OAI

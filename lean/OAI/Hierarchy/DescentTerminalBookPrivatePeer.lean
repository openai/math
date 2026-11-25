import OAI.Hierarchy.DescentTerminalBookPrivateCell
import OAI.Hierarchy.DescentTerminalBookGraphFields

namespace OAI
/-! # Lifting a recovered physical pointer to its actual opposite home and socket -/
namespace Hierarchy.DescentTerminalLocalPortBook.Board
open DescentSixParty DescentCompiler DescentSharedCableNames DescentColonies DescentChosenRouter
open DescentTerminalPeerChronology DescentTerminalPointerDigits DescentTerminalGrainProfiles
open DescentTerminalGraphPositions DescentTerminalCableOrder DescentPacking DescentSortedRoster
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentTerminalGraphRows Computability.BorderVNP.Crossing DescentStageEdgeReceipt
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {F P V:Type} [Field F] [Fintype P] [Fintype V] [DecidableEq V] {groups d k i H p scale:ℕ}
    {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε (Fin groups) V k) (hosts:V↪Fin H) (S:AtomSchedule) (ready:A.StateBounds S i)
    (native:W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (raw:Fin H→Fin A.degree→Option (Fin H))
    (roster:∀o,present raw (hosts o)=(A.near o).map hosts)
local notation "ord" => native.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=groups)) (hosts.trans Fin.valEmbedding))
local notation "ends" => Stage.source A ord
local notation "hereAt" => fun v:W.graph.Site=>hosts (Prod.snd (A.pos v))

include roster in
omit [Fintype P] in
theorem wing_socket (h:Stage.Host (Fin groups) V k) (u:A.CellPorts h.1.1 h.1.2 h.2) :
    indexed raw (hosts h.1.2) (Stage.live A ord S ready names h u).neighbor=
      some (hosts ((ends).peer h (Stage.ofPort A ord h u).val).1.2) := by
  rcases h with ⟨⟨g,o⟩,b⟩
  let h:Stage.Host (Fin groups) V k:=((g,o),b)
  let q:=Stage.ofPort A ord h u
  let dest:=(ends).peer h q.val
  have near:= (ends).peer_mem (Stage.near A) (Stage.connected A ord) h q
  obtain ⟨t,ht,eqn⟩:=Finset.mem_map.mp near
  obtain ⟨v,hv,hit⟩:=Finset.mem_map.mp ht
  change (t,b)=dest at eqn
  change (g,v)=t at hit
  have atV:dest=((g,v),b):=by rw [←eqn,←hit]
  let nb:↥(A.near o):=⟨v,hv⟩
  have nbMem:(g,v)∈neighbors A (g,o):=Finset.mem_map.mpr ⟨v,hv,rfl⟩
  have stage:=paired A (groupRank Fin.valEmbedding (hosts.trans Fin.valEmbedding)) (g,o) b ⟨_,nbMem⟩
  rw [PackedFlow.socket_grouped A Fin.valEmbedding (hosts.trans Fin.valEmbedding) g o nb] at stage
  have lane: (Stage.live A ord S ready names h u).neighbor=PackedFlow.socket A (hosts.trans Fin.valEmbedding) o nb :=
    ((peer_slot A ord S ready names h _ u).2 atV).trans stage
  change indexed raw (hosts o) (Stage.live A ord S ready names h u).neighbor=some (hosts dest.1.2)
  rw [lane,atV]
  apply (indexed_iff ..).2
  constructor
  · rw [roster];exact Finset.mem_map.mpr ⟨_,hv,rfl⟩
  · rw [before,roster,PackedFlow.socket,nb_val,Finset.filter_map,Finset.card_map]
    rfl

variable (ext:P↪ℕ) (nodes:W.graph.Site↪ℕ) (ops:∀v,Boundary W.graph v↪ℕ)
local notation "graph" => order W.graph hereAt native p ext nodes ops

theorem actual_neighbor (v:W.graph.Site) (u:A.CellPorts (A.pos v).1 (A.pos v).2 (A.block v))
    (g:Order.Group graph (hereAt v)) (nm:Order.At graph (hereAt v) g)
    (j:Fin (poolBatchCount (W.graph.width (Stage.recover A (Stage.home A v) u).1) p))
    (label:nm.val=.inl ⟨(Stage.recover A (Stage.home A v) u).1,j⟩) :
    g.val=some (hosts ((ends).peer (Stage.home A v) (Stage.ofPort A ord (Stage.home A v) u).val).1.2) := by
  let h:=Stage.home A v
  let q:=Stage.ofPort A ord h u
  let dest:=(ends).peer h q.val
  have same:=peer_home A native h u
  have place:dest=((h.1.1,dest.1.2),h.2):=Prod.ext (Prod.ext same.1 rfl) same.2
  have incident:q.val∈(ends).parallel h dest:=((ends).mem_parallel ..).2 ⟨q.property,rfl⟩
  rw [show q.val=Stage.stream A ord (Stage.recover A h u) from recover_stream A native h u,place] at incident
  have pair:=((parallel_at A ord hosts h.1.2 dest.1.2 h.1.1 h.2 _).1 incident).2.2
  have real:= (between_iff W.graph p graph (hereAt v) (hosts dest.1.2) (Stage.recover A h u).1 j).2 pair
  exact nm.property.2.symm.trans (label ▸ real.2)

end
end Hierarchy.DescentTerminalLocalPortBook.Board

end OAI

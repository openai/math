import OAI.Hierarchy.DescentTerminalPeerCounterSockets

namespace OAI
/-! # Identifying a purchased sorted roster slot with the signed stage neighbor -/
namespace Hierarchy.DescentTerminalGrainProfiles.Counter
open DescentHostDirectory Computability.BorderVNP.Crossing DescentSixParty DescentColonies DescentCompiler DescentSortedRoster DescentTerminalCableOrder
open DescentPacking.PackedMatch.Local.Stage
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {deg k H : ℕ} {bits:P→ℕ} {W:MarkedWorld F deg P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (hosts:V↪Fin H) (raw:Fin H→Fin A.degree→Option (Fin H))
    (presentAt:∀v,present raw (hosts v)=(A.near v).map hosts)
local notation "R" => indexed raw
local notation "atH" => fun v:W.graph.Site=>hosts (Prod.snd (A.pos v))
local notation "socket" => PackedFlow.socket A (hosts.trans Fin.valEmbedding)
include presentAt

theorem reached_socket (v:V) (j:Fin A.degree) {u:Fin H} (hit:R (hosts v) j=some u) :
    ∃y:↥(A.near v),hosts y.val=u ∧ socket v y=j := by
  obtain ⟨near,slot⟩:=(indexed_iff raw (hosts v) j u).1 hit
  rw [presentAt v] at near
  obtain ⟨y,hy,rfl⟩:=Finset.mem_map.mp near
  refine ⟨⟨y,hy⟩,rfl,Fin.ext ?_⟩
  rw [PackedFlow.socket,nb_val]
  rw [←slot,before,presentAt,Finset.filter_map,Finset.card_map]
  rfl

theorem all_adjacent (e:W.graph.Edge) :
    atH (W.graph.dst e)∈present raw (atH (W.graph.src e)) ∧ atH (W.graph.src e)∈present raw (atH (W.graph.dst e)) := by
  have adj (i j:J×V) (hit:j∈groupedNear A.near i) : hosts j.2∈present raw (hosts i.2) := by
    obtain ⟨u,hu,eqn⟩:=Finset.mem_map.mp hit
    rw [presentAt]
    exact Finset.mem_map.mpr ⟨u,hu,congrArg (fun z:J×V=>hosts z.2) eqn⟩
  exact ⟨adj _ _ (A.peers e).1,adj _ _ (A.peers e).2⟩

theorem mounted_present (v:V) : present R (hosts v)=present raw (hosts v) := by
  ext z
  constructor
  · intro h
    obtain ⟨j,read⟩:=(Finset.mem_filter.mp h).2
    exact ((indexed_iff raw (hosts v) j z).1 read).1
  · intro h
    have room:(present raw (hosts v)).card≤A.degree:=by rw [presentAt,Finset.card_map];exact A.degreeBound v
    have own:before raw (hosts v) z<(present raw (hosts v)).card:=by
      apply Finset.card_lt_card
      apply (Finset.ssubset_iff_of_subset (Finset.filter_subset ..)).2
      exact ⟨z,h,by simp⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨_,own.trans_le room⟩,(indexed_iff ..).2 ⟨h,rfl⟩⟩⟩

omit presentAt in
theorem absent_mass (h other:Fin H) (lost:∀v,hosts v≠h) : pairMass W.graph atH (pair h other)=0 := by
  apply Finset.sum_eq_zero
  intro e he
  have which:pair (atH (W.graph.src e)) (atH (W.graph.dst e))=pair h other:=(Finset.mem_filter.mp he).2
  rcases (pair_iff ..).1 which with one|two
  · exact (lost _ one.1).elim
  · exact (lost _ two.2).elim

end
end Hierarchy.DescentTerminalGrainProfiles.Counter

end OAI

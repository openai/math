import OAI.Hierarchy.DescentTerminalPeerCounter
import OAI.Hierarchy.DescentPackedFlowRoster

namespace OAI
/-! # The reached short roster slot counts the true cable volume of its host pair -/

namespace Hierarchy.DescentTerminalGrainProfiles.Counter
open DescentSixParty DescentSharedCableNames DescentCompiler DescentColonies DescentTerminalCableOrder
open DescentStageEdgeReceipt DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {deg k i H groups M d : ℕ} {bits : P→ℕ} {W : MarkedWorld F deg P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S i)
    (ranks:J↪Fin groups) (hosts:V↪Fin H)
local notation "names" => cableNames k (groupRank (ranks.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding))
local notation "board" => Prepare.signed A native S ready ranks hosts
local notation "B" => Stage.source A native
local notation "peers" => PackedFlow.socket A (hosts.trans Fin.valEmbedding)

theorem raster_peer (v:V) (other:↥(A.near v)) (g:J) (x:Block k) :
    (peerWires (fun t=>board x t (hosts v) (ranks g)) (peers v other)).card=
      ((B).parallel ((g,v),x) ((g,other.val),x)).card := by
  have adj : (g,other.val)∈neighbors A (g,v):=Finset.mem_map.mpr ⟨other.val,other.property,rfl⟩
  have stage:=paired A (groupRank (ranks.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)) (g,v) x ⟨_,adj⟩
  rw [PackedFlow.socket_grouped A (ranks.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding) g v other] at stage
  have lookup : (fun t => board x t (hosts v) (ranks g)) =
      Stage.signedPanel A native S ready names ((g,v),x) := by
    funext t
    exact DescentTerminalSignedGrainWord.stored_site A native S ready ranks hosts x t (g,v)
  rw [lookup]
  rw [←stage]
  exact pair_count A native S ready names _ _

theorem raster_blank (x:Block k) (v:V) (g:Fin groups) (off:∀j,ranks j≠g) (t:Fin (2*A.cap)) :
    board x t (hosts v) g=none := by
  have no : ¬∃z:J×V,ranks z.1=g ∧ hosts z.2=hosts v := by rintro ⟨z,eqn,_⟩;exact off _ eqn
  simp only [Prepare.signed,Prepare.spreadField,dite_eq_right no]

theorem reached (positive:0<M) (z:Fin (columns (2^k) A.cap groups M)→Cell d)
    (v:V) (other:↥(A.near v)) {p scale:ℕ} (hp:0<p) (whole:A.z*G.b=scale*p)
    (ticket:(z (number (2^k) A.cap groups M (.inl 0))).val=(peers v other).val+1)
    (port:∀x t g,sample A.degree positive z x t g=board x t (hosts v) g) :
    (aggregate A.degree scale positive z).val=
      pairMass W.graph (fun s=>hosts (A.pos s).2) (pair (hosts v) (hosts other.val))/p := by
  change tally A.degree scale positive z=_
  rw [tally,ticket,candidate_read]
  simp_rw [port]
  let f:Fin groups→ℕ:=fun g=>∑x:Block k,(peerWires (fun j=>board x j (hosts v) g) (peers v other)).card
  have sums : (∑g:Fin groups,f g)=∑g:J,∑x:Block k,((B).parallel ((g,v),x) ((g,other.val),x)).card := by
    calc
      _=∑g∈Finset.univ.map ranks,f g := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro g _ off
        have absent:∀j,ranks j≠g:=by rintro j rfl;exact off (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩)
        simp [f,raster_blank A native S ready ranks hosts _ v g absent,peerWires]
      _=_ := by
        rw [Finset.sum_map]
        simp only [f,raster_peer A native S ready ranks hosts v other]
  rw [show (∑g:Fin groups,∑x:Block k,(peerWires (fun j=>board x j (hosts v) g) (peers v other)).card)=_ from sums]
  exact purchased_chunks A native hosts S ready v other.val hp whole

theorem inactive {blocks cap : ℕ} (positive:0<M) (z:Fin (columns blocks cap groups M)→Cell d)
    (zero:(z (number blocks cap groups M (.inl 0))).val=0) (D scale:ℕ) :
    (aggregate D scale positive z).val=0 := by simp [aggregate,tally,zero,candidate]

end
end Hierarchy.DescentTerminalGrainProfiles.Counter

end OAI

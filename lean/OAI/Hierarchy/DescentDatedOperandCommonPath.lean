import OAI.Hierarchy.DescentDatedSourcePathAtPort
import OAI.Hierarchy.DescentDatedReversePath
import OAI.Hierarchy.DescentHaloReversePath

namespace OAI
/-! # The receiver's prior signed lookup and the raw donor rebase name the same slot -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentSixParty DescentSharedCableNames DescentGroupPeerOrder DescentIssuedFallbackPanel
open DescentPacking.PackedMatch.Local.Stage DescentHostDirectory DescentHaloWalkRAM DescentStageEdgeReceipt
open scoped Classical
noncomputable section
variable {F Pin J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i H : ℕ} {bits : Pin→ℕ} {W : MarkedWorld F d Pin bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (ord : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (group : J↪ℕ) (host : V↪Fin H)
local notation "vertex" => host.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank group vertex)
local notation "R" => hostRotor host (hostRoster A vertex)

theorem reciprocal (z y : Fin H) (port : Fin A.degree) (found : R z port=some y) : ∃q,R y q=some z :=by
  unfold hostRotor at found
  split at found
  · rename_i present
    obtain ⟨t,roster,addr⟩:=Option.map_eq_some_iff.mp found
    have near: t∈A.near present.choose :=(hostRoster_mem A vertex present.choose t).2 ⟨port,roster⟩
    obtain ⟨j,back⟩:=(hostRoster_mem A vertex t present.choose).1 ((A.symmetric _ _).1 near)
    have yt:∃v,host v=y:=⟨t,addr⟩
    have same:yt.choose=t:=host.injective (yt.choose_spec.trans addr.symm)
    exact ⟨j,by simp only [hostRotor,dite_eq_left yt,same,back,Option.map_some,present.choose_spec]⟩
  · contradiction

theorem previous_source_from_raw (h : Stage.Host J V k) (u : A.CellPorts h.1.1 h.1.2 h.2)
    (recv : Fin H) (p back : Fin (breadth A.degree))
    (actor : Gather.reaching R recv p=some (host h.1.2))
    (forward : walk R (host (A.pos (W.graph.src (Stage.recover A h u).1)).2) (path back) 4=some recv) :
    let src:=host (A.pos (W.graph.src (Stage.recover A h u).1)).2
    let r:=Stage.live A ord S ready names h u
    ∃q,Gather.select (Gather.reaching R) recv q=some src ∧
      value (Gather.reaching R) recv p (shortPath (if r.target then r.neighbor.castSucc else Fin.last A.degree))=q.val+1 ∧
      DescentHaloWalkRAM.Rebase.value R .path src back=q.val :=by
  intro src r
  obtain ⟨digits,atSource⟩:=reverse_path R (reciprocal A host) (path back) src recv forward
  have hit: ∃j,Gather.reaching R recv j=some src:=by
    exact ⟨finFunctionFinEquiv digits,by simpa only [Gather.reaching,path,Equiv.symm_apply_apply] using atSource⟩
  obtain ⟨q,actual,_⟩:=Gather.once (Gather.reaching R) recv src hit
  exact ⟨q,actual,previous_source A ord S ready group host h u recv p q actor actual,
    DescentHaloWalkRAM.Rebase.canonical_path R src recv back q forward actual⟩

end
end Hierarchy.DescentDatedSourcePathDirectory

end OAI

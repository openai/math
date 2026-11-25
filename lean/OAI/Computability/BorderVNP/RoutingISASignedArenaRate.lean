import OAI.Computability.BorderVNP.RoutingISASignedReaderArena
import OAI.Computability.BorderVNP.RoutingISACubeArenaRate

/-! # A single word bound for the routed signed task, tally and entry arrays -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open DiagonalTallyAllocation Filter

/-- All addresses after the fixed finite cube tables fit a fixed cubic
polynomial in the actual source-format and sparse window maxima. -/
theorem Layout.end_le (l : Layout) (W u v k q : ℕ) (report : l.p.report.Le q)
    (cells : l.cube.cells ≤ q) (teams : l.cube.teams ≤ q) (cables : l.cube.cables ≤ q)
    (rows : l.cube.maxRows ≤ q) (params : l.p.parameters ≤ q)
    (scratch : l.p.scratchStride ≤ q) (burst : l.p.burstStride ≤ q)
    (word : W ≤ q) (query : u ≤ q) (guess : v ≤ q) (gates : k ≤ q) :
    l.endAddress W u v k ≤ CubeConstants.arenaEnd l.cube.stop l.id + 192*(q+1)^3 := by
  let x := CubeConstants.arenaEnd l.cube.stop l.id
  have fr : l.before.start ≤ x+32*(q+1)^2 :=
    l.fragments.polynomial_room cables rows cells scratch
  have pr : l.before.limit ≤ l.before.start+23*(q+1)^2 := l.before.polynomial_room report
  have stages : l.after.start = l.before.limit + 3*l.cube.cells+7*l.cube.cells+
      l.p.scratchStride*l.cube.cells+l.p.burstStride*l.cube.cells := rfl
  have hr := l.after.polynomial_room (K:=q) report
  have pair := Nat.mul_le_mul scratch cells
  have bpair := Nat.mul_le_mul burst cells
  have op : l.p.report.operands ≤ q*q+q+q := by
    unfold Bounds.operands
    have cg := Nat.mul_le_mul report.cells report.gadgets
    have hu := report.uses
    have hv := report.vertices
    omega
  have dim : l.dim ≤ 2*q := by unfold Layout.dim; have := report.gadgets; omega
  have td := Nat.mul_le_mul teams dim
  have dw := Nat.mul_le_mul dim word
  change l.after.fresh+2*l.p.report.operands+l.dim+l.cube.teams*l.dim+l.dim+l.dim+1+
    l.dim*W+1+2+u+v+k+(6+3*k+u) ≤ x + 192*(q+1)^3
  nlinarith only [fr,pr,hr,stages,pair,bpair,op,dim,td,dw,cells,query,guess,gates,
    Nat.zero_le (q*q*q),Nat.zero_le (q*q),Nat.zero_le q]

variable {ι : Type*} {scale : ι → ℕ}

/-- The numeric inputs may range over different histories and batch sizes. The
two envelopes here cover the preceding arena and the input/output dimensions.
The concrete final address has one exponent over the entire family. -/
theorem polynomial_end (L : ι → Layout) (W u v k q : ι → ℕ)
    (base : CubeArena.Poly scale (fun i ↦ CubeConstants.arenaEnd (L i).cube.stop (L i).id))
    (bound : CubeArena.Poly scale q) (report : ∀ i,(L i).p.report.Le (q i))
    (scalar : ∀ i, (L i).cube.cells ≤ q i ∧ (L i).cube.teams ≤ q i ∧ (L i).cube.cables ≤ q i ∧
      (L i).cube.maxRows ≤ q i ∧ (L i).p.parameters ≤ q i ∧ (L i).p.scratchStride ≤ q i ∧
      (L i).p.burstStride ≤ q i ∧ W i ≤ q i ∧ u i ≤ q i ∧ v i ≤ q i ∧ k i ≤ q i) :
    CubeArena.Poly scale (fun i ↦ (L i).endAddress (W i) (u i) (v i) (k i)) := by
  apply (base.add ((CubeArena.Poly.const 192).mul ((bound.add (CubeArena.Poly.const 1)).pow 3))).mono
  intro i
  obtain ⟨c,r,m,rows,par,sc,bu,hw,hq,hv,hk⟩ := scalar i
  exact (L i).end_le _ _ _ _ _ (report i) c r m rows par sc bu hw hq hv hk

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI

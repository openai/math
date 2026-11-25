import OAI.Optimization.LinearProgramming.Compression.RequestProbeSession

/-! A fixed polynomial bounds the duration and every word in the variable-dimension
request dialogue as a function of its initial encoded length. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable
namespace Dialogue

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit OracleSpec

variable {I : Type} {ei : I → Word} {prepare : I → Prepared}

noncomputable def prepareSizePoly (p : Procedure ei preparedCode prepare) : Polynomial ℕ :=
  Polynomial.X+p.bound

noncomputable def depthPoly (p : Procedure ei preparedCode prepare) : Polynomial ℕ :=
  let s := prepareSizePoly p
  s+gridDepthP.bound.comp s

noncomputable def sourcePoly (p : Procedure ei preparedCode prepare) : Polynomial ℕ :=
  let s := prepareSizePoly p
  s+gridRowsP.bound.comp s

noncomputable def routeInputPoly (p : Procedure ei preparedCode prepare) : Polynomial ℕ :=
  let s := prepareSizePoly p
  2*s+Driver.Probe.probeWordPolynomial.comp (s+1+depthPoly p+sourcePoly p)+1

noncomputable def dispatchWidthPoly (p : Procedure ei preparedCode prepare) : Polynomial ℕ :=
  let u := routeInputPoly p
  Polynomial.X+u+routeP.bound.comp u+Polynomial.C ((outputCode failOutput).length+7)

noncomputable def runtimePoly (p : Procedure ei preparedCode prepare) : Polynomial ℕ :=
  let L := dispatchWidthPoly p
  (depthPoly p+1)*((dispatchWithP p).shared.bound.comp L+18*L+18)+3

theorem prepared_bounds (p : Procedure ei preparedCode prepare) (i : I) :
    let x := (prepare i).2
    let n := (ei i).length
    let L := (dispatchWidthPoly p).eval n
    gridDepth x ≤ (depthPoly p).eval n ∧
      routedSize x (x.2.length+1) (gridDepth x) (sourceWordSize x)+6 ≤ L ∧
      (WordDialogue.stateCode ei carryCode (.inl i)).length ≤ L := by
  intro x n L
  let s := (prepareSizePoly p).eval n
  let u := (routeInputPoly p).eval n
  have hs : (gridArgCode x).length ≤ s := by
    have hp := p.output_length_le i
    simp only [preparedCode,prodCode,pairBits_length] at hp
    simp only [s,n,x,prepareSizePoly,Polynomial.eval_add,Polynomial.eval_X]
    omega
  have hz : x.2.length ≤ s := by
    have count := list_length_le_code intCode x.2
    have hxs : (intRowCode x.2).length≤(gridArgCode x).length := by
      simp only [gridArgCode,prodCode,pairBits_length]
      omega
    exact count.trans (hxs.trans hs)
  have hk : gridDepth x ≤ (depthPoly p).eval n := by
    have hk := gridDepthP.output_length_le x
    simp only [unaryCode,List.length_replicate] at hk
    simpa only [depthPoly,Polynomial.eval_add,Polynomial.eval_comp,s] using
      hk.trans (Nat.add_le_add hs (eval_nat_mono gridDepthP.bound hs))
  have hB : sourceWordSize x ≤ (sourcePoly p).eval n := by
    have hb := gridRowsP.output_length_le x
    simpa only [sourceWordSize,sourcePoly,Polynomial.eval_add,Polynomial.eval_comp,s] using
      hb.trans (Nat.add_le_add hs (eval_nat_mono gridRowsP.bound hs))
  have hu : routedInputSize x (x.2.length+1) (gridDepth x) (sourceWordSize x) ≤ u := by
    rw [routedInputSize,← Driver.Probe.probeWordPolynomial_eval]
    have hh := eval_nat_mono Driver.Probe.probeWordPolynomial
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right hz 1) hk) hB)
    simp only [u,routeInputPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
      Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [s] at hs hh
    omega
  have hroute : routedSize x (x.2.length+1) (gridDepth x) (sourceWordSize x) ≤
      u+routeP.bound.eval u := Nat.add_le_add hu (eval_nat_mono routeP.bound hu)
  have hL : L=n+u+routeP.bound.eval u+((outputCode failOutput).length+7) := by
    simp [L,u,dispatchWidthPoly]
  refine ⟨hk,?_,?_⟩
  · exact (Nat.add_le_add_right hroute 6).trans (by rw [hL]; omega)
  · rw [hL]; change (false :: ei i).length ≤ _
    simp only [List.length_cons];dsimp only [n];omega

theorem failure_length_le (p : Procedure ei preparedCode prepare) (n : ℕ) :
    (outputCode failOutput).length ≤ (dispatchWidthPoly p).eval n := by
  simp only [dispatchWidthPoly,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_C]
  omega

theorem runtime_bound (p : Procedure ei preparedCode prepare) (n r : ℕ)
    (hr : r ≤ (depthPoly p).eval n+1) :
    let L := (dispatchWidthPoly p).eval n
    r*((dispatchWithP p).shared.bound.eval L+18*L+18)+3 ≤ (runtimePoly p).eval n := by
  intro L
  simp only [runtimePoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hr) _

end Dialogue
end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI

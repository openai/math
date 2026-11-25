import OAI.Optimization.LinearProgramming.Lattice.BitRoundState
import OAI.Optimization.LinearProgramming.Lattice.BitProjector
import OAI.Optimization.LinearProgramming.Lattice.BitSelectorNative
import OAI.Optimization.LinearProgramming.Lattice.BitRadix

/-! Exact agreement of the three actual word-level kernels with the three
mathematical transformations in the rounding loop. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

noncomputable def actualKernels : Kernels where
  projection x := Selector.integralRowsList (Projector.deployed x)
  selector := Selector.select
  assemble := Horner.assembleWord

theorem actual_projection {p : ℕ} (old : List (Fin p → ℤ))
    (h : LinearIndependent ℝ (fun i : Fin old.length => WithLp.toLp 2 (realCoordinates (old.get i)))) :
    actualKernels.projection (p,old.map List.ofFn) =
      List.ofFn (fun i => List.ofFn (integralRows (residualTableMatrix old) i)) := by
  change Selector.integralRowsList (Projector.deployed (Projector.input old)) = _
  rw [Projector.projector_pack old h]
  exact Selector.integralRowsListPack _

theorem actual_selector {p : ℕ} (M : ℕ) (u : Fin p → ℚ) :
    actualKernels.selector (M,List.ofFn u) =
      ((lllShortSelector M u).1,List.ofFn (lllShortSelector M u).2) :=
  Selector.selectPack M u

theorem finish_packed {p : ℕ} (M fuel : ℕ) (old : List (Fin p → ℤ)) :
    finish actualKernels (packedEnv M fuel old) =
      .inl (signRowWord (radixVector ((2:ℤ)^radixWidth p M) old.reverse)) := by
  change Sum.inl (signPacket (Horner.assembleWord ((p,radixWidth p M),old.map List.ofFn))) = _
  rw [Horner.assembleWordPack,signPacket_pack]

theorem probeParams_packed {p : ℕ} (M fuel : ℕ) (old : List (Fin p → ℤ))
    (h : LinearIndependent ℝ (fun i : Fin old.length => WithLp.toLp 2 (realCoordinates (old.get i)))) :
    probeParams actualKernels (packedEnv M fuel old) =
      ((p,searchPrecision p M),List.ofFn (fun i => List.ofFn (integralRows (residualTableMatrix old) i))) := by
  unfold probeParams packedEnv
  simp only [actual_projection old h]

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

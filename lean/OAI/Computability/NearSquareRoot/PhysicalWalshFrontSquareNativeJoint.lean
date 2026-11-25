import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareElementaryJoint
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorLarge
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSelected

/-! # Termination and sharp bounds for a generated canonical XOR command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Space PhysicalWalsh GeneratorSyntax CommonRegisters
open KernelPass KernelPass.ComputableSyntax

/-- The selected raw descriptor determines arity and width. The single
generated command includes compact header expansion, native padding and
cropping, the square-log test and the full signed-record elementary branch.
The same command inherits termination and the sharp estimate from the native
program, each on precisely the headers that reach its branch. -/
theorem compileSquareFromNativeJoint {Z : Type} [Primcodable Z] (raw : Z → Raw) (hraw : Computable raw)
    (core : Z → Cmd) (hc : Effective ltr core) (R : ℕ) (reg : ∀ z, Within R (core z)) :
    ∃ (emit : Z → Cmd) (N e : ℕ), Effective ltr emit ∧ 0<N ∧ 1≤e ∧ (∀ z, Within N (emit z)) ∧
      (∀ (z : Z) (ρ : ℝ) (a W : ℕ) (ops : List Op) (arity : 4 ≤ a),
        raw z = (a+1,ops) → (Packed.decode (a+1) ops).i = W →
        PhysicalWalshCompileInterior.NativeOn a W ρ (squareFits a) (core z) →
        ∀ d, e ≤ d → PhysicalWalshCompileXorPacket.FlatRuns (W:=W)
          (nodeScan a W d (squareExtra a W ρ)) (nodeArena a W d) (Interior.axes a arity) (emit z)) ∧
      ∀ (z : Z) (a W : ℕ) (ops : List Op) (arity : 4 ≤ a),
        raw z = (a+1,ops) → (Packed.decode (a+1) ops).i = W →
        PhysicalWalshCompileInterior.NativeTotalOn a W (squareFits a) (core z) →
        flatTotal (W:=W) (Interior.axes a arity) (emit z) := by
  obtain ⟨large,M,f,el,pf,regL,native⟩ :=
    PhysicalWalshCompileInterior.compileOnTotal raw core hraw hc R reg
  let dims := PhysicalWalshCompile.Dispatch.dimensions ∘ raw
  have hdims : Computable dims := PhysicalWalshCompile.Dispatch.primrec_dimensions.to_comp.comp hraw
  obtain ⟨emit,N,b,ee,pN,regE,gate,gateTotal⟩ :=
    compileSquareWithNativeJoint (fun z => (dims z).1) (fun z => (dims z).2)
      (Computable.fst.comp hdims) (Computable.snd.comp hdims) large el M regL
  have dimensions_eq (z : Z) (a W : ℕ) (ops : List Op) (shape : raw z = (a+1,ops))
      (width : (Packed.decode (a+1) ops).i = W) : (dims z).1 = a ∧ (dims z).2 = W := by
    refine ⟨by simp [dims,PhysicalWalshCompile.Dispatch.dimensions,shape],?_⟩
    change ((ComputableSyntax.Shape.algebra (raw z).1).parse (raw z).2).1.1 = W
    rw [shape,← Packed.decode_shape]
    exact width
  refine ⟨emit,N,max b f,ee,pN,pf.trans (le_max_right ..),regE,?_,?_⟩
  · intro z ρ a W ops arity shape width coreOK d de
    obtain ⟨ad,wd⟩ := dimensions_eq z a W ops shape width
    subst a
    subst W
    apply gate z ρ arity d ((le_max_left ..).trans de)
    have hf := (le_max_right ..).trans de
    have inner := (native z _ _ ops arity shape width _).1 ρ coreOK
    exact inner.mono (fun t => Nat.add_le_add_right (allowance_mono hf t.val.shape) _)
      (fun t => allowance_mono hf t.val.shape)
  · intro z a W ops arity shape width coreOK
    obtain ⟨ad,wd⟩ := dimensions_eq z a W ops shape width
    subst a
    subst W
    exact gateTotal z arity ((native z _ _ ops arity shape width _).2 coreOK)

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI

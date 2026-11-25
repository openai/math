import OAI.Computability.NearSquareRoot.PhysicalWalshCompileElementaryRaw
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileGrade

/-! # Effective prefix XOR at a descriptor-dependent squared-logarithm reserve -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileElementaryRelease
open IntegerMultiplication Code Staff PhysicalWalshNode KernelPass.ComputableSyntax
open CommonRegisters GeneratorSyntax
open PhysicalWalshCompileSwapRulers (World regime)

def gradedCut (A : ℕ) (s : PhysicalWalshNode.Shape) := SlotSwap.reserve (Nat.clog 2 (Header.scale A s+1)) A s

/-- The reserve is read from each node descriptor. No reserve depth is
needed in the outer opcode generating the physical program. -/
theorem compileGraded : ∃ (R E : ℕ) (low : PhysicalWalshCompileXorSwap.Params → Cmd),
    Effective ltr low ∧ (∀ k, Within R (low k)) ∧
    ∀ a W (ops : List Op), (Packed.decode (a+1) ops).i = W →
    ∀ (src dst : Fin (a+1)), src ≠ dst → ∀ d, E ≤ d →
      PhysicalWalshCompileXorRoute.Flat (a:=a) (W:=W)
        (nodeScan a W d (ElementarySweep.prefixExtra (a+1) (gradedCut (a+1))))
        (nodeArena a W d) (PhysicalWalshCompileXorSwap.slice (gradedCut (a+1)) src dst)
        (low ((a+1,ops),src.val,dst.val)) := by
  let n (u : World) := PhysicalWalshCompileElementaryAgenda.steps true (PhysicalWalshCompileGrade.regrade u)
  have h : Realizes regime n :=
    PhysicalWalshCompileGrade.has (PhysicalWalshCompileElementaryAgenda.steps_realizes true)
  have bound (u : World) : n u ≤ ElementarySchedule.slotWidth (u.a+1) u.shape :=
    PhysicalWalshCompileElementaryAgenda.steps_le true (PhysicalWalshCompileGrade.regrade u)
  obtain ⟨R,E,c,hc,rc,ok⟩ := compileFor n h bound
  exact ⟨R,E,fun k => c (0,k),hc.comp ((Computable.const 0).pair Computable.id),
    fun k => rc (0,k),fun a W ops eq src dst ne d hd => ok a W ops eq src dst ne 0 d hd⟩

end PhysicalWalshCompileElementaryRelease

end NearSquareRoot
end Computability
end OAI

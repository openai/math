import OAI.Computability.NearSquareRoot.PhysicalWalshCompileElementaryRelease

/-! # Raw-template addressing of the named elementary XOR sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileElementaryRelease
open IntegerMultiplication Code PhysicalWalshNode
open PhysicalWalshCompileSwapRulers (World regime)
open KernelPass.ComputableSyntax KernelPass.ComputableSyntax.Packed CommonRegisters GeneratorSyntax

/-- The reserve degree, raw template, and directed pair select the five control literals. -/
def rawKey (p : ℕ × PhysicalWalshCompileXorSwap.Params) : PhysicalWalshCompileSwapRulers.Control :=
  let raw := p.2.1
  (raw.1, ((KernelPass.ComputableSyntax.Shape.algebra raw.1).parse raw.2).1.1, p.2.2.1, p.2.2.2, p.1)

theorem primrec_rawKey : Primrec rawKey := by
  let T := ℕ × PhysicalWalshCompileXorSwap.Params
  have raw : Primrec (fun p : T => p.2.1) := Primrec.fst.comp Primrec.snd
  have arg : Primrec (fun p : T => p.2.2) := Primrec.snd.comp Primrec.snd
  have A := Primrec.fst.comp raw
  have parse := KernelPass.ComputableSyntax.Shape.primrec_algebra.comp A (Primrec.snd.comp raw)
  exact A.pair (((Primrec.fst.comp Primrec.fst).comp parse).pair
    ((Primrec.fst.comp arg).pair ((Primrec.snd.comp arg).pair Primrec.fst)))

/-- The caller can choose the low reserve degree after receiving the rectangle
degree. Its joint natural parameter remains part of the computable emitter. -/
theorem compileFor (stepsOf : World → ℕ) (known : IntegerMultiplication.Staff.Realizes regime stepsOf)
    (bound : ∀ u, stepsOf u ≤ ElementarySchedule.slotWidth (u.a+1) u.shape) : ∃ (R E : ℕ) (c : ℕ × PhysicalWalshCompileXorSwap.Params → Cmd),
    Effective ltr c ∧ (∀ k, Within R (c k)) ∧
    ∀ a W (ops : List Op), (Packed.decode (a+1) ops).i = W → ∀ (i j : Fin (a+1)), i ≠ j → ∀ D d, E ≤ d →
      PhysicalWalshCompileXorRoute.Flat (a:=a) (W:=W) (nodeScan a W d (ElementarySweep.prefixExtra (a+1) (fun s => stepsOf (world W i j D s))))
        (nodeArena a W d) (PhysicalWalshCompileXorSwap.slice (fun s => stepsOf (world W i j D s)) i j) (c (D,(a+1,ops),i.val,j.val)) := by
  obtain ⟨R,E,c,h,hr,run⟩ := compiledFor stepsOf known bound
  refine ⟨R,E,c ∘ rawKey,h.comp primrec_rawKey.to_comp,fun _ => hr _,?_⟩
  intro a W ops eqW i j ne D d hD
  dsimp only [rawKey,Function.comp_apply]
  rw [← Packed.decode_shape,show (Packed.decode (a+1) ops).shape.1.1 = W from eqW]
  exact run a W i j ne D d hD

/-- Full or fixed-degree low bits selected from the raw template. -/
theorem compile (trim : Bool) : ∃ (R E : ℕ) (c : ℕ × PhysicalWalshCompileXorSwap.Params → Cmd),
    Effective ltr c ∧ (∀ k, Within R (c k)) ∧
    ∀ a W (ops : List Op), (Packed.decode (a+1) ops).i = W → ∀ (i j : Fin (a+1)), i ≠ j → ∀ D d, E ≤ d →
      PhysicalWalshCompileXorRoute.Flat (a:=a) (W:=W) (nodeScan a W d (ElementarySweep.prefixExtra (a+1) (cut trim D (a+1))))
        (nodeArena a W d) (PhysicalWalshCompileXorSwap.slice (cut trim D (a+1)) i j) (c (D,(a+1,ops),i.val,j.val)) :=
  compileFor (PhysicalWalshCompileElementaryAgenda.steps trim)
    (PhysicalWalshCompileElementaryAgenda.steps_realizes trim)
    (PhysicalWalshCompileElementaryAgenda.steps_le trim)

end PhysicalWalshCompileElementaryRelease

end NearSquareRoot
end Computability
end OAI

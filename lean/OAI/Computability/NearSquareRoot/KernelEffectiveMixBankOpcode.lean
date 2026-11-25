import OAI.Computability.NearSquareRoot.KernelEffectiveMixBank
import OAI.Computability.NearSquareRoot.KernelEffectiveMixBankBounds
import OAI.Computability.NearSquareRoot.KernelEffectiveMixBankRoute
import OAI.Computability.NearSquareRoot.KernelEffectiveMix

/-! # Physical bank commands generated from literal mix instructions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveMixBank

open IntegerMultiplication IntegerMultiplication.Code CommonRegisters GeneratorSyntax
open KernelPass KernelPass.ComputableSyntax KernelPassMix Filter

/-- For each raw opcode the output file encodes the actual command on the tape.
All executions restore the opaque control fields along with the two arithmetic
rulers. Register support is uniform even for malformed literal opcodes. -/
theorem compileOpcode {H : Type} [Codec H] (key : H → Rulers) (hk : Code.Easy key) :
    ∀ᶠ R in atTop, ∃ c : Op → Cmd, Effective ltr c ∧ ∀ op, Within R (c op) ∧
      Sound (c op) key (arg op 0) (arg op 1) (mixMarked (EffectiveMix.coeff op)) :=
  compile key hk _ _ (primrec_arg.comp Primrec.id (.const 0)).to_comp
    (primrec_arg.comp Primrec.id (.const 1)).to_comp _ EffectiveMix.markedFamily

open PhysicalWalsh PhysicalWalshContext

/-- The command family can be selected before the shape, meter, and input are
known. It implements the decoded mix leaf on every ready recursive packet. -/
theorem compileRoute (D : Type) [Codec D] :
    ∀ᶠ R in atTop, ∃ c : Op → Cmd, Effective ltr c ∧ ∀ op, Within R (c op) ∧
      ∀ {a : ℕ} {U F X : Type} (L : KernelScaleBank.Layout a U F) (w : U → ℕ) (desc : U → D)
        (m : Meter U), (∀ s, routeArena L w desc s ≤ m.arena s) →
        ∀ (xor : Fin (a+1) × Fin (a+1) → ∀ s, PhysicalWalshGrid.Row L w s → PhysicalWalshGrid.Row L w s)
          (child : Fin (a+1) → ∀ s, PhysicalWalshGrid.Row L w s → PhysicalWalshGrid.Row L w s)
          (xorReady : Fin (a+1) × Fin (a+1) → ∀ s, PhysicalWalshGrid.Row L w s → Prop)
          (childReady : Fin (a+1) → ∀ s, PhysicalWalshGrid.Row L w s → Prop)
          (u : X → U), op.1 = 0 →
          PhysicalWalshCompile.Implements (routeOps L w desc xor child)
            (routeGuards L w desc xorReady childReady) m u (Packed.leaf (a+1) op) (c op) := by
  have select : Code.Easy (routeKey D) := Easy.fst.compose Easy.fst
  filter_upwards [compileOpcode (routeKey D) select] with R hc
  obtain ⟨c,he,h⟩ := hc
  exact ⟨c,he,fun op => ⟨(h op).1,fun L w d _ fits xor child xr cr u tag =>
    implements_leaf_mix L w d fits xor child xr cr u op tag (c op) (h op).2⟩⟩

end KernelEffectiveMixBank

end NearSquareRoot
end Computability
end OAI

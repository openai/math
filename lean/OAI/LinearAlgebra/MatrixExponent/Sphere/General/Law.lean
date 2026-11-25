import OAI.LinearAlgebra.MatrixExponent.Sphere.General.RawSpec

/-!
# General local concentration and binary bookkeeping

The fixed intermediate field and polynomial lower bound are chosen
before the scale. The working degree is measured over the original
field. The existence clause guarantees a nonempty working window.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Raw
open Filter SphereScale

def WorkingExtension (k K : Type) [Field k] [Field K] [Algebra k K] (A c T : ℕ) (L : ℝ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Algebra K F) (_ : Algebra k F)
    (_ : IsScalarTower k K F) (_ : Module.Finite k F),
    A * (1 + 2 * T) ^ A ≤ Fintype.card F ∧ Fintype.card F ≤ (T + 1) ^ c ∧
      (Module.finrank k F : ℝ) ≤ L * Real.log T

def BookkeepingLaw (k : Type) [Field k] (g ℓ D : ℕ) (hD : Input.threshold g ≤ D) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra k K)
      (p l b : ℕ) (_ : CharP K p) (_ : Fact p.Prime) (A : ℕ) (L : ℝ), 0 < L ∧
      ∀ c : ℕ, 5 * A + 2 ≤ c → ∃ B : ℕ, 0 < B ∧ ∀ᶠ T : ℕ in atTop,
        ∃ (d : ℕ) (sc : Input.PacketScales g ℓ D T p l b d)
          (hc : Ready K (ℓ + 1) (2 ^ Nat.clog 2 D) g (p ^ l) b d),
          0 < Input.unitSize g ℓ D T ∧ T ≤ Input.unitSize g ℓ D T * D ^ (2 * Input.terminalExponent g (ℓ + 1)) ∧
          WorkingExtension k K A c T L ∧
          ∀ (F : Type) [Field F] [Fintype F] [Algebra K F],
            A * (1 + 2 * T) ^ A ≤ Fintype.card F → Fintype.card F ≤ (T + 1) ^ c →
            ∃ _ : ExpChar F p, Family (F := F) sc hc hD A c B

end OAI.LinearAlgebra.MatrixExponent.Rounds.Raw

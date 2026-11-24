import OAI.Computability.VPVNP.FixedNativeRealization
import OAI.Computability.VPVNP.FixedProgramRoutes

/-!
# Reducing the final native compiler obligation to the compressed pair

The actual evaluator tail handles the second half of the diagonal chain.
A sufficiently large address multiplier makes its physical frames and
per-call budgets fit. Thus only the compressed first-half pair computation
enters the compiler premise below.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal

open Compression LiveProgram CursorNetwork Filter
universe u

namespace Program

variable {K : Type*} [Field K] {S : BlockSchedule K} (T : S.Templates)

/-- For arbitrarily large address multipliers, one fixed pair table realizes all sufficiently large input lengths. -/
def PairCompiler (C : ℕ) : Prop :=
  let u := pairExponents T
  ∀ (c : Constants) (hc : c.circuitExponent = C) (hm : c.motifLabels = Fintype.card T.Entry),
    2 ≤ c.chainPower → ∀ N : ℕ, ∃ b ≥ N, ∃ (hb : 1 ≤ b) (O : PairTable),
      let D := ofPaperConstants c CompressorReader.program O b hb (liveRatio u)
      ∀ᶠ n : ℕ in atTop, D.PairRuns T u C hc hm n

theorem nativeCompiler_of_pair (C : ℕ) (pairs : PairCompiler T C) : NativeCompiler T C := by
  let u := pairExponents T
  intro c hc hm ha N
  obtain ⟨b₀,tail⟩ := eventually_native_of_pairRuns T u C c CompressorReader.program hc hm
  obtain ⟨b,hb,hpos,O,hpair⟩ := pairs c hc hm ha (max N b₀)
  have stages := tail b ((le_max_right ..).trans hb) hpos O
  refine ⟨b,(le_max_left ..).trans hb,hpos,O,?_⟩
  filter_upwards [stages,hpair] with n route run
  exact route run

end Program

theorem uniform_of_pair_compilers
    (build : ∀ (C : ℕ), 1 ≤ C → ∀ (q : ℕ) (K : Type) [Field K] [IsAlgClosed K] [Countable K] [CharP K q],
      ∀ (S : BlockSchedule K) (T : S.Templates), (∃ κ : T.Entry → K, T.IsSolution κ) →
        Program.PairCompiler T C) : UniformPBound.{u} := by
  apply uniform_of_native_compilers
  intro C hC q K _ _ _ _ S T hT
  exact Program.nativeCompiler_of_pair T C (build C hC q K S T hT)

end FixedProgramDiagonal

end VPVNP
end Computability
end OAI

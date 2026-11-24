import OAI.Computability.VPVNP.FixedProgramSelection
import OAI.Computability.VPVNP.FixedProgramRealization
import OAI.Computability.VPVNP.FixedProgramDiagonal

/-!
# Specializing the diagonal to the fixed scalar reader and the native pair table

All scalar readers, advice powers and site clocks are those of the concrete
program. The compiler premise below concerns only executions on prepared
pair and tail groups. Its table and address multiplier are selected before
the eventual length. It does not prescribe the integer count of a whole
chain.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal

open Compression BurstRAM LiveProgram CursorNetwork Filter
universe u

namespace Program

variable {K : Type*} [Field K] {S : BlockSchedule K} (T : S.Templates)

/-- The address multiplier may be increased for the native compressed pair
implementation, after the scalar clock and advice powers have been fixed. -/
def NativeCompiler (C : ℕ) : Prop :=
  let u := pairExponents T
  ∀ c : Constants, c.circuitExponent = C → c.motifLabels = Fintype.card T.Entry →
    2 ≤ c.chainPower → ∀ N : ℕ, ∃ b ≥ N, ∃ (hb : 1 ≤ b) (O : PairTable),
      let D := ofPaperConstants c CompressorReader.program O b hb (liveRatio u)
      ∀ᶠ n : ℕ in atTop, D.NativeContinuations T u C n

theorem program_of_native (q C : ℕ) (native : NativeCompiler T C) :
    ∃ D : Program, D.Realizes T q C := by
  let u := pairExponents T
  obtain ⟨env,c,hC,hm,ha,b₀,hb₀,prepared⟩ := select_scalar T q C
  let cap := max (max (c.chainPower+1) (c.chainPower+c.deltaPower)) (max c.advicePower (grammarCapacityPower C)) + 2
  let N := max b₀ (max (max S.laneBits 5) cap)
  obtain ⟨b,hb,hpos,O,runs⟩ := native c hC hm ha N
  let D := ofPaperConstants c CompressorReader.program O b hpos (liveRatio u)
  have atB : b₀ ≤ b := (le_max_left ..).trans hb
  have lanes : max S.laneBits 5 ≤ b := (le_max_left ..).trans ((le_max_right ..).trans hb)
  have virtual : cap ≤ b := (le_max_right ..).trans ((le_max_right ..).trans hb)
  have data := prepared b atB O
  refine ⟨D,?_⟩
  apply D.realizes_of_continuations T u q C evaluatorPorts env hC hm rfl rfl rfl lanes virtual
  · filter_upwards [data] with n h
    obtain ⟨_,h⟩ := h
    exact h
  · exact runs

end Program

/-- The only remaining compiler inputs are prepared single-group execution
proofs for the fixed native implementation. The scalar evaluator, processor
coefficient, weighted algebraic contradiction, and common field threshold
all follow from the compiled development. -/
theorem uniform_of_native_compilers
    (build : ∀ (C : ℕ), 1 ≤ C → ∀ (q : ℕ) (K : Type) [Field K] [IsAlgClosed K] [Countable K] [CharP K q],
      ∀ (S : BlockSchedule K) (T : S.Templates), (∃ κ : T.Entry → K, T.IsSolution κ) →
        Program.NativeCompiler T C) : UniformPBound.{u} := by
  apply uniform_bound_of_local_programs
  intro C hC q K _ _ _ _ S T hT
  exact Program.program_of_native T q C (build C hC q K S T hT)

end FixedProgramDiagonal

end VPVNP
end Computability
end OAI

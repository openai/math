import OAI.Computability.VPVNP.RAMTapePublicGeometry
import OAI.Computability.VPVNP.RAMTapeProcessorStartup
import OAI.Computability.VPVNP.RAMProcessorReset

/-!
# Loading parsed public geometry into the arithmetic interpreter

The physical parser supplies the four unary parameters and its zero-bit
template. The converter writes the four public operands of the ISA bank,
copies the template into its persistent word, and initializes its padded
register words and empty private log. The existing processor stacks are
available throughout the expression evaluation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicGeometry.Physical

open BurstRAM LiveProgram PublicExprMachine

/-- Joint bank of parsed processor data and the four-public-input arithmetic interpreter. -/
abbrev Port (r : ℕ) := ProcessorPublic.Port ⊕ ISA.Port r 4

instance (r : ℕ) : DecidableEq (Port r) := by
  letI : DecidableEq ProcessorPublic.Port := inferInstance
  infer_instance

noncomputable instance (r : ℕ) : Fintype (Port r) := by
  letI : Fintype ProcessorPublic.Port := inferInstance
  infer_instance

private def unaryPort : Fin 4 → ProcessorPublic.Port :=
  ![ProcessorPublic.lengthPort, ProcessorPublic.addressWidthPort, ProcessorPublic.bucketPort, ProcessorPublic.widthPort]

private def zeros : ProcessorPublic.Port := .inl SiteSetup.zerosPort

private def embed (r : ℕ) : PublicGeometry.Port → Port r
  | .unary i => .inl (unaryPort i)
  | .word i => .inr (.pub i)
  | .zeros => .inl zeros
  | .pending => .inr (.work 1)
  | .tmp => .inr (.work 0)

private theorem embed_injective (r : ℕ) : Function.Injective (embed r) := by
  have hu : Function.Injective unaryPort := by decide
  have hz : ∀ i, unaryPort i ≠ zeros := by decide
  intro a b he
  cases a <;> cases b <;> simp [embed, hz, Ne.symm (hz _)] at he ⊢ <;> first | assumption | exact hu he

/-- Enter the fixed arithmetic routine with an initialized ISA bank.
The number of arithmetic registers belongs to the fixed expression code. -/
def prepare (r : ℕ) : FiniteRoutine (Port r) :=
  (((PublicGeometry.prepare.onPorts (embed r)).followedBy
    (SuccessorFields.prependCopy (.inl zeros) (.inr .persistent) (.inr (.work 0)))).followedBy
    (ISA.freshCall.onPorts Sum.inr))

/-- Time for loading the four public inputs, padding the persistent word,
and initializing the requested private arithmetic register bank. -/
def budget (g : Geometry) (r : ℕ) := PublicGeometry.steps g + (5*g.w+2) + (r*(8*g.w+3)+5)

variable {r : ℕ}

theorem prepare_runs (g : Geometry) (processor : Stacks ProcessorPublic.Port)
    (hn : processor ProcessorPublic.lengthPort = List.replicate g.n true)
    (hd : processor ProcessorPublic.addressWidthPort = List.replicate g.d true)
    (hH : processor ProcessorPublic.bucketPort = List.replicate g.H true)
    (hw : processor ProcessorPublic.widthPort = List.replicate g.w true)
    (hz : processor (.inl SiteSetup.zerosPort) = List.replicate g.w false)
    (hfit : ∀ i, geometryNat g i < 2^g.w) :
    ∃ t ≤ budget g r, (prepare r).Runs t (Sum.elim processor (fun _ => []))
      (Sum.elim processor (ISA.bank (geometryWords g) 0 (fun _ => 0) [])) := by
  change processor zeros = List.replicate g.w false at hz
  let empty : Stacks (ISA.Port r 4) := fun _ => []
  let loaded : Stacks (ISA.Port r 4) := fun p =>
    match p with
    | .pub i => wordBits (geometryWords g i)
    | _ => []
  let dest := ISA.preCall (geometryWords g) (0 : Word g.w) (fun _ : Fin r => []) []
  have hsource (i : Fin 4) : processor (unaryPort i) = List.replicate (geometryNat g i) true := by
    fin_cases i <;> first | exact hn | exact hd | exact hH | exact hw
  have cv : (PublicGeometry.prepare.onPorts (embed r)).Runs (PublicGeometry.steps g)
      (Sum.elim processor empty) (Sum.elim processor loaded) := by
    apply FiniteRoutine.runs_onPorts_framed _ (embed_injective r) (PublicGeometry.runs g hfit)
    · intro j
      cases j <;> first | rfl | exact hsource _ | exact hz
    · intro j
      cases j <;> first | rfl | exact hsource _ | exact hz
    · rintro (j | j) h
      · rfl
      · cases j with
        | pub i => exact (h (.word i) rfl).elim
        | reg | work | persistent | logPort => rfl
  have copy := SuccessorFields.prependCopy_runs (Sum.inl zeros : Port r) (.inr .persistent) (.inr (.work 0))
    (by simp) (by simp) (by simp) (Sum.elim processor loaded) rfl
  have copyResult : Function.update (Sum.elim processor loaded) (.inr .persistent)
      (processor zeros ++ loaded .persistent) = Sum.elim processor dest := by
    funext p
    rcases p with i | i
    · rfl
    · cases i with
      | persistent =>
        change processor zeros ++ [] = wordBits (0 : Word g.w)
        rw [List.append_nil, hz, UnaryWord.zeros_wordBits]
      | reg | pub | work => rfl
      | logPort j => cases j <;> rfl
  change (SuccessorFields.prependCopy (.inl zeros) (.inr .persistent) (.inr (.work 0))).Runs
    (5*(processor zeros).length+2) (Sum.elim processor loaded)
    (Function.update (Sum.elim processor loaded) (.inr .persistent) (processor zeros ++ loaded .persistent)) at copy
  rw [copyResult, hz, List.length_replicate] at copy
  obtain ⟨u,hu,reset⟩ := ISA.freshCall_run (geometryWords g) (0 : Word g.w) (fun _ : Fin r => []) [] (by simp)
  have reset' : (ISA.freshCall.onPorts Sum.inr).Runs u (Sum.elim processor dest)
      (Sum.elim processor (ISA.bank (geometryWords g) 0 (fun _ => 0) [])) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inr_injective reset
    · intro _; rfl
    · intro _; rfl
    · rintro (j | j) hj
      · rfl
      · exact (hj j rfl).elim
  exact ⟨_, Nat.add_le_add_left (by simpa using hu) _, (cv.followedBy copy).followedBy reset'⟩

end RAMTape.PublicGeometry.Physical

end VPVNP
end Computability
end OAI

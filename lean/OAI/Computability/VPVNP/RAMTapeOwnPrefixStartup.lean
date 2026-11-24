import OAI.Computability.VPVNP.RAMTapeOwnPrefix
import OAI.Computability.VPVNP.RAMTapePublicGeometryStartup
import OAI.Computability.VPVNP.RAMTapePublicInputOperands
import OAI.Computability.VPVNP.LivePublicCounterOperands

/-!
# The six live public inputs from the original site tape

The physical processor first parses its own tape and computes the four
geometry words. It retains the literal self-delimiting prefix on a stack.
A fixed routine copies that stack into the fifth and sixth public fields
as its length and packed value. The startup code has no program-text operand.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.OwnPrefix.Physical

open BurstRAM LiveProgram RAMLayout ProcessorInput StackCompiler PublicExprMachine

/-- Combined physical processor ports and arithmetic bank with six public inputs, including the
two parsed prefix words. -/
abbrev Port (r : ℕ) := ProcessorPublic.Port ⊕ ISA.Port r 6

instance (r : ℕ) : DecidableEq (Port r) := by
  letI : DecidableEq ProcessorPublic.Port := inferInstance
  infer_instance

noncomputable instance (r : ℕ) : Fintype (Port r) := by
  letI : Fintype ProcessorPublic.Port := inferInstance
  infer_instance

/-- Processor stack retaining the complete parsed self-delimiting prefix. -/
def savedPrefix : ProcessorPublic.Port := .inl (.inl (.inl .prefix))

private def widen {r : ℕ} : PublicGeometry.Physical.Port r → Port r :=
  Sum.map id InputOperandMachine.embed

private theorem widen_injective (r : ℕ) : Function.Injective (widen (r := r)) :=
  Sum.map_injective.mpr ⟨Function.injective_id, InputOperandMachine.embed_inj⟩

/-- Intermediate arithmetic bank containing the four geometry words, empty prefix-word slots,
and zero-valued registers and persistent word. -/
def geometryBank (r : ℕ) (g : Geometry) : Stacks (ISA.Port r 6)
  | .pub i => if h : i.val < 4 then wordBits (geometryWords g ⟨i.val, h⟩) else []
  | .reg _ | .persistent => wordBits (0 : Word g.w)
  | .work _ | .logPort _ => []

private theorem widen_geometry {r : ℕ} (g : Geometry) (processor : Stacks ProcessorPublic.Port)
    (raw : List Bool) (code : FiniteRoutine (PublicGeometry.Physical.Port r)) {t : ℕ}
    (h : code.Runs t (labeledInput (.inl ProcessorPublic.rawPort) raw)
      (Sum.elim processor (ISA.bank (geometryWords g) 0 (fun _ => 0) []))) :
    (code.onPorts widen).Runs t (labeledInput (.inl ProcessorPublic.rawPort) raw)
      (Sum.elim processor (geometryBank r g)) := by
  apply FiniteRoutine.runs_onPorts_framed _ (widen_injective r) h
  · rintro (j | j)
    · simp [widen, labeledInput]
    · cases j <;> simp [widen, InputOperandMachine.embed, labeledInput]
  · rintro (j | j)
    · rfl
    · cases j with
      | pub i => simp [widen, InputOperandMachine.embed, geometryBank, i.isLt, ISA.bank]
      | logPort i => cases i <;> rfl
      | _ => rfl
  · rintro (j | j) hj
    · exact (hj (.inl j) rfl).elim
    · cases j with
      | pub i =>
        by_cases hi : i.val < 4
        · have he : widen (.inr (.pub ⟨i.val, hi⟩) : PublicGeometry.Physical.Port r) = .inr (.pub i) := by
            simp [widen, InputOperandMachine.embed]
          exact (hj _ he).elim
        · simp [geometryBank, hi, labeledInput]
      | reg i => exact (hj (.inr (.reg i)) rfl).elim
      | persistent => exact (hj (.inr .persistent) rfl).elim
      | work i => exact (hj (.inr (.work i)) rfl).elim
      | logPort i => exact (hj (.inr (.logPort i)) rfl).elim

private def source (r : ℕ) : SiteRecordWords.Port → Port r
  | .header => .inl savedPrefix
  | .width => .inl ProcessorPublic.widthPort
  | .headerWord => .inr (.pub 5)
  | .addressWord => .inr (.pub 4)
  | .count => .inr (.work 0)
  | .tmp => .inr (.work 1)
  | .siteLog => .inr (.work 2)
  | .address => .inr (.work 3)

private theorem source_injective (r : ℕ) : Function.Injective (source r) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [source, savedPrefix, ProcessorPublic.widthPort, SiteSetup.wordPort]

private theorem pack_geometry (r : ℕ) (g : Geometry) (prog : UniversalMachine.Program)
    (processor : Stacks ProcessorPublic.Port) (hp : processor savedPrefix = UniversalMachine.programPrefix prog)
    (hwidth : processor ProcessorPublic.widthPort = List.replicate g.w true)
    (hf : (UniversalMachine.programPrefix prog).length ≤ g.w) :
    (OwnPrefix.program.onPorts (source r)).Runs (steps g.w (UniversalMachine.programPrefix prog).length)
      (Sum.elim processor (geometryBank r g))
      (Sum.elim processor (ISA.bank (InputOperandMachine.input g (CounterPublic.actualPrefix prog)) 0 (fun _ => 0) [])) := by
  let s := (Sum.elim processor (geometryBank r g)) ∘ source r
  have hpre : s .header = UniversalMachine.programPrefix prog := hp
  have hr := OwnPrefix.runs s g.w (hpre ▸ hf) hwidth rfl rfl rfl rfl
  rw [hpre, prefixWordBits prog hf] at hr
  have hv : SiteRecordWords.addressWord hf (PrimedInputRAM.Opcodes.packedPrefix prog) =
      packed g.w (PrimedInputRAM.Opcodes.packedPrefix prog).val := by
    apply Fin.ext
    exact (Nat.mod_eq_of_lt ((PrimedInputRAM.Opcodes.packedPrefix prog).isLt.trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) hf))).symm
  apply FiniteRoutine.runs_onPorts_framed _ (source_injective r) hr
  · intro j; rfl
  · intro j
    cases j <;> first | rfl | (change wordBits _ = wordBits _; exact congrArg wordBits hv.symm)
  · rintro (j | j) hj
    · rfl
    · cases j with
      | pub i =>
        fin_cases i <;> first | rfl | exact (hj .headerWord rfl).elim | exact (hj .addressWord rfl).elim
      | logPort i => cases i <;> rfl
      | _ => rfl

/-- Parse and load the physical operand bank. Its fixed code depends only
on the register count and the cost parameters of the processor. -/
def startup (r B a b u lit : ℕ) (hb : 0 < b) : FiniteRoutine (Port r) :=
  ((PublicGeometry.Physical.startup r B a b u lit hb).onPorts widen).followedBy
    (OwnPrefix.program.onPorts (source r))

theorem startup_runs (r B a b u lit : ℕ) (hB : 1 ≤ B) (hb : 0 < b) (hab : a ≤ b) (hu : 1 ≤ u)
    (prog : UniversalMachine.Program) (n : ℕ) (hn : 1 ≤ n) :
    let d := B * Nat.clog 2 n
    let e := roundedUp a b n
    let w := (d+10)^4
    let g : Geometry := ⟨n, d, 2^e, w⟩
    ∀ (v : Word d) (hdr : Header) (inc : Fin (width d (2^e) w) → Bool), Fits prog n d (2^e) w →
      (UniversalMachine.programPrefix prog).length ≤ w →
      let processor := ProcessorPublic.recordResult (ProcessorPublic.rawResult prog n d (2^e) w v hdr inc)
        n d e w u lit v hdr (ProcessorPublic.capFits B a b n hB hb hab hn) (ProcessorPublic.recordWidth_ge_four d)
      ∃ t ≤ (ProcessorPublic.recordClockCoefficient B a b u + 183 + 11*r)*(n+1)^max 7 (u+1),
        (startup r B a b u lit hb).Runs t
          (labeledInput (.inl ProcessorPublic.rawPort) (ProcessorInput.tape prog n v hdr inc))
          (Sum.elim processor (ISA.bank (InputOperandMachine.input g (CounterPublic.actualPrefix prog)) 0
            (fun _ => 0) [])) := by
  intro d e w g v hdr inc fit hf processor
  obtain ⟨s, hs, hrun⟩ := PublicGeometry.Physical.startup_runs r B a b u lit hB hb hab hu prog n hn v hdr inc fit
  have hgeo := widen_geometry g processor _ _ hrun
  have hprefix := pack_geometry r g prog processor rfl rfl hf
  refine ⟨_, ?_, hgeo.followedBy hprefix⟩
  have hw : w ≤ n := by
    change (UniversalMachine.programPrefix prog).length + (d + 4 + width d (2^e) w) ≤ n at fit
    rw [width_eq] at fit
    omega
  have h₂ : (w+1)^2 ≤ (n+1)^max 7 (u+1) := (Nat.pow_le_pow_left (Nat.succ_le_succ hw) 2).trans
    (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))
  have hl := (steps_le hf).trans (Nat.mul_le_mul_left 43 h₂)
  exact (Nat.add_le_add hs hl).trans (by ring_nf; rfl)

end RAMTape.OwnPrefix.Physical

end VPVNP
end Computability
end OAI

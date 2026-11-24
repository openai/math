import OAI.Computability.VPVNP.RAMTapeOwnPrefixStartup

/-!
# Computing the live operand vector with the processor's own code as data

Compose the six-word physical startup with the finite arithmetic expression
loader. The primed assembler's length and packed-prefix slots agree with its
specification for the actual program, although the loader is fixed before
this program is chosen.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.OwnPrefix.Physical

open BurstRAM LiveProgram RAMLayout ProcessorInput StackCompiler PublicExprMachine

variable {k : ℕ}

/-- Parse the physical site and its prefix into six public words, then run the operand program
on that bank. -/
def operandStartup (args : Fin k → InputOperand) (B a b u lit : ℕ) (hb : 0 < b) :
    FiniteRoutine (Port (InputOperandMachine.registers args)) :=
  (startup _ B a b u lit hb).followedBy ((InputOperandMachine.program args).onPorts Sum.inr)

/-- Clock coefficient for parsing the physical inputs, packing the actual prefix, evaluating
geometry, and filling the operand slots. -/
def operandCoefficient (args : Fin k → InputOperand) (B a b u : ℕ) :=
  ProcessorPublic.recordClockCoefficient B a b u + 183 + 11*InputOperandMachine.registers args +
    coefficient (InputOperandMachine.geometryOnly args) + 11*k + 2

theorem operand_runs (args : Fin k → InputOperand) (B a b u lit : ℕ)
    (hB : 1 ≤ B) (hb : 0 < b) (hab : a ≤ b) (hu : 1 ≤ u)
    (prog : UniversalMachine.Program) (n : ℕ) (hn : 1 ≤ n) :
    let d := B * Nat.clog 2 n
    let e := roundedUp a b n
    let w := (d+10)^4
    let g : Geometry := ⟨n, d, 2^e, w⟩
    ∀ (v : Word d) (hdr : Header) (inc : Fin (width d (2^e) w) → Bool), Fits prog n d (2^e) w →
      (UniversalMachine.programPrefix prog).length ≤ w →
      (∀ i, (InputOperandMachine.geometryOnly args i).Fits g (2^w)) →
      let processor := ProcessorPublic.recordResult (ProcessorPublic.rawResult prog n d (2^e) w v hdr inc)
        n d e w u lit v hdr (ProcessorPublic.capFits B a b n hB hb hab hn) (ProcessorPublic.recordWidth_ge_four d)
      ∃ t ≤ operandCoefficient args B a b u * (n+1)^max 7 (u+1),
        ∃ out : Fin (InputOperandMachine.registers args) → Word w,
          (operandStartup args B a b u lit hb).Runs t
            (labeledInput (.inl ProcessorPublic.rawPort) (ProcessorInput.tape prog n v hdr inc))
            (Sum.elim processor (ISA.bank (InputOperandMachine.input g (CounterPublic.actualPrefix prog)) 0 out [])) ∧
          ∀ j, out (InputOperandMachine.slot args j) = Pieces.word g (CounterPublic.actualPrefix prog) (args j) := by
  intro d e w g v hdr inc fit hp hf processor
  obtain ⟨s, hs, hstart⟩ := startup_runs (InputOperandMachine.registers args) B a b u lit hB hb hab hu
    prog n hn v hdr inc fit hp
  obtain ⟨t, ht, out, hop, hout⟩ := InputOperandMachine.runs args g (CounterPublic.actualPrefix prog)
    hf 0 (fun _ => 0) []
  have lifted : ((InputOperandMachine.program args).onPorts Sum.inr).Runs t
      (Sum.elim processor (ISA.bank (InputOperandMachine.input g (CounterPublic.actualPrefix prog)) 0 (fun _ => 0) []))
      (Sum.elim processor (ISA.bank (InputOperandMachine.input g (CounterPublic.actualPrefix prog)) 0 out [])) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inr_injective hop
    · intro; rfl
    · intro; rfl
    · rintro (i|i) h
      · rfl
      · exact (h i rfl).elim
  refine ⟨_, ?_, out, hstart.followedBy lifted, hout⟩
  let K := (n+1)^max 7 (u+1)
  have hK : 1 ≤ K := one_le_pow₀ (by omega)
  have hw : w ≤ n := by
    change (UniversalMachine.programPrefix prog).length + (d + 4 + width d (2^e) w) ≤ n at fit
    rw [width_eq] at fit
    omega
  have hw₂ : (w+1)^2 ≤ K := (Nat.pow_le_pow_left (Nat.succ_le_succ hw) 2).trans
    (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))
  have hw₁ : w + 1 ≤ K := (Nat.succ_le_succ hw).trans (Nat.le_self_pow (by omega) _)
  have hm : k*(8*w+3) ≤ (11*k)*K := calc
    _ ≤ k*(11*K) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring
  have ht' : t ≤ (coefficient (InputOperandMachine.geometryOnly args) + 11*k + 2)*K := by
    change t ≤ coefficient (InputOperandMachine.geometryOnly args)*(w+1)^2+k*(8*w+3)+2 at ht
    rw [Nat.add_mul, Nat.add_mul]
    exact ht.trans (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hw₂) hm) (by omega))
  exact (Nat.add_le_add hs ht').trans (by unfold operandCoefficient; dsimp [K]; ring_nf; rfl)

/-- Every fixed program's literal prefix eventually fits in one live word. -/
theorem eventually_prefix_fits (prog : UniversalMachine.Program) {B : ℕ} (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in Filter.atTop, (UniversalMachine.programPrefix prog).length ≤ CursorBounds.wordBits B n := by
  let P := (UniversalMachine.programPrefix prog).length
  filter_upwards [Filter.eventually_ge_atTop (2^(P+1))] with n hn
  have hn₀ : 0 < n := (Nat.two_pow_pos _).trans_le hn
  have hlarge := ((Nat.le_log2 hn₀.ne').mpr hn).trans (log2_le_addressWidth hB n)
  change P ≤ (addressWidth B n + 10)^4
  exact (show P ≤ addressWidth B n + 10 by omega).trans (Nat.le_self_pow (by decide) _)

end RAMTape.OwnPrefix.Physical

end VPVNP
end Computability
end OAI

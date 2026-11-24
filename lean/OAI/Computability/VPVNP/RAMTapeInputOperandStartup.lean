import OAI.Computability.VPVNP.RAMTapeOwnPrefixOperands
import OAI.Computability.VPVNP.RAMTapeSiteEntryFrame

/-!
# Installing parsed prefix and geometry operands in the site processor

The first arithmetic registers are the actual public ports of the burst
interpreter. Two site scratch stacks hold the packed prefix and its length
during initialization, then a fixed routine clears both stacks before the
successor guard. The sorting workspace remains available at entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputOperandStartup

open BurstRAM LiveProgram RAMLayout ProcessorInput StackCompiler PublicExprMachine
open SiteProcessorPorts (Frame)
open OwnPrefix.Physical (operandStartup operand_runs operandCoefficient)

variable {k : ℕ}

/-- Geometry expressions for operand slots, with zero placeholders for slots supplied from the
actual program prefix. -/
abbrev Expr (args : Fin k → InputOperand) := InputOperandMachine.geometryOnly args
/-- Combined site-processor bank for the private table and its parsed operand vector. -/
abbrev Target (r : ℕ) (args : Fin k → InputOperand) := SiteProcessorPorts.Port r (Expr args)
/-- Bank on which the physical prefix and operand initialization routines execute before their
ports are renamed. -/
abbrev Source (args : Fin k → InputOperand) := OwnPrefix.Physical.Port (InputOperandMachine.registers args)

/-- Map computed operands to the interpreter’s public registers and map the two temporary
prefix words to site scratch stacks. -/
def ports (r : ℕ) (args : Fin k → InputOperand) : Source args → Target r args
  | .inl p => SiteProcessorPorts.pub r _ p
  | .inr (.reg i) => if h : i.val < k then SiteProcessorPorts.native r _ (.isa (.pub ⟨i.val,h⟩))
      else .inl (.inr (.inr (.reg i)))
  | .inr (.pub i) =>
    if h : i.val < 4 then .inl (.inr (.inr (.pub ⟨i.val, h⟩)))
    else if i.val = 4 then SiteProcessorPorts.native r _ (.scratch 0)
    else SiteProcessorPorts.native r _ (.scratch 1)
  | .inr .persistent => .inl (.inr (.inr .persistent))
  | .inr (.work i) => .inl (.inr (.inr (.work i)))
  | .inr (.logPort i) => .inl (.inr (.inr (.logPort i)))

theorem ports_injective (r : ℕ) (args : Fin k → InputOperand) : Function.Injective (ports r args) := by
  let back : Target r args → Source args := fun
    | .inl (.inr (.inl p)) => .inl p
    | .inl (.inl (.isa (.pub i))) => .inr (.reg (InputOperandMachine.slot args i))
    | .inl (.inr (.inr (.reg i))) => .inr (.reg i)
    | .inl (.inr (.inr (.pub i))) => .inr (.pub (i.castAdd 2))
    | .inl (.inr (.inr .persistent)) => .inr .persistent
    | .inl (.inr (.inr (.work i))) => .inr (.work i)
    | .inl (.inr (.inr (.logPort i))) => .inr (.logPort i)
    | .inl (.inl (.scratch i)) => .inr (.pub (if i = 0 then 4 else 5))
    | _ => .inl ProcessorPublic.rawPort
  apply Function.LeftInverse.injective (g := back)
  rintro (j | j)
  · rfl
  · cases j with
    | reg i =>
      by_cases hi : i.val < k <;> simp [ports, hi, SiteProcessorPorts.native, back, InputOperandMachine.slot]
    | pub i => fin_cases i <;> rfl
    | _ => rfl

private def clear (args : Fin k → InputOperand) : FiniteRoutine (Source args) :=
  (ISA.clearList [.pub 4, .pub 5]).onPorts Sum.inr

/-- Initialize the operand vector from the parsed site, clear the two prefix-word scratch
stacks, and return on the processor’s own ports. -/
def program (r : ℕ) (args : Fin k → InputOperand) (B a b u lit : ℕ) (hb : 0 < b) :
    FiniteRoutine (Target r args) :=
  ((operandStartup args B a b u lit hb).followedBy (clear args)).onPorts (ports r args)

/-- Fixed coefficient in the operand-startup clock bound, including the final scratch cleanup. -/
def clockCoefficient (args : Fin k → InputOperand) (B a b u : ℕ) :=
  operandCoefficient args B a b u + 3

/-- The geometry arithmetic bank is kept apart from the site and sort work
stacks. Only the first arithmetic registers become site operands. -/
def result (r : ℕ) (args : Fin k → InputOperand) (g : Geometry)
    (proc : Stacks ProcessorPublic.Port) (out : Fin (InputOperandMachine.registers args) → Word g.w) :
    Stacks (Target r args)
  | .inl (.inl (.isa (.pub j))) => wordBits (out (InputOperandMachine.slot args j))
  | .inl (.inr (.inl j)) => proc j
  | .inl (.inr (.inr (.reg i))) => if i.val < k then [] else wordBits (out i)
  | .inl (.inr (.inr j)) => ISA.bank (geometryWords g) 0 out [] j
  | _ => []

private theorem install (r : ℕ) (args : Fin k → InputOperand) (g : Geometry) (pref : LiteralPrefix)
    (proc : Stacks ProcessorPublic.Port) (raw : List Bool) (out : Fin (InputOperandMachine.registers args) → Word g.w)
    (src : FiniteRoutine (Source args)) {t : ℕ}
    (h : src.Runs t (labeledInput (.inl ProcessorPublic.rawPort) raw)
      (Sum.elim proc (ISA.bank (InputOperandMachine.input g pref) 0 out []))) :
    ∃ t' ≤ t + 2*(g.w+1)+1, ((src.followedBy (clear args)).onPorts (ports r args)).Runs t'
      (labeledInput (SiteProcessorPorts.pub r _ ProcessorPublic.rawPort) raw) (result r args g proc out) := by
  let bank := ISA.bank (InputOperandMachine.input g pref) 0 out []
  let clean := ISA.cleared [.pub 4, .pub 5] bank
  obtain ⟨n, hn, hc⟩ := ISA.clearList_runs [.pub 4, .pub 5] bank g.w (by
    intro i hi; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> simp [bank, ISA.bank])
  have hc' : (clear args).Runs n (Sum.elim proc bank) (Sum.elim proc clean) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inr_injective hc
    · intro; rfl
    · intro; rfl
    · rintro (j|j) hj
      · rfl
      · exact (hj j rfl).elim
  refine ⟨t+n, by simp only [List.length_cons, List.length_nil] at hn; omega, ?_⟩
  apply FiniteRoutine.runs_onPorts_framed _ (ports_injective r args) (h.followedBy hc')
  · rintro (j|j)
    · simp [ports, SiteProcessorPorts.pub, labeledInput]
    · cases j with
      | reg i => by_cases hi : i.val < k <;> simp [ports, hi, SiteProcessorPorts.native, SiteProcessorPorts.pub, labeledInput]
      | pub i => fin_cases i <;> rfl
      | _ => rfl
  · rintro (j|j)
    · rfl
    · cases j with
      | reg i =>
        by_cases hi : i.val < k <;> simp [ports, hi, result, clean, bank, ISA.cleared, ISA.bank,
          SiteProcessorPorts.native, InputOperandMachine.slot]
      | pub i => fin_cases i <;> rfl
      | logPort i => cases i <;> rfl
      | _ => rfl
  · rintro (((j | (j|j)) | j)) hj
    · cases j with
      | isa x =>
        cases x with
        | pub i => exact (hj (.inr (.reg (InputOperandMachine.slot args i))) (by
            simp [ports, InputOperandMachine.slot, i.isLt, SiteProcessorPorts.native])).elim
        | _ => rfl
      | _ => rfl
    · exact (hj (.inl j) rfl).elim
    · cases j with
      | reg i =>
        by_cases hi : i.val < k
        · simp [result, hi, labeledInput, SiteProcessorPorts.pub]
        · exact (hj (.inr (.reg i)) (by simp [ports, hi])).elim
      | pub i =>
        exact (hj (.inr (.pub (i.castAdd 2))) (by simp [ports, i.isLt])).elim
      | persistent => exact (hj (.inr .persistent) rfl).elim
      | work i => exact (hj (.inr (.work i)) rfl).elim
      | logPort i => exact (hj (.inr (.logPort i)) rfl).elim
    · rfl

/-- The installed public bank is ready for the successor guard, the native
call interpreter, and the physical sorter. -/
theorem frame_runs (r : ℕ) (args : Fin k → InputOperand) (B a b u lit : ℕ)
    (hB : 1 ≤ B) (hb : 0 < b) (hab : a ≤ b) (hu : 1 ≤ u) (n : ℕ) (hn : 1 ≤ n) :
    let d := B * Nat.clog 2 n
    let e := roundedUp a b n
    let w := (d+10)^4
    let g : Geometry := ⟨n,d,2^e,w⟩
    ∀ (x : SiteCutBank.Input d e w), x.n = n → x.u = u → x.lit = lit →
      Fits x.prog n d (2^e) w → (UniversalMachine.programPrefix x.prog).length ≤ w →
      (∀ i, (Expr args i).Fits g (2^w)) →
      ∃ t ≤ clockCoefficient args B a b u * (n+1)^max 7 (u+1), ∃ s : Stacks (Target r args),
        (program r args B a b u lit hb).Runs t (labeledInput (SiteProcessorPorts.pub r (Expr args) ProcessorPublic.rawPort)
          (ProcessorInput.tape x.prog n x.v x.hdr (incidentBits x.sends x.v))) s ∧
        Frame r (Expr args) x (fun j => Pieces.word g (CounterPublic.actualPrefix x.prog) (args j)) s ∧
        ∀ j : SitePost.Port, s (.inr (.inr j)) = [] := by
  intro d e w g x hxn hxu hxl fit hp hf
  obtain ⟨t, ht, out, hrun, hout⟩ := operand_runs args B a b u lit hB hb hab hu x.prog n hn
    x.v x.hdr (incidentBits x.sends x.v) fit hp hf
  let proc := ProcessorPublic.recordResult (ProcessorPublic.rawResult x.prog n d (2^e) w x.v x.hdr
    (incidentBits x.sends x.v)) n d e w u lit x.v x.hdr x.hcap x.hw
  obtain ⟨t', ht', hlift⟩ := install r args g _ proc _ out _ hrun
  refine ⟨t', ?_, _, hlift, ?_, fun _ => rfl⟩
  · have hw : w ≤ n := by
      change (UniversalMachine.programPrefix x.prog).length + (d + 4 + width d (2^e) w) ≤ n at fit
      rw [width_eq] at fit
      omega
    let K := (n+1)^max 7 (u+1)
    have hK : n+1 ≤ K := Nat.le_self_pow (by omega) _
    change t' ≤ t+2*(w+1)+1 at ht'
    change t ≤ operandCoefficient args B a b u * K at ht
    change t' ≤ (operandCoefficient args B a b u+3)*K
    rw [Nat.add_mul]
    omega
  · constructor
    · rintro (j|j)
      · change proc j = _
        simp [proc, SiteCutBank.Input.prepared, hxn, hxu, hxl]
      · rfl
    · intro j
      cases j with
      | isa y =>
        cases y with
        | pub i => exact congrArg wordBits (hout i)
        | _ => rfl
      | _ => rfl

end RAMTape.InputOperandStartup

end VPVNP
end Computability
end OAI

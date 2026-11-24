import OAI.Computability.VPVNP.RAMTapePublicOperandStartup
import OAI.Computability.VPVNP.RAMProcessorBank

/-! # Installing the evaluated public operands in the actual processor bank

The first arithmetic registers are the instruction interpreter's public-word
ports. The arithmetic program reads and writes those ports directly. Its
temporary registers and the retained input fields have separate labels.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicOperandStartup

open BurstRAM LiveProgram RAMLayout ProcessorInput StackCompiler PublicExprMachine

variable {k : ℕ}

/-- Port space combining the site interpreter and the arithmetic source of its public operands. -/
abbrev Port (r : ℕ) (expr : Fin k → PublicExpr) := SiteProcessor.Port r k ⊕ Source expr

private def index (expr : Fin k → PublicExpr) (i : Fin k) : Fin (registerCount expr) :=
  ⟨i.val, by dsimp [registerCount, capacity]; omega⟩

/-- Identify the first arithmetic result registers with the interpreter’s public operand ports
and keep the other source ports separate. -/
def ports (r : ℕ) (expr : Fin k → PublicExpr) : Source expr → Port r expr
  | .inr (.reg i) => if h : i.val < k then .inl (.isa (.pub ⟨i.val,h⟩)) else .inr (.inr (.reg i))
  | p => .inr p

theorem ports_injective (r : ℕ) (expr : Fin k → PublicExpr) : Function.Injective (ports r expr) := by
  let back : Port r expr → Source expr := fun
    | .inl (.isa (.pub i)) => .inr (.reg (index expr i))
    | .inr p => p
    | _ => .inl ProcessorPublic.rawPort
  apply Function.LeftInverse.injective (g := back)
  rintro (p|p)
  · rfl
  · cases p with
    | reg i => by_cases hi : i.val < k <;> simp [ports, hi, back, index]
    | _ => rfl

/-- Exactly the public registers of the site interpreter are populated. -/
def siteWords (r : ℕ) (expr : Fin k → PublicExpr) (g : Geometry) : Stacks (SiteProcessor.Port r k)
  | .isa (.pub i) => wordBits (packed g.w ((expr i).eval g))
  | _ => []

/-- Original processor fields and all arithmetic workspace after initialization. -/
def result (r : ℕ) (expr : Fin k → PublicExpr) (g : Geometry) (processor : Stacks ProcessorPublic.Port) :
    Stacks (Port r expr)
  | .inl p => siteWords r expr g p
  | .inr (.inl p) => processor p
  | .inr (.inr (.reg i)) => if i.val < k then [] else arithmetic g expr (.reg i)
  | .inr (.inr p) => arithmetic g expr p

theorem result_public (r : ℕ) (expr : Fin k → PublicExpr) (g : Geometry)
    (processor : Stacks ProcessorPublic.Port) (i : Fin k) :
    result r expr g processor (.inl (.isa (.pub i))) = wordBits (packed g.w ((expr i).eval g)) := rfl

theorem result_processor (r : ℕ) (expr : Fin k → PublicExpr) (g : Geometry)
    (processor : Stacks ProcessorPublic.Port) (p : ProcessorPublic.Port) :
    result r expr g processor (.inr (.inl p)) = processor p := rfl

/-- Run the physical operand initializer on the port bank that installs its results directly in
the site interpreter. -/
def program (r : ℕ) (expr : Fin k → PublicExpr) (B p q u lit : ℕ) (hq : 0 < q) :
    FiniteRoutine (Port r expr) := (sourceProgram expr B p q u lit hq).onPorts (ports r expr)

private theorem install_run (r : ℕ) (expr : Fin k → PublicExpr) {t : ℕ} {src : FiniteRoutine (Source expr)}
    (g : Geometry) (processor : Stacks ProcessorPublic.Port) (tape : List Bool)
    (hr : src.Runs t (labeledInput (.inl ProcessorPublic.rawPort) tape) (Sum.elim processor (arithmetic g expr))) :
    (src.onPorts (ports r expr)).Runs t (labeledInput (.inr (.inl ProcessorPublic.rawPort)) tape)
      (result r expr g processor) := by
  apply FiniteRoutine.runs_onPorts_framed _ (ports_injective r expr) hr
  · rintro (p|p)
    · simp [ports, labeledInput]
    · cases p with
      | reg i => by_cases hi : i.val < k <;> simp [ports, hi, labeledInput]
      | _ => simp [ports, labeledInput]
  · rintro (p|p)
    · rfl
    · cases p with
      | reg i =>
        by_cases hi : i.val < k
        · simp [ports, hi, result, siteWords, arithmetic, output, ISA.bank]
        · simp [ports, hi, result]
      | _ => rfl
  · rintro (p | (p|p)) hp
    · cases p with
      | isa i =>
        cases i with
        | pub j =>
          exact (hp (.inr (.reg (index expr j))) (by simp [ports, index, j.isLt])).elim
        | _ => rfl
      | _ => rfl
    · exact (hp (.inl p) rfl).elim
    · cases p with
      | reg i =>
        by_cases hi : i.val < k
        · simp [result, hi, labeledInput]
        · exact (hp (.inr (.reg i)) (by simp [ports, hi])).elim
      | pub i => exact (hp (.inr (.pub i)) rfl).elim
      | persistent => exact (hp (.inr .persistent) rfl).elim
      | work i => exact (hp (.inr (.work i)) rfl).elim
      | logPort i => exact (hp (.inr (.logPort i)) rfl).elim

theorem runs (r : ℕ) (expr : Fin k → PublicExpr) (B p q u lit : ℕ) (hB : 1 ≤ B) (hq : 0 < q)
    (hpq : p ≤ q) (hu : 1 ≤ u) (prog : UniversalMachine.Program) (n : ℕ) (hn : 1 ≤ n) :
    let d := B*Nat.clog 2 n
    let e := roundedUp p q n
    let w := (d+10)^4
    let g : Geometry := ⟨n,d,2^e,w⟩
    ∀ (v : Word d) (hdr : Header) (inc : Fin (width d (2^e) w) → Bool), Fits prog n d (2^e) w →
      (∀ i, (expr i).Fits g (2^w)) →
      let processor := ProcessorPublic.recordResult (ProcessorPublic.rawResult prog n d (2^e) w v hdr inc)
        n d e w u lit v hdr (ProcessorPublic.capFits B p q n hB hq hpq hn) (ProcessorPublic.recordWidth_ge_four d)
      ∃ t ≤ clockCoefficient expr B p q u * (n+1)^(max 7 (u+1)), (program r expr B p q u lit hq).Runs t
        (labeledInput (.inr (.inl ProcessorPublic.rawPort)) (ProcessorInput.tape prog n v hdr inc))
        (result r expr g processor) := by
  intro d e w g v hdr inc fit hf processor
  obtain ⟨t,ht,hr⟩ := source_runs expr B p q u lit hB hq hpq hu prog n hn v hdr inc fit hf
  exact ⟨t, ht, install_run r expr g processor _ hr⟩

end RAMTape.PublicOperandStartup

end VPVNP
end Computability
end OAI

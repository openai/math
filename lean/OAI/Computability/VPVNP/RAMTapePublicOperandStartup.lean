import OAI.Computability.VPVNP.RAMTapePublicExprVector
import OAI.Computability.VPVNP.RAMTapePublicGeometryStartup

/-! # Computing the live table's public operands from the original site input

The geometry parser, word initialization and expression interpreter form one
fixed finite control. It retains the processor's record fields and leaves the
operand vector at the front of its arithmetic register bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicOperandStartup

open BurstRAM LiveProgram RAMLayout ProcessorInput StackCompiler PublicExprMachine

variable {k : ℕ}

/-- Port bank of the physical geometry parser and the register file sized for the expression
vector. -/
abbrev Source (expr : Fin k → PublicExpr) := PublicGeometry.Physical.Port (registerCount expr)

/-- Initialize the geometry words from the raw tape, then evaluate the expression vector on the
arithmetic bank. -/
def sourceProgram (expr : Fin k → PublicExpr) (B p q u lit : ℕ) (hq : 0 < q) :
    FiniteRoutine (Source expr) :=
  (PublicGeometry.Physical.startup (registerCount expr) B p q u lit hq).followedBy
    ((vector expr).onPorts Sum.inr)

/-- Arithmetic output bank with the geometry inputs, evaluated operand vector, zero persistent
word, and empty private log. -/
def arithmetic (g : Geometry) (expr : Fin k → PublicExpr) :=
  ISA.bank (geometryWords g) 0 (output g expr) []

/-- Fixed clock coefficient for physical geometry startup, register allocation, and vector
evaluation. -/
def clockCoefficient (expr : Fin k → PublicExpr) (B p q u : ℕ) :=
  ProcessorPublic.recordClockCoefficient B p q u + 140 + 11*registerCount expr + coefficient expr + 1

theorem source_runs (expr : Fin k → PublicExpr) (B p q u lit : ℕ) (hB : 1 ≤ B) (hq : 0 < q)
    (hpq : p ≤ q) (hu : 1 ≤ u) (prog : UniversalMachine.Program) (n : ℕ) (hn : 1 ≤ n) :
    let d := B*Nat.clog 2 n
    let e := roundedUp p q n
    let w := (d+10)^4
    let g : Geometry := ⟨n,d,2^e,w⟩
    ∀ (v : Word d) (hdr : Header) (inc : Fin (width d (2^e) w) → Bool), Fits prog n d (2^e) w →
      (∀ i, (expr i).Fits g (2^w)) →
      let processor := ProcessorPublic.recordResult (ProcessorPublic.rawResult prog n d (2^e) w v hdr inc)
        n d e w u lit v hdr (ProcessorPublic.capFits B p q n hB hq hpq hn) (ProcessorPublic.recordWidth_ge_four d)
      ∃ t ≤ clockCoefficient expr B p q u * (n+1)^(max 7 (u+1)),
        (sourceProgram expr B p q u lit hq).Runs t
          (labeledInput (.inl ProcessorPublic.rawPort) (ProcessorInput.tape prog n v hdr inc))
          (Sum.elim processor (arithmetic g expr)) := by
  intro d e w g v hdr inc fit hf processor
  obtain ⟨t,ht,init⟩ := PublicGeometry.Physical.startup_runs (registerCount expr) B p q u lit hB hq hpq hu
    prog n hn v hdr inc fit
  obtain ⟨s,hs,arith⟩ := vector_runs g expr hf 0 (fun _ => 0) []
  have installed : ((vector expr).onPorts (Sum.inr : _ → Source expr)).Runs s
      (Sum.elim processor (ISA.bank (geometryWords g) 0 (fun _ => 0) [])) (Sum.elim processor (arithmetic g expr)) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inr_injective arith
    · intro; rfl
    · intro; rfl
    · rintro (x|x) hx
      · rfl
      · exact (hx x rfl).elim
  refine ⟨_, ?_, init.followedBy installed⟩
  have hw : w ≤ n := by
    change (UniversalMachine.programPrefix prog).length + (d + 4 + width d (2^e) w) ≤ n at fit
    rw [width_eq] at fit
    omega
  let K := (n+1)^(max 7 (u+1))
  have hK : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
  have hpow : (w+1)^2 ≤ K := (Nat.pow_le_pow_left (Nat.succ_le_succ hw) 2).trans
    (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))
  have h₂ := (Nat.add_le_add (Nat.mul_le_mul_left (coefficient expr) hpow) hK)
  change s ≤ coefficient expr * (w+1)^2 + 1 at hs
  exact (Nat.add_le_add ht (hs.trans h₂)).trans (by unfold clockCoefficient; dsimp [K]; ring_nf; rfl)

end RAMTape.PublicOperandStartup

end VPVNP
end Computability
end OAI

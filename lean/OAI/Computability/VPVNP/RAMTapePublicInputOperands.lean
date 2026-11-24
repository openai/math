import OAI.Computability.VPVNP.LiveProgramPieces
import OAI.Computability.VPVNP.RAMTapePublicExprVector
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-!
# Loading a fixed operand vector from geometry and a parsed program prefix

The physical operand bank has six inputs. The first four are the parsed
geometry. The remaining two are the length and packed value of the actual
program prefix read from the input tape. The program fills the expression
slots, then copies the two parsed words to each of their designated slots.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputOperandMachine

open BurstRAM BurstRAM.PrivateRAM LiveProgram PublicExprMachine

variable {k : ℕ}

/-- Replace the two prefix-derived operand forms by literal zero while retaining the geometry
expressions in their own slots. -/
def geometryOnly (args : Fin k → InputOperand) (i : Fin k) : PublicExpr :=
  match args i with
  | .geometry e => e
  | _ => .lit 0

/-- Register count needed for evaluating the geometry part of the input operand vector. -/
abbrev registers (args : Fin k → InputOperand) := registerCount (geometryOnly args)

/-- The six public inputs, in order, are the four geometry words followed by the packed length
and value of the parsed prefix. -/
def input (g : Geometry) (lit : LiteralPrefix) : Fin 6 → Word g.w :=
  Fin.append (geometryWords g) ![packed g.w lit.length, packed g.w lit.value]

/-- Embed the geometry interpreter’s four public ports into the first four of six while
retaining its other port names. -/
def embed {r : ℕ} : ISA.Port r 4 → ISA.Port r 6
  | .pub i => .pub (i.castAdd 2)
  | .reg i => .reg i
  | .persistent => .persistent
  | .work i => .work i
  | .logPort i => .logPort i

theorem embed_inj {r : ℕ} : Function.Injective (@embed r) := by
  intro a b h
  cases a <;> cases b <;> simp_all [embed]
  exact Fin.ext (congrArg (fun j : Fin 6 => j.val) h)

/-- Register index at which the selected input operand is stored. -/
def slot (args : Fin k → InputOperand) (i : Fin k) : Fin (registers args) :=
  ⟨i.val,by dsimp [registers,registerCount,capacity]; omega⟩

private def put (args : Fin k → InputOperand) (i : Fin k) : FiniteRoutine (ISA.Port (registers args) 6) :=
  match args i with
  | .geometry _ => .ret
  | .prefixLength => load (slot args i) 4
  | .prefixWord => load (slot args i) 5

private def patch (args : Fin k → InputOperand) : (n : ℕ) → n ≤ k → FiniteRoutine (ISA.Port (registers args) 6)
  | 0, _ => .ret
  | n+1, h => (patch args n (by omega)).followedBy (put args ⟨n,h⟩)

/-- Evaluate the geometry slots, then copy the parsed prefix length or value to each slot that
requests it. -/
def program (args : Fin k → InputOperand) : FiniteRoutine (ISA.Port (registers args) 6) :=
  ((vector (geometryOnly args)).onPorts embed).followedBy (patch args k le_rfl)

private theorem vector_input {r : ℕ} (g : Geometry) (lit : LiteralPrefix)
    (st : Word g.w) (rs out : Fin r → Word g.w) (log : WriteLog g.w)
    (routine : FiniteRoutine (ISA.Port r 4)) {t : ℕ}
    (h : routine.Runs t (ISA.bank (geometryWords g) st rs log) (ISA.bank (geometryWords g) st out log)) :
    (routine.onPorts embed).Runs t (ISA.bank (input g lit) st rs log) (ISA.bank (input g lit) st out log) := by
  apply FiniteRoutine.runs_onPorts_framed _ embed_inj h
  · intro j; cases j <;> simp [embed, ISA.bank, input]
  · intro j; cases j <;> simp [embed, ISA.bank, input]
  · intro j hj
    cases j with
    | reg i => exact (hj (.reg i) rfl).elim
    | _ => rfl

private def mixed (args : Fin k → InputOperand) (g : Geometry) (lit : LiteralPrefix) (n : ℕ)
    (i : Fin (registers args)) : Word g.w :=
  if hi : i.val < k then
    if i.val < n then Pieces.word g lit (args ⟨i.val,hi⟩) else output g (geometryOnly args) i
  else output g (geometryOnly args) i

private theorem put_run (args : Fin k → InputOperand) (g : Geometry) (lit : LiteralPrefix)
    (st : Word g.w) (log : WriteLog g.w) (i : Fin k) :
    ∃ t ≤ 8*g.w+3, (put args i).Runs t
      (ISA.bank (input g lit) st (mixed args g lit i.val) log)
      (ISA.bank (input g lit) st (mixed args g lit (i.val+1)) log) := by
  have hnew : mixed args g lit (i.val+1) (slot args i) = Pieces.word g lit (args i) := by
    simp [mixed,slot,i.isLt]
  have hsame (j : Fin (registers args)) (hne : j ≠ slot args i) :
      mixed args g lit (i.val+1) j = mixed args g lit i.val j := by
    have hj : j.val ≠ i.val := fun h => hne (Fin.ext h)
    simp only [mixed,show j.val < i.val+1 ↔ j.val < i.val by omega]
  have hbase : mixed args g lit i.val (slot args i) = packed g.w ((geometryOnly args i).eval g) := by
    simp only [mixed,slot,i.isLt,↓reduceDIte,lt_self_iff_false,↓reduceIte]
    exact output_at ..
  have eq (a : Word g.w) (ha : Pieces.word g lit (args i) = a) :
      Function.update (mixed args g lit i.val) (slot args i) a = mixed args g lit (i.val+1) := by
    funext j
    by_cases hj : j = slot args i
    · subst j; rw [Function.update_self,hnew,ha]
    · rw [Function.update_of_ne hj,hsame j hj]
  cases h : args i with
  | geometry e =>
    have he : mixed args g lit i.val = mixed args g lit (i.val+1) := by
      funext j
      by_cases hj : j = slot args i
      · subst j; rw [hnew,hbase]; simp [geometryOnly,h,Pieces.word,InputOperand.eval]
      · exact (hsame j hj).symm
    rw [put,h,he]
    exact ⟨1,by omega,Routine.runs_ret _⟩
  | prefixLength =>
    rw [put,h,← eq ((input g lit) 4) (by rw [h]; rfl)]
    exact ⟨_,le_rfl,load_runs ..⟩
  | prefixWord =>
    rw [put,h,← eq ((input g lit) 5) (by rw [h]; rfl)]
    exact ⟨_,le_rfl,load_runs ..⟩

private theorem patch_run (args : Fin k → InputOperand) (g : Geometry) (lit : LiteralPrefix)
    (st : Word g.w) (log : WriteLog g.w) (n : ℕ) (hn : n ≤ k) :
    ∃ t ≤ n*(8*g.w+3)+1, (patch args n hn).Runs t
      (ISA.bank (input g lit) st (mixed args g lit 0) log)
      (ISA.bank (input g lit) st (mixed args g lit n) log) := by
  induction n with
  | zero => exact ⟨1,by simp,Routine.runs_ret _⟩
  | succ n ih =>
    obtain ⟨t,ht,first⟩ := ih (by omega)
    obtain ⟨u,hu,last⟩ := put_run args g lit st log ⟨n,hn⟩
    exact ⟨_,by rw [Nat.succ_mul]; omega,first.followedBy last⟩

/-- Each component of the flattened table is loaded from its prescribed
operand. The time constant depends only on the fixed operand vector. -/
theorem runs (args : Fin k → InputOperand) (g : Geometry) (lit : LiteralPrefix)
    (hf : ∀ i, (geometryOnly args i).Fits g (2^g.w))
    (st : Word g.w) (rs : Fin (registers args) → Word g.w) (log : WriteLog g.w) :
    ∃ t ≤ coefficient (geometryOnly args)*(g.w+1)^2+k*(8*g.w+3)+2,
      ∃ out : Fin (registers args) → Word g.w, (program args).Runs t
        (ISA.bank (input g lit) st rs log) (ISA.bank (input g lit) st out log) ∧
        ∀ i, out (slot args i) = Pieces.word g lit (args i) := by
  obtain ⟨t,ht,arith⟩ := vector_runs g (geometryOnly args) hf st rs log
  have pre := vector_input g lit st rs _ log _ arith
  have hzero : mixed args g lit 0 = output g (geometryOnly args) := by funext i; simp [mixed]
  obtain ⟨u,hu,fix⟩ := patch_run args g lit st log k le_rfl
  rw [hzero] at fix
  exact ⟨_,by omega,_,pre.followedBy fix,fun i => by simp [mixed,slot,i.isLt]⟩

end RAMTape.InputOperandMachine

end VPVNP
end Computability
end OAI

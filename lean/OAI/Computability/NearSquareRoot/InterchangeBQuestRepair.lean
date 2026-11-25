import OAI.Computability.NearSquareRoot.InterchangeRepairProgram
import OAI.Computability.NearSquareRoot.InterchangeBQuestRepairBank

/-!
# Bounded execution of the four predictors and spectral corrections

The finite-bank repair schedule is interpreted using bounded oracle calls
and linear local tables. The local stack certificate charges the registers
retained during each branch and passes the child peak through additively.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.BRepairRun

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  NearSquareRoot.InterchangeSpace RepairRun RepairSchedule SwapRepair
variable {I Y : Type} {X : I → Type} {r : Regime I} {N l : I → ℕ}
    {job : Job Y} {zone : I → Y → Prop}

private theorem bank_rules {E : Type} {cell : RepairRun.Cell X E} (s : RepairRun.Store r N l cell) :
    RepairProgram.Rules (X:=X) (E:=E) (fun {_A _B} price x y => Runs job r N l zone cell price x y) where
  table x f := runs_table s x f
  seq h g := Runs.seq s h g
  fork h g := Runs.fork s h g
  keep h := Runs.keep s h
  empty x y := empty_target s x y


variable {K L : Type} [Field K] [Fintype L] {m : ℕ}
variable {enc : Cell X (Coeff K m)} (machine : Store r N l enc)
include machine
/-- Execute the four predictors and the four check-row sweeps, retaining each
intermediate exactly where its later use requires it. `paid` is the cost of
one complete conversion of one extension row, including its basis components. -/
theorem execute [Nonempty L] (e : Environment K m) (T : Table K m)
    (tag : (i : I) → X i → Pattern m) (mask : Tagged job r N l zone enc tag)
    (F G : (i : I) → (X i → Coeff K m) → X i → Coeff K m)
    (P : (i : I) → Data K L (X i) (width m) m → Data K L (X i) (width m) m)
    (pred paid : ℕ)
    (hp : ∀ x, Runs job r N l zone enc pred (flatten x) (flatten fun i => P i (x i)))
    (hf : ∀ v : (i : I) → X i → Coeff K m, BHop job r N l zone paid
      (together r.header (fun i => enc i (v i))) (fun i => enc i (F i (v i))))
    (hg : ∀ v : (i : I) → X i → Coeff K m, BHop job r N l zone paid
      (together r.header (fun i => enc i (v i))) (fun i => enc i (G i (v i))))
    (x : (i : I) → Data K L (X i) (width m) m) :
    Runs job r N l zone enc (4 * pred + 4 * Fintype.card L * checks m * paid)
      (flatten x) (flatten (fun i => schedule e T (tag i) (F i) (G i) (P i) (x i))) := by
  exact RepairProgram.execute (bank_rules machine) e T tag mask F G P pred paid hp
    (fun x => runs_rows machine F x hf) (fun x => runs_rows machine G x hg) x

end Interchange.BRepairRun

end NearSquareRoot
end Computability
end OAI

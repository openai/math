import OAI.Optimization.LinearProgramming.Lattice.BitProbeCodes
import OAI.Optimization.LinearProgramming.Lattice.BitProbe

/-! Finite stack operations for tagged requests, completed probes, and zero rows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

variable {A B C : Type} {ea : A → List Bool} {eb : B → List Bool} {ec : C → List Bool}

noncomputable def leftP (ec : C → List Bool) {f : A → B} (p : Procedure ea eb f) :
    Procedure ea (sumCode eb ec) (fun x => Sum.inl (f x)) :=
  ((prepend eb [false]).comp p).result (fun _ => rfl)

noncomputable def rightP (eb : B → List Bool) {f : A → C} (p : Procedure ea ec f) :
    Procedure ea (sumCode eb ec) (fun x => Sum.inr (f x)) :=
  ((prepend ec [true]).comp p).result (fun _ => rfl)

noncomputable def askP {a : A → Row} {c : A → Carry} (x : Procedure ea intRowCode a)
    (k : Procedure ea carryCode c) : Procedure ea actionCode (fun s => ask (a s) (c s)) :=
  rightP resultCode (x.pair k)

noncomputable def doneP (b : Bool) {a : A → List ℚ} (p : Procedure ea ratListCode a) :
    Procedure ea actionCode (fun s => done b (a s)) :=
  leftP (prodCode intRowCode carryCode) ((constant ea boolCode b).pair p)

noncomputable def emptyListP (ea : A → List Bool) :
    Procedure (listCode ea) boolCode List.isEmpty :=
  listEmpty (ea:=ea)

noncomputable def zeroUnaryP : Procedure unaryCode boolCode (fun n => decide (n = 0)) :=
  unaryZero

noncomputable def replicateP (ea : A → List Bool) (d : A) :
    Procedure unaryCode (listCode ea) (fun n => List.replicate n d) := by
  let cell := constant (prodCode unaryCode unaryCode) ea d
  let all := (tabulate (f:=fun (_ : ℕ) (_ : ℕ) => d) d cell).comp
    ((identity unaryCode).pair (identity unaryCode))
  exact all.congrFun (by intro n; change (List.range n).map (fun _ => d) = _; simp)

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

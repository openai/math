import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic

/-! A polynomial-time bit-stack map with a serialized read-only context. The context is
retained by the loop while each computed output is consed onto its accumulator. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace GridMachine
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

private def contextStep {C A B : Type} (f : C × A → B) (p : A × (C × List B)) : C × List B :=
  (p.2.1, f (p.2.1,p.1) :: p.2.2)

private theorem fold_contextStep {C A B : Type} (f : C×A → B) (c : C)
    (xs : List A) (ys : List B) :
    xs.foldl (fun st x => contextStep f (x,st)) (c,ys) =
      (c, (xs.map fun x => f (c,x)).reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    change xs.foldl (fun st x => contextStep f (x,st)) (c,f (c,a)::ys) = _
    rw [ih]
    simp [List.append_assoc]

private noncomputable def contextStepP {C A B : Type} {ec : C → List Bool} {ea : A → List Bool}
    {eb : B → List Bool} {f : C×A → B} (p : Procedure (prodCode ec ea) eb f) :
    Procedure (prodCode ea (prodCode ec (listCode eb))) (prodCode ec (listCode eb)) (contextStep f) := by
  let state := prodCode ec (listCode eb)
  let input := first ea state
  let old := second ea state
  let ctx := (first ec (listCode eb)).comp old
  let output := (second ec (listCode eb)).comp old
  let newValue := p.comp (ctx.pair input)
  exact (ctx.pair ((listCons eb).comp (newValue.pair output))).congrFun (fun _ => rfl)

/-- The input carries the list followed by one copy of the shared context. Parameter, list
positions and intermediate outputs are always read, copied and written by the bit machine. -/
noncomputable def mapWithContext {C A B : Type} {ec : C → List Bool} {ea : A → List Bool}
    {eb : B → List Bool} {f : C×A → B} (da : A) (db : B) (p : Procedure (prodCode ec ea) eb f) :
    Procedure (prodCode (listCode ea) ec) (listCode eb)
      (fun x : List A × C => x.1.map (fun a => f (x.2,a))) := by
  let state := prodCode ec (listCode eb)
  let argSize : Polynomial ℕ := Polynomial.C 3*Polynomial.X+1
  let itemSize := argSize + p.bound.comp argSize
  let bound : Polynomial ℕ := Polynomial.X*(Polynomial.C 2*itemSize+Polynomial.C 2)+
    Polynomial.X+1
  let fold := foldList da (contextStepP p) bound (by
    rintro xs ⟨c,ys⟩ i
    change (state ((xs.take i).foldl (fun st x => contextStep f (x,st)) (c,ys))).length ≤ _
    rw [fold_contextStep]
    let L := (listCode ea xs).length+(state (c,ys)).length
    have hctx : (ec c).length ≤ L := by
      simp only [L, state, prodCode, pairBits_length]
      omega
    have hx : (listCode ea xs).length ≤ L := Nat.le_add_right _ _
    have hcount : (xs.take i).length ≤ L :=
      (by simp only [List.length_take]; exact (Nat.min_le_right _ _).trans ((list_length_le_code ea xs).trans hx))
    have mapped := listCode_length_map_bound eb (fun x => f (c,x)) (xs.take i) (itemSize.eval L) (by
      intro a ha
      have hA := (code_le_of_mem ea (List.mem_of_mem_take ha)).trans hx
      have hArg : (prodCode ec ea (c,a)).length ≤ argSize.eval L := by
        simp only [prodCode, pairBits_length, argSize, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
        omega
      have hg := p.output_length_le (c,a)
      have hpoly := eval_nat_mono p.bound hArg
      change (eb (f (c,a))).length ≤ (argSize + p.bound.comp argSize).eval L
      rw [Polynomial.eval_add, Polynomial.eval_comp]
      exact hg.trans (Nat.add_le_add hArg hpoly))
    have hrev := listCode_length_append eb (((xs.take i).map fun a => f (c,a)).reverse) ys
    rw [listCode_length_rev] at hrev
    have hroom := Nat.mul_le_mul_right (2*itemSize.eval L+2) hcount
    change (state (c, (((xs.take i).map fun a => f (c,a)).reverse ++ ys))).length ≤ bound.eval L
    have hold : (state (c,ys)).length ≤ L := Nat.le_add_left _ _
    simp only [state, prodCode, pairBits_length] at hold ⊢
    simp only [bound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
    omega)
  let list := first (listCode ea) ec
  let context := second (listCode ea) ec
  let empty := constant (prodCode (listCode ea) ec) (listCode eb) []
  let run := fold.comp (list.pair (context.pair empty))
  let result := (listReverse eb db).comp ((second ec (listCode eb)).comp run)
  exact result.congrFun (by
    intro x
    change (((x.1.foldl (fun st a => contextStep f (a,st)) (x.2,[])).2).reverse) = _
    simp [fold_contextStep])

end GridMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # A charged physical fold over a list of binary records -/

namespace OAI.Computability.MultitapeWeakETH

open IntegerMultiplication.Code

abbrev SweepRow {I A : Type} (records : I → List A) :=
  {q : A × List A × I // q.1 :: q.2.1 <:+ records q.2.2}

/-- Consume the records on the input tape in their supplied order. The
encoded accumulator may depend on the original input and the unread suffix. -/
theorem bounded_sweep {I A : Type} [Codec A] (budget : I → ℕ) (records : I → List A)
    (acc : List A → I → Tree) (hr : Dom budget (fun i => size (records i)))
    (step : Task.BT (fun q : SweepRow records => budget q.val.2.2)
      (fun q => .fork (send q.val.1) (acc (q.val.1 :: q.val.2.1) q.val.2.2))
      (fun q => acc q.val.2.1 q.val.2.2)) :
    Task.BT budget (fun i => .fork (send (records i)) (acc (records i) i)) (acc []) := by
  obtain ⟨a,⟨k,C,ha⟩,body⟩ := step
  let time (i : I) := C*(budget i+1)^k
  let D (l : List A) (i : I) := l <:+ records i
  have run := Task.sweep (p:=fun (_ : I) => send (X:=A)) (w:=acc) (a:=fun _ _ i => time i) (D:=D)
    (fun b l i ⟨pre,eq⟩ => ⟨pre++[b],by simpa using eq⟩) (body.mono ha)
  have price (i : I) (l : List A) :
      Task.foldCost (fun v _ => time i+(send v).count) l = time i*l.length + size l := by
    induction l with
    | nil => simp [Task.foldCost]
    | cons x l ih =>
      change time i+size x+1+Task.foldCost _ l = _
      rw [ih,List.length_cons,Nat.mul_add,Nat.mul_one,size_cons]
      omega
  have cost := ((Dom.const budget C).mul (((Dom.base budget).add (Dom.const budget 1)).pow k)).mul
    (hr.mono fun i => (duration (records i)).le)
  refine ⟨fun i => time i*(records i).length+size (records i),cost.add hr,?_⟩
  have exec := run.on (fun i => (⟨(records i,i),List.suffix_rfl⟩ : {p : List A × I // D p.1 p.2}))
  exact exec.conform (fun i => price i _) (fun i => by simp [Task.forest_send]) (fun _ => rfl)

end OAI.Computability.MultitapeWeakETH

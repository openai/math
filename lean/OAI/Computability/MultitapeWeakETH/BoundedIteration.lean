import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Iterating a physical step on a bounded family of reachable states -/

namespace OAI.Computability.MultitapeWeakETH

open IntegerMultiplication.Code

/-- A single tape program iterates the supplied step. The polynomial size
estimate need only hold on prefixes from each actual seed, and the ghost
index is never supplied to the program. -/
theorem bounded_iteration {I X : Type} [Codec X] (scale fuel : I → ℕ) (seed : I → X)
    (step : X → X) (program : Poly step) (hf : Dom scale fuel)
    (C d : ℕ) (bounded : ∀ i j, j ≤ fuel i → size (step^[j] (seed i)) ≤ C*(scale i+1)^d) :
    Task.BT scale (fun i => send (tally (fuel i),seed i)) (fun i => send (step^[fuel i] (seed i))) := by
  let D (l : Tally) (i : I) := l.length ≤ fuel i
  let acc (l : Tally) (i : I) := step^[fuel i-l.length] (seed i)
  let Q := {q : Unit × Tally × I // D (q.1 :: q.2.1) q.2.2}
  let L (q : Q) := scale q.val.2.2
  let input (q : Q) := (q.val.1,acc (q.val.1::q.val.2.1) q.val.2.2)
  have size_input : Dom L (fun q => size (input q)) := by
    apply (((Dom.const L C).mul (((Dom.base L).add (Dom.const L 1)).pow d)).add (Dom.const L 2)).mono
    intro q
    have b := bounded q.val.2.2 (fuel q.val.2.2 - (q.val.1::q.val.2.1).length) (Nat.sub_le ..)
    change 1 + size (acc (q.val.1::q.val.2.1) q.val.2.2) + 1 ≤ _
    dsimp only [acc,L]
    omega
  have machine := ((Easy.snd (X:=Unit)).poly.compose program).on size_input
  obtain ⟨a,⟨e,A,ha⟩,task⟩ := machine
  let time (i : I) := A*(scale i+1)^e
  have sweep := Task.sweep (p:=fun (_ : I) => send (X:=Unit)) (w:=fun l i => send (acc l i))
    (a:=fun _ _ i => time i) (D:=D)
    (fun x l i h => Nat.le_trans (Nat.le_succ _) h)
    (show Task _ _ _ from (task.mono ha).conform (by intro; rfl) (fun _ => rfl) (fun q => ?_))
  · have charge (i : I) (l : Tally) : Task.foldCost (fun x _ => time i+(send x).count) l =
        (time i+2)*l.length + 1 := by
      induction l with
      | nil => rfl
      | cons u l ih =>
        change time i + 1 + 1 + Task.foldCost _ l = _
        rw [ih,List.length_cons,Nat.mul_add,Nat.mul_one]; omega
    have run := sweep.on (fun i : I => (⟨(tally (fuel i),i),by simp [D]⟩ : {q : Tally × I // D q.1 q.2}))
    refine ⟨fun i => (time i+2)*fuel i+1,
      ((((Dom.const scale A).mul (((Dom.base scale).add (Dom.const scale 1)).pow e)).add (Dom.const scale 2)).mul hf
        |>.add (Dom.const scale 1)),run.conform ?_ ?_ ?_⟩
    · intro i; simp only [charge,tally_length]
    · intro i; simp [acc,Task.forest_send]
    · intro i; simp [acc]
  · rcases q with ⟨⟨u,l,i⟩,h⟩
    change send (step (step^[fuel i-(u::l).length] (seed i))) = send (step^[fuel i-l.length] (seed i))
    change l.length+1 ≤ fuel i at h
    rw [List.length_cons,show fuel i-l.length = (fuel i-(l.length+1))+1 by omega,Function.iterate_succ_apply']

end OAI.Computability.MultitapeWeakETH

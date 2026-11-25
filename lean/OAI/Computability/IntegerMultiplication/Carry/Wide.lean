import OAI.Computability.IntegerMultiplication.Carry.Shrink

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- convert arbitrary binary to unary in polynomial length+numeric value. -/
namespace Carry
open Code Bits

def swell (i : Bool × Tally) :=
  let s := i.2++i.2
  bif i.1 then ()::s else s
@[fun_prop] theorem easy_swell : Easy swell := by
  unfold swell
  dsimp only
  apply condition <;> fun_prop

private theorem swell_v (b:Bool) (n:ℕ):swell (b,tally n)=tally (digit b + 2*n) := by
  have e : tally n++tally n=tally (2*n) := by simp only [IntegerMultiplication.Strip.Dims.mergeTally, two_mul]
  unfold swell
  cases b <;> simp only [Bool.cond_true,Bool.cond_false,d1,d0,e,Nat.zero_add]
  rw [show 1+2*n=(2*n)+1 by omega]; rfl

/-- canonical Unary extraction. Any amount paid (also true linear in needed
number of nodes). -/
theorem rice : Computes (fun t=> size t + value t) (fun t=>tally (value t)) := by
  let f (t:Word):Unit→Tree := fun _=>send (tally (value t))
  let I := {s:Bool × Word × Unit // True}
  have h := Task.foldRight (p:=fun (_:Unit) (b:Bool)=> send b) (f:=f)
    (seed:=fun _=>send ([]:Tally))
    (b:=fun _=>0)
    (a:=fun (i:Bool) (s:Word) (_:Unit)=>2*value s+3) (D:=fun _ _=>True)
    (fun _ _ _ _=>trivial)
    (show Task _ _ _ from Task.self)
    (show Task _ _ _ from ?_)
  swap
  · let X (i:I) := (i.val.1,tally (value i.val.2.1))
    refine (easy_swell.on X).conform (fun i=>?_) (fun i=>send_prod ..) (fun i=> ?_)
    · unfold X; rw [size_prod,size_tally,tally_length,show size (i.val.1:Bool)=1 from rfl]
      omega
    rw [show swell (X i)= _ from swell_v ..]; rfl
  let g (b : Bool) (s:Word):=2*value s+3+(send b).count
  let z (b:Bool) (s:Word) := g b s +1
  -- sum over suffix values telescopes
  have b (s:Word) :
      Task.foldCost g s ≤ 10*s.length+2*value s+1 := by
    induction s with
    | nil=>simp [Task.foldCost]
    | cons x s ih =>
      rw [value_cons,List.length_cons,Task.foldCost, show g x s=2*value s+4 from rfl]
      omega
  have hp := h.on (fun t:Word=>⟨(t,()),trivial⟩)
  let nil:=send ([]:Tally)
  have u := (Task.supply nil (send (X:=Word))).compose (Task.exchange (fun _=>nil) send)
  have p : Task (fun s:Word=>Task.foldCost g s) (fun t=>Tree.fork (send t) nil)
      (fun s=>send (tally (value s))) := by
    simpa only [Task.forest_send,zero_add] using hp
  refine (u.compose p).bound 12 (fun x=> ?_)
  change 0+(nil.count+size x)+Task.foldCost g x+1≤_
  have e := b x; simp only [size_word,show nil.count=1 from rfl]; omega
end Carry

end IntegerMultiplication
end Computability
end OAI

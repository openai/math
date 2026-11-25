import OAI.Computability.IntegerMultiplication.Code.Chunk

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open _root_.OAI.Computability.IntegerMultiplication.Code.Task
variable {X Y : Type*} [Codec X]

/-- replicate actual arbitrary encoded input (time proportional to output). -/
theorem generate :
    Computes (fun i : Tally × X => (i.1.length+1)*size i.2)
      (fun i => List.replicate i.1.length i.2) := by
  -- fold with carried pair x × result list
  let ans (l : Tally) (x : X) := Tree.fork (send x) (send (List.replicate l.length x))
  let side (x : X) := Tree.fork (send x) (send ([] : List X))
  let D (_ : Tally) (_ : X) := True
  have step : Task (fun i : {s : Unit × Tally × X // D (s.1::s.2.1) s.2.2} => size i.val.2.2)
      (fun i => .fork (send i.val.1) (ans i.val.2.1 i.val.2.2))
      (fun i => ans (i.val.1::i.val.2.1) i.val.2.2) := by
    obtain ⟨c,C,h⟩ := Task.copy (fun x : X => send x)
    refine ⟨splitRoot 0 (fun _ => .pass)
      (splitRoot 0 (fun _ => splitRoot 0 (fun _ => .pass)
        (.join c (splitRoot 0 (fun _ => .pass)
          -- two copies one stack: x,x,l. Need reconstruct x,(x,l); can move x off and back.
          (.join (move 0 1 2) (.join (pack 0) (.join (move 1 0 2) (pack 0))))))) .pass),
      C+115,?_⟩
    intro ⟨⟨_,l,x⟩,_⟩ G r
    let p := send (List.replicate l.length x)
    have h₁ := fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide) (send x) G
      (pile 0 (send x) (pile 0 p r))
    rw [pile_comm 1 _ _ 0 _ (by decide),pile_comm 1 _ _ 0 _ (by decide)] at h₁
    have h₂ := fits_pack (send x) p (pile 1 (send x) r) 0 G
    have h₃ := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) (send x) G
      (pile 0 (.fork (send x) p) r)
    rw [pile_comm 1 _ r 0 _ (by decide)] at h₃
    have d := fits_pair (c:=fun _ => .pass) (h₁.join (h₂.join (h₃.join (fits_pack ..))))
    have g := fits_pair (c:=fun _ => .pass) ((h x G (pile 0 p r)).join d)
    simp only [ans, List.length_cons, List.replicate_succ, send_cons]
    apply (fits_pair (fits_bit (b:=false) (c:= fun _ => _) g)).mono
    beta_reduce
    rw [show (send x).count=size x from rfl] -- rewrites all? rw all exact occurrences first? rw uses all matching
    rw [Nat.add_mul]
    omega
  have f (l : Tally) : ∀ x : X, (foldCost (fun _ _ => size x+(send ()).count) l) =
      l.length*(size x+2)+1 := by
    intro x; induction l with
    | nil => simp [foldCost]
    | cons t l ih => simp only [foldCost,List.length_cons,Nat.add_mul,ih]; change _+1+1+_ = _; omega
  have hs := Task.foldRight (p:=fun _ => send) (f:=ans) (seed:=side)
    (b:=fun _ => 0) (a := fun _ _ x => size x) (D:=D)
    (fun _ _ _ _ => trivial) (Task.self) step
  have as : Easy (fun i : Tally × X => (i.1,i.2,([] : List X))) := by fun_prop
  have hd := Task.dropLeft (fun x : Tally × X => send x.2)
    (fun x => send (List.replicate x.1.length x.2))
  have ht := hs.on (fun i : Tally × X => ⟨(i.1,i.2),trivial⟩)
  simp only [zero_add, Task.forest_send] at ht
  -- defeq
  refine ((Task.compose as ht).compose hd).bound 10 ?_
  intro i
  -- f rewrite foldCost
  have one (x : Unit) : (send x).count = 1 := rfl
  simp_rw [one]
  change _ + foldCost (fun _ _ => size i.2+(send ()).count) i.1+_ +1 ≤ _
  rw [f,size_prod,size_tally]
  have p := size_pos i.2
  have : i.1.length ≤ i.1.length*size i.2 := Nat.le_mul_of_pos_right _ p
  rw [Nat.add_mul, Nat.one_mul,Nat.mul_add i.1.length]
  change _+_+_+(_ + _ + _)+size i.2+1 ≤ _
  omega

end Code

end IntegerMultiplication
end Computability
end OAI

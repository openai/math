import OAI.Computability.IntegerMultiplication.Loom.Final
import OAI.Computability.IntegerMultiplication.Code.Padding

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Spindle
open Code Strip
variable (b : ℕ)

/-- manufacture tally(b^length) and beacon. To fit into polynomial time on
 scale, use only where b^length bounded below a polynomial. -/
def assembly (l : Tally) : Tally × Tree :=
  (tally (b^l.length),Loom.beacon b l.length)
def times (x : Tally) := ((x.map fun _ => tally b).flatten)
private theorem easyTimes : Easy (times b) := by unfold times; fun_prop
private theorem times_length (x : Tally) : times b x=tally (x.length*b) := by
  unfold times
  rw [List.map_const']; simp [Dims.tallies]

private theorem pair_easy : Easy (fun x : Tally × Tree => let y := times b x.1; (y,Tree.fork (.atom true) (Tree.fork (send y) x.2))) := by
  let Y := (fun x : Tally × Tree => times b x.1)
  have g : Easy Y := Easy.fst.compose (easyTimes b)
  -- send/Tree.fork operations
  have j {X} [Codec X] : Easy (send (X:=X)) := Code.Task.self
  have e : Easy (fun k : Tree × Tree => Tree.fork k.1 k.2) := Code.Task.self
  exact g.pair (((Easy.const _).pair (((g.compose j).pair Easy.snd).compose e)).compose e)

private theorem ay (d : 2≤b) :
    Computes (fun x : Tally => b^x.length) (assembly b) := by
  have he := Task.foldRight (p:=fun (_:Unit) => send (X:=Unit)) (f:=fun l _ => send (assembly b l))
    (seed:=fun _ => send (assembly b [])) (b:=fun _ => 0)
    (a:=fun u l _ => size (assembly b l)) (D:=fun (_:Tally) (_:Unit)=>True)
    (fun _ _ _ _ => trivial) Code.Task.self (by
      have h := Task.on (Easy.snd (X:=Unit) (Y:=Tally×Tree) |>.compose (pair_easy b))
        (fun i : {s:Unit × Tally × Unit // True} => (i.val.1, assembly b i.val.2.1))
      simp_rw [assembly] at *
      apply (h.bound 3 (fun i => ?_)).conform (by intro; rfl) (by intro; rfl) (fun i => ?_)
      · -- h bound infers wrap b'?
        rw [Code.size_prod,show size i.val.1=1 from rfl]
        change 1+size (tally (b^i.val.2.1.length),Loom.beacon b i.val.2.1.length)+1+1 ≤ 3*(size (tally (b^i.val.2.1.length),Loom.beacon b i.val.2.1.length)+1)
        omega
      ·
        rw [times_length,tally_length,List.length_cons,pow_succ,Loom.beacon]
        rw [pow_succ])
  have u := (Task.supply (send (assembly b [])) send).compose
    (Task.exchange (fun _ => send (assembly b [])) (send (X:=Tally)))
  simp_rw [Task.forest_send] at he
  apply (u.compose (he.on fun (i:Tally) => ⟨(i,()),trivial⟩)).bound
    (80+size (assembly b []))
  have hh (l : Tally) : Task.foldCost (fun (x:Unit) s => size (assembly b s)+(send x).count) l ≤
      48*b^l.length := by
    induction l with
    | nil => change 1≤48*b^0; simp
    | cons x l ih =>
      rw [Task.foldCost,List.length_cons,pow_succ]
      have hs := IntegerMultiplication.Loom.Stair.beacon_size b l.length d
      have e := Nat.one_le_pow l.length b (by omega)
      rw [assembly,size_prod,size_tally,tally_length]
      change 2*b^l.length+1+_+1+1+1+_ ≤ _
      have ht (l) : size (Loom.beacon b l)=(Loom.beacon b l).count := rfl
      rw [ht]
      have : (b^l.length)*2 ≤ (b^l.length)*b := Nat.mul_le_mul_left _ d
      omega
  intro i
  have g : i.length+1 ≤ b^i.length := by
    suffices h : ∀ k, k+1≤b^k from h _
    intro k; induction k with
    | zero => simp
    | succ k h => rw [pow_succ]; have := Nat.mul_le_mul h d; omega
  change 0+((size (assembly b []))+(size i))+(0+Task.foldCost _ i)+1≤ _
  rw [Nat.mul_add,Nat.mul_one,Nat.add_mul,size_tally] -- one_mul maybe no
  specialize hh i
  omega

theorem drawn (d : 2 ≤ b) : Computes (fun x : Tally => b^x.length) (assembly b) := ay b d
theorem juge {I} (r : Regime I) (k : I→ℕ) (h : 2≤b)
    (f : r.Has (tally ∘ k)) (t : Dom r.scale (fun i => b^k i)) :
    r.Has (fun i => tally (b^k i)) ∧ r.Small (Loom.beacon b ∘ k) := by
  have u := Task.on (ay b h) (fun i:I => tally (k i))
  simp only [assembly,tally_length] at u
  have y : r.Has (fun (i:I) => (tally (b^k i),Loom.beacon b (k i))) :=
    Regime.Small.chain f (⟨_,t,u⟩ : Task.BT r.scale _ _)
  exact ⟨y.ez Easy.fst,y.ez Easy.snd⟩

theorem growth {I} (s : I→ℕ) (k : I→ℕ) (D : ℕ)
    (h : Dom s (fun i => D^k i)) (e : 2≤D) :
    Dom s (fun i => b^k i) := by
  -- b ≤ D^b
  have hi : ∀ i : ℕ, i ≤ D^i := by
    intro i; induction i with
    | zero => simp
    | succ i hi =>
      have t := Nat.one_le_pow i D (by omega)
      rw [pow_succ]
      have c := Nat.mul_le_mul_left (D^i) e
      omega
  apply (h.pow b).mono
  intro i
  rw [← pow_mul, Nat.mul_comm (k i), pow_mul]
  exact Nat.pow_le_pow_left (hi b) _
end Spindle

end IntegerMultiplication
end Computability
end OAI

import OAI.Computability.IntegerMultiplication.Strip.Dims
import OAI.Computability.IntegerMultiplication.Strip.Cars

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip.Dims
open Code Code.Task

def shape (l : Tape) : List Tally := l.map tally
@[simp] theorem shape_cons (n) (l : Tape) : shape (n::l)=tally n::shape l := rfl
@[simp] theorem shape_nil : shape []=[] := rfl

theorem mergeTally (x y) : tally x ++ tally y = tally (x+y) := by
  induction x with
  | zero => simp [tally]
  | succ x ih =>
    rw [tally_succ,List.cons_append,ih,Nat.add_right_comm,tally_succ]
theorem tallies (n m) : (List.replicate n (tally m)).flatten=tally (n*m) := by
  induction n with
  | zero => simp [tally]
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons,ih, mergeTally,Nat.add_mul,Nat.one_mul,Nat.add_comm]

private theorem size_rep (n m) :
    size (List.replicate n (tally m))=n*(2*m+2)+1 := by
  induction n with
  | zero => simp [tally]
  | succ n ih =>
    rw [List.replicate_succ,size_cons,size_tally,tally_length,ih,Nat.add_mul,Nat.one_mul]
    omega

-- accumulator cost: every multiply covered by O(product+ descriptor); all radices ≥2
theorem unary : Code.Task (fun l : {l : Tape // solid l} => room l.val)
    (fun l => Code.send (shape l.val))
    (fun l => Code.send (tally (room l.val))) := by
  let D := fun (l:Tape) (_:Unit) => solid l
  let seed (_:Unit) := send (tally 1)
  let f := fun (l:Tape) (_:Unit) => send (tally (room l))
  let ext := fun (n:ℕ) (l:Tape) (_:Unit) => n*room l
  let I := {s : ℕ × Tape × Unit // D (s.1::s.2.1) s.2.2}
  let p (i : I) := (tally i.val.1,tally (room i.val.2.1))
  have h := Code.generate (X:=Tally)
  have u := Computes.comp (g:=List.flatten) Easy.flatten h
  have q := u.on p
  have g := foldRight (b:=fun _ => 0) (D:=D) (a:=ext) (p:= fun _ n => send (tally n)) (f:=f) (seed:=seed)
    (fun _ _ _ e => (solid_cons ..).mp e |>.2)
    Code.Task.self
    (show Code.Task (X:=I) _ _ _ from (q.bound (b':= fun i : I => i.val.1*room i.val.2.1) 20 (by
      rintro ⟨⟨n,l,_⟩,h⟩
      dsimp only [p,tally_length]
      rw [tally_length,size_tally,tally_length,size_rep]
      have e := (solid_cons ..).mp h
      have hn : 0<n := by omega
      have hl := wide l e.2
      have : n≤n*room l := Nat.le_mul_of_pos_right _ hl
      have : room l ≤ n*room l := Nat.le_mul_of_pos_left _ hn
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_add n, Nat.mul_add n]
      -- normalize n*(2*room l)
      rw [Nat.mul_left_comm n 2]
      omega)).conform (by intro; rfl)
        (by simp [p,f]) (by simp [p,f,tallies]))
  let A := {l : Tape // solid l}
  have e : Code.Task (X:=A) (fun i => size (shape i.val))
      (fun i => send (shape i.val)) (fun i => Tree.fork (send (shape i.val)) (seed ())) :=
    -- supply seed prep block cost placement? pack with new seed needs scan payload
    ((Code.Task.supply (seed ()) (fun i => send (shape i.val))).compose
      (Code.Task.exchange (fun (_:A) => seed ()) _)).bound 15 (by intro x; change 0+(3+size _)+_ ≤ _; omega)
  have gg := g.on (fun i : A => (⟨(i.val,()),i.property⟩))
  simp_rw [← forest_map send tally,forest_send] at gg
  refine (e.compose gg).bound 25 ?_
  rintro ⟨l,j⟩
  dsimp only [ext]
  simp only [Nat.zero_add]
  suffices hi : ∀ (l : Tape), solid l →
      size (shape l)+foldCost (fun n s => n*room s+(send (tally n)).count) l + 1 ≤ 25*room l by
    specialize hi l j
    omega
  intro l i
  induction l with
  | nil => simp [foldCost]
  | cons a l ih =>
    obtain ⟨c,d⟩ := solid_cons _ _ |>.mp i
    specialize ih d
    have hs := wide _ d
    have h₁ : 2*room l≤a*room l := Nat.mul_le_mul_right _ c
    have h₂ : a≤a*room l := Nat.le_mul_of_pos_right _ hs
    rw [shape_cons,size_cons, room_cons,foldCost, show (send (tally a)).count = size (tally a) from rfl,
      size_tally,tally_length]
    omega
end Strip.Dims

end IntegerMultiplication
end Computability
end OAI

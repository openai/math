import OAI.Computability.IntegerMultiplication.Wave.Liner

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Param Scale Halo Strip Code Dims Cap Loom Staff Brief Carry Echo Well Moira Bureau
open Atoll
variable {X:Type}[Codec X]
variable {n m:ℕ}(e:n ≤ m)
-- cut & rotate in list
abbrev Valley:=Ticket ×List X
def wcut (t:Tally)(x:List X):List X:=
  (cutLists (t,x)).2 ++ (cutLists (t,x)).1
def spin (q:Valley (X:=X)):List X :=
  let p:=cutLists (q.1.1,q.2)
  wcut q.1.2 p.1 ++ p.2
private theorem easyW : Easy (fun q:Tally×List X=>wcut q.1 q.2):=
  ((easy_cut Easy.identity).compose Easy.exchange).compose Easy.append
@[fun_prop] theorem spinE : Easy (spin (X:=X)) := by
  let H:Valley (X:=X)→List X×List X:=fun i=>cutLists (i.1.1,i.2)
  have P:Easy H:=by unfold H; fun_prop
  exact (((Easy.fst.sndCompose.pair P.fstCompose).compose easyW).pair P.sndCompose).compose Easy.append
-- wrap proof get by actual cut
variable (a:ℕ)(x:Fin m→X)
include e
omit e in
private theorem roundW {Y:Type}(x:Fin n→Y)(p:0<n):
    wcut (Code.tally (a%n)) (List.ofFn x)=List.ofFn (fun i:Fin n=> x (⟨(i.val+a)%n, Nat.mod_lt _ p⟩)) := by
  have h : a % n <(List.ofFn x).length := by simp [Nat.mod_lt _ p]
  rw [wcut,cutLists]
  dsimp only
  rw [tally_length]
  suffices H:(List.ofFn x).rotate (a%n)=List.ofFn (fun i:Fin n=> x (⟨(i.val+a)%n,Nat.mod_lt _ p⟩)) by
    rwa [List.rotate_eq_drop_append_take_mod,Nat.mod_eq_of_lt h] at H
  refine List.ext_getElem (by simp) ?_
  intro i hh hv
  rw [List.getElem_rotate,List.getElem_ofFn,List.getElem_ofFn]
  congr 2
  simp

omit [Codec X] in
theorem spin_l(p:0<n):
    spin ((Code.tally n,Code.tally (a%n)),List.ofFn x)=List.ofFn (x ∘ Atoll.slide e a):= by
  unfold spin cutLists; dsimp
  rw [tally_length]
  let t:=x ∘ glue e
  have g:(List.ofFn x).take n=List.ofFn t:=by
    apply List.ext_getElem (by simp [e])
    intro i h v; simp [t,glue]
  rw [g,roundW a _ p]
  refine List.ext_getElem (by simp; omega) ?_
  intro i h v
  by_cases P:i<n
  · simp (disch := simp [P]) only [List.getElem_append_left,List.getElem_ofFn]
    change _=x (Atoll.slide e a _)
    unfold Atoll.slide; rw [dite_eq_left P];rfl
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.getElem_drop,List.length_ofFn,List.getElem_ofFn,Function.comp_apply]
  unfold Atoll.slide; rw [dite_eq_right P]
  congr 2; omega

end Wave

end IntegerMultiplication
end Computability
end OAI

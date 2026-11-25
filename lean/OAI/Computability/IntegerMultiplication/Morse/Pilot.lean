import OAI.Computability.IntegerMultiplication.Morse.Canon
import OAI.Computability.IntegerMultiplication.Halo.Diagram

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Morse
open Net Net.Walsh Strip Loom Adic Dusk Grid Axon Finset Code Earth
variable {X:Type} {k w:ℕ}
abbrev PhaseL (k:ℕ):Series (Face k):= Earth.canon k
theorem phase_size (k:ℕ): (PhaseL k).count=2^k:=by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (Track (Series.natural 2) (k+1)).count = _
    rw [Loom.Track, Series.count_via, Series.count_cart, Series.count_natural]
    change 2 * (PhaseL k).count = 2^(k+1)
    rw [ih, pow_succ]
    ring
theorem follow_pre (f:Face (k+1)→X):
    (PhaseL (k+1)).tab f =
      (PhaseL k).tab (fun v=>f (pre 0 v)) ++ (PhaseL k).tab (fun v=> f (pre 1 v)) := by
  change (Fin (k+1) → Fin 2) → X at f
  change (Track (Series.natural 2) _).tab (f: (Fin (_+1)→Fin 2)→X) = _
  rw [(Loom.step (Series.natural 2) k).back.route,Series.grouped]
  -- route cast is step.cast.symm
  have E:(Series.natural 2).explore=[0,1]:=by decide
  let z(c:B):=(PhaseL k).tab (fun v=> f (pre c v))
  change ((Series.natural 2).explore.map z).flatten = z 0++z 1
  rw [E]; change z 0 ++ (z 1 ++ []) = _; rw [List.append_nil]
@[simp] theorem rootSize (f:Face 0→X):
    (PhaseL 0).tab f = [f Fin.elim0] := rfl
private theorem snoc_m {k} (v:Face k)(c d:B):
    pre c (fan v d) = fan (pre c v) d := by
  funext i
  -- cases last or castsucc
  refine Fin.lastCases ?_ (fun i=>?_) i
  · change join (c,fan v d) (Fin.last (k+1))=_
    rw [show Fin.last (k+1) = (Fin.last k).succ from rfl,tail_j]
    change fan v d (Fin.last k)=fan (pre c v) d (Fin.last _)
    simp [fan]
  refine Fin.cases ?_ (fun j=> ?_) i
  · rw [show (0:Fin (k+1)).castSucc =0 from rfl]
    rw [← show (0:Fin (k+1)).castSucc=(0:Fin (k+2)) from rfl,fan,fan,Fin.snoc_castSucc]
    rfl -- unify first
  rw [fan,fan,Fin.snoc_castSucc]
  change join (c,fan v d) j.castSucc.succ=join (c,v) j.succ
  rw [tail_j,fan,Fin.snoc_castSucc,tail_j]
-- zip interleave
abbrev duo (x:X×X) : List X:=[x.1,x.2]
theorem woven (f:Face (k+1)→X):
    (PhaseL (k+1)).tab f=
      ((PhaseL k).tab (fun v=> [f (fan v 0), f (fan v 1)])).flatten := by
  induction k with
  | zero=>
    rw [follow_pre,rootSize,rootSize,rootSize];
    have e (b:B): pre (k:=0) b Fin.elim0=fan Fin.elim0 b:=by
      funext i
      have w:i=Fin.last 0:=by exact @Subsingleton.elim (Fin 1) _ _ _
      simp [w,fan,pre,branch]
      rfl -- maybe
    simp [e]
  | succ k ih =>
    rw [follow_pre,ih (fun v=> f (pre 0 v)),ih (fun v=>f (pre 1 v)),follow_pre (k:=k) (fun v=> [_,_]),List.flatten_append]
    simp [snoc_m]

variable {Y:Type}
theorem w_l [Codec X] (f:Face (k+1)→X) (a:X):
    (lock duo a a ((PhaseL k).tab (fun v=> f (fan v 0)),(PhaseL k).tab (fun v=> f (fan v 1)))).flatten=
    (PhaseL (k+1)).tab f := by rw [paired,woven f]
@[simp] theorem phase_local (f:Fourier.Spot (2^k)→X):
    (PhaseL k).tab (f ∘ localE k)=List.ofFn f := by
  rw [← show f ∘ (Halo.noir k).cast ∘ (Earth.bolt k).cast=f ∘ localE k from funext (fun i=> by
    change Face k at i
    change f (localE k (layBit k ((Earth.bolt k).cast i)))=_
    rw [Earth.lightning]; rfl)]
  change (canon k).tab ((f ∘ (Halo.noir k).cast) ∘ (Earth.bolt k).cast) = _
  rw [← (Earth.bolt k).route, ← (Halo.noir k).route]
  change List.map f (List.finRange _)=_
  simp [List.finRange,Function.comp_def]
end Morse

end IntegerMultiplication
end Computability
end OAI

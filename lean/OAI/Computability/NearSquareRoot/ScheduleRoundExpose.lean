import OAI.Computability.NearSquareRoot.ScheduleRoundControl
import OAI.Computability.NearSquareRoot.ScheduleClock

/-!
# Exposing the round controller's head position as a unary word

Sweep the cursor left to its origin, writing one true bit per step. Then cross the
word in reverse while restoring the cursor. The blank just left of the word stops
the return sweep, leaving the unary output under its low-end head.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RoundExpose

open IntegerMultiplication TM

inductive State
  | scan | rewind | done
  deriving DecidableEq

instance : Finite State := Finite.of_injective (fun q : State => match q with
  | .scan => (0 : Fin 3) | .rewind => 1 | .done => 2) (by intro x y h; cases x <;> cases y <;> simp_all)

def letter (b : Bool) : Option Bool := if b then some true else none

def cursor (p : ℤ) : Tape (Option Bool) :=
  ⟨(RoundControl.cursor p).pos, fun d => letter ((RoundControl.cursor p).view d)⟩

def word (n : ℕ) (p : ℤ) : Tape (Option Bool) :=
  ⟨p, fun d => if 0 ≤ p+d ∧ p+d < n then some true else none⟩

@[simp] theorem word_at_zero (n : ℕ) :
    word n 0 = Tape.loaded none ((List.replicate n true).map some) := by
  simp only [word,Tape.loaded,Tape.mk.injEq,true_and,zero_add]
  funext k
  cases k with
  | ofNat i => simp [List.getElem?_replicate]; split <;> simp_all
  | negSucc => simp

def cfg (s : State) (p k : ℤ) (n : ℕ) : Config (Option Bool) State Bool :=
  ⟨s, fun i => if i then word n k else cursor p⟩

private def ops (a b : Move) (u v : Option Bool) (i : Bool) :=
  if i then (v,b) else (u,a)

def rule : Rule (Option Bool) State Bool := fun q heads =>
  match q with
  | .scan =>
    if (heads false).isSome then some (.rewind,ops .stay .left (heads false) (heads true))
    else some (.scan,ops .left .right (heads false) (some true))
  | .rewind =>
    if (heads true).isSome then some (.rewind,ops .right .left (heads false) (heads true))
    else some (.done,ops .stay .right (heads false) (heads true))
  | .done => none

private theorem cursor_move (p : ℤ) (m : Move) :
    (cursor p).apply ((cursor p).view 0,m) = cursor (p+m.shift) := by
  simp only [cursor, RoundControl.cursor, Tape.apply, add_zero,Tape.mk.injEq,true_and]
  funext d
  split
  · rw [show p + m.shift + d = p by omega]
  · rw [show p + m.shift + d = p + (d + m.shift) by omega]

private theorem word_move (n : ℕ) (p : ℤ) (m : Move) :
    (word n p).apply ((word n p).view 0,m) = word n (p+m.shift) := by
  simp only [word,Tape.apply,add_zero,Tape.mk.injEq,true_and]
  funext d
  split
  · rw [show p + m.shift + d = p by omega]
  · rw [show p + m.shift + d = p + (d+m.shift) by omega]

private theorem push_right (k : ℕ) :
    (word k k).apply (some true,.right) = word (k+1) (k+1 : ℕ) := by
  simp only [word,Tape.apply,Move.shift,Nat.cast_add,Nat.cast_one,Tape.mk.injEq,true_and]
  funext d
  change (if d+1=0 then some true else
    if 0 ≤ (k:ℤ)+(d+1) ∧ (k:ℤ)+(d+1) < k then some true else none) =
    (if 0 ≤ (k:ℤ)+1+d ∧ (k:ℤ)+1+d < k+1 then some true else none)
  split_ifs <;> first | rfl | omega

private theorem run_step {q q'} {p k p' k' : ℤ} {n n' : ℕ} {mi ma : Move}
    {v : Option Bool} (hp : p + mi.shift = p')
    (hm : rule q (fun i => ((cfg q p k n).tape i).view 0) =
      some (q',ops mi ma ((cursor p).view 0) v))
    (hx : (word n k).apply (v,ma) = word n' k') :
    advance rule (cfg q p k n) = some (cfg q' p' k' n') := by
  unfold advance
  change Option.map _ (rule q _) = _
  rw [hm]
  simp only [Option.map_some, Option.some.injEq]
  apply congrArg (Config.mk q')
  funext i
  cases i
  · exact hp ▸ cursor_move _ _
  · exact hx

private theorem copy_step (i k : ℕ) :
    advance rule (cfg .scan (i+1 : ℕ) k k) = some (cfg .scan i (k+1 : ℕ) (k+1)) := by
  apply run_step (mi := .left) (ma := .right) (v := some true) (by simp [Move.shift])
  · simp [rule,cfg,cursor,letter,RoundControl.cursor]; omega
  · exact push_right _

private theorem turn_step (n : ℕ) :
    advance rule (cfg .scan 0 n n) = some (cfg .rewind 0 ((n : ℤ)-1) n) := by
  apply run_step (mi := .stay) (ma := .left) (v := (word n n).view 0) (by rfl)
  · simp [rule,cfg,cursor,letter,RoundControl.cursor]
  · exact word_move _ _ _

private theorem return_step (i k n : ℕ) (hk : k < n) :
    advance rule (cfg .rewind i k n) = some (cfg .rewind (i+1 : ℕ) ((k:ℤ)-1) n) := by
  apply run_step (mi := .right) (ma := .left) (v := (word n k).view 0) (by simp [Move.shift])
  · simp [rule,cfg,word,hk]
  · exact word_move _ _ _

private theorem finish_step (i n : ℕ) :
    advance rule (cfg .rewind i (-1) n) = some (cfg .done i 0 n) := by
  apply run_step (mi := .stay) (ma := .right) (v := (word n (-1)).view 0) (by simp [Move.shift])
  · simp [rule,cfg,word]
  · exact word_move _ _ _

private abbrev Bounded (s : ℕ) := FencedRun rule (fun _ => (-1 : ℤ)) (fun _ => (s : ℤ))

private theorem single {q q'} {s n n' : ℕ} {p k p' k' : ℤ}
    (h : advance rule (cfg q p k n) = some (cfg q' p' k' n'))
    (lo : -1 ≤ p ∧ -1 ≤ k ∧ -1 ≤ p' ∧ -1 ≤ k')
    (hi : p ≤ s ∧ k ≤ s ∧ p' ≤ s ∧ k' ≤ s) :
    Bounded s (cfg q p k n) 1 (cfg q' p' k' n') := by
  refine ⟨.single h, ?_⟩
  intro j hj c hc i
  rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
  · have := trace_endpoint_unique hc (.nil _)
    subst c
    cases i <;> simp_all [cfg,word,cursor,RoundControl.cursor]
  · have := trace_endpoint_unique hc (.single h)
    subst c
    cases i <;> simp_all [cfg,word,cursor,RoundControl.cursor]

private theorem return_sweep (i k n : ℕ) (hi : i+k ≤ n) :
    Bounded n (cfg .rewind i ((k:ℤ)-1) n) (k+1) (cfg .done (i+k : ℕ) 0 n) := by
  induction k generalizing i with
  | zero =>
    simpa using single (s := n) (finish_step i n) (by omega) (by omega)
  | succ k ih =>
    have h := single (s := n) (return_step i k n (by omega)) (by omega) (by omega)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.trans (ih (i+1) (by omega))

private theorem sweeps (i k n : ℕ) (hi : i+k=n) :
    Bounded n (cfg .scan i k k) (i+1+n+1) (cfg .done n 0 n) := by
  induction i generalizing k with
  | zero =>
    have eq : k = n := by omega
    subst k
    have h := single (s := n) (turn_step n) (by omega) (by omega)
    have ht := h.trans (return_sweep 0 n n (by omega))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  | succ i ih =>
    have h := single (s := n) (copy_step i k) (by omega) (by omega)
    have ht := h.trans (ih (k+1) (by omega))
    convert ht using 1
    omega

/-- The persistent cursor is restored, and the output is the true-mark unary word
expected by the interpreter budget clock. Both heads stay in `[-1,n]`. -/
theorem expose (n : ℕ) :
    FencedRun rule (fun _ => -1) (fun _ => (n:ℤ))
      (cfg .scan n 0 0) (2*n+2) (cfg .done n 0 n) := by
  convert sweeps n 0 n (by omega) using 1
  omega

theorem expose_visits (n : ℕ) : VisitsAtMost rule (cfg .scan n 0 0) (2*n+2) (2*(n+2)) := by
  convert visitsAtMost_of_common_fence _ _ (expose n).2 using 1
  simp
  omega

theorem faithful_output (n : ℕ) :
    (word n 0).view = SM.display (List.replicate n true) := by
  rw [word_at_zero, SM.display_loaded]

end RoundExpose

end NearSquareRoot
end Computability
end OAI

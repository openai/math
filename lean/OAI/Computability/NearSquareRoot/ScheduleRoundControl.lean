import OAI.Computability.NearSquareRoot.ShortWordSpace

/-!
# Physical enumeration of geometric scheduling slots

Two one-dimensional tapes have a single mark at the origin. Their head offsets
are the zero-based candidate index and the current clock exponent. Thus the
last slot of round `s` has offsets `(s-1,0)`. Transferring the index back to the
other head starts the next round without multiplying or dividing any counters.
The state `offer` is the boundary at which a caller can suspend this control
during a bounded attempt.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RoundControl
open IntegerMultiplication

inductive State
  | initialize | offer | rollover
  deriving DecidableEq

instance : Finite State := Finite.of_injective
  (fun x : State => match x with | .initialize => (0 : Fin 3) | .offer => 1 | .rollover => 2)
  (by intro x y h; cases x <;> cases y <;> simp_all)

/-- Tape `false` holds the index, tape `true` the clock exponent. -/
def rule : TM.Rule Bool State Bool := fun st v =>
  let go (st' : State) (mi ma : TM.Move) := some (st', fun j => (v j, if j then ma else mi))
  match st with
  | .initialize => some (.offer, fun _ => (true, .stay))
  | .offer => if v true then go .rollover .stay .stay else go .offer .right .left
  | .rollover => if v false then go .offer .stay .right else go .rollover .left .right

def cursor (p : ℤ) : TM.Tape Bool := ⟨p, fun h => decide (p+h=0)⟩

def cfg (st : State) (i a : ℕ) : TM.Config Bool State Bool :=
  ⟨st, fun j => cursor (if j then a else i)⟩

def initial : TM.Config Bool State Bool := ⟨.initialize, fun _ => TM.Tape.loaded false []⟩

private theorem cursor_move (p : ℤ) (m : TM.Move) :
    (cursor p).apply ((cursor p).view 0, m) = cursor (p+m.shift) := by
  simp only [cursor, TM.Tape.apply, add_zero, TM.Tape.mk.injEq, true_and]
  funext d
  split
  · rw [show p + m.shift + d = p by omega]
  · rw [show p + m.shift + d = p + (d + m.shift) by omega]

theorem start : TM.advance rule initial = some (cfg .offer 0 0) := by
  simp only [TM.advance, rule, initial, Option.map_some, Option.some.injEq]
  apply congrArg (TM.Config.mk (A := Bool) (I := Bool) State.offer)
  funext j
  cases j <;> simp only [cursor, TM.Tape.apply, TM.Move.shift, add_zero, Nat.cast_zero,
    Bool.false_eq_true, ite_false, ite_true, zero_add, TM.Tape.loaded, TM.Tape.mk.injEq, true_and]
  all_goals
    funext h
    split <;> simp_all
    cases h <;> simp

private theorem step {st st' : State} {i a i' a' : ℕ} (mi ma : TM.Move)
    (hi : (i : ℤ) + mi.shift = i') (ha : (a : ℤ) + ma.shift = a')
    (h : rule st (fun j => ((cfg st i a).tape j).view 0) =
      some (st', fun j => (((cfg st i a).tape j).view 0, if j then ma else mi))) :
    TM.advance rule (cfg st i a) = some (cfg st' i' a') := by
  unfold TM.advance
  change Option.map _ (rule st _) = _
  rw [h]
  simp only [Option.map_some, Option.some.injEq]
  apply congrArg (TM.Config.mk st')
  funext j
  cases j
  · exact hi ▸ cursor_move i mi
  · exact ha ▸ cursor_move a ma

/-- Adjacent slots differ by a single simultaneous movement. -/
theorem next_slot (i a : ℕ) : TM.advance rule (cfg .offer i (a+1)) =
    some (cfg .offer (i+1) a) :=
  step .right .left (by simp [TM.Move.shift]) (by simp [TM.Move.shift])
    (by simp [rule, cfg, cursor]; omega)

theorem enter_rollover (i : ℕ) : TM.advance rule (cfg .offer i 0) =
    some (cfg .rollover i 0) := step .stay .stay (by simp [TM.Move.shift]) (by simp [TM.Move.shift])
      (by simp [rule, cfg, cursor])

theorem transfer (i a : ℕ) : TM.advance rule (cfg .rollover (i+1) a) =
    some (cfg .rollover i (a+1)) :=
  step .left .right (by simp [TM.Move.shift]) (by simp [TM.Move.shift])
    (by simp [rule, cfg, cursor]; omega)

theorem begin_round (a : ℕ) : TM.advance rule (cfg .rollover 0 a) =
    some (cfg .offer 0 (a+1)) :=
  step .stay .right (by simp [TM.Move.shift]) (by simp [TM.Move.shift])
    (by simp [rule, cfg, cursor])

private abbrev Bounded (s : ℕ) :=
  FencedRun rule (fun _ => 0) (fun _ => (s : ℤ))

private theorem single {st st' : State} {i a i' a' s : ℕ}
    (h : TM.advance rule (cfg st i a) = some (cfg st' i' a'))
    (hi : i ≤ s) (ha : a ≤ s) (hi' : i' ≤ s) (ha' : a' ≤ s) :
    Bounded s (cfg st i a) 1 (cfg st' i' a') := by
  refine ⟨.single h, ?_⟩
  intro k hk x run j
  rcases (show k=0 ∨ k=1 by omega) with rfl | rfl
  · have := trace_endpoint_unique run (.nil _)
    subst x
    cases j <;> simp_all [cfg, cursor]
  · have := trace_endpoint_unique run (.single h)
    subst x
    cases j <;> simp_all [cfg, cursor]

/-- Exactly `j` physical transitions present the `j`th slot of a round.
All intervening heads remain at offsets between zero and the round number. -/
theorem slots (i a j s : ℕ) (h : i+a+j ≤ s) :
    Bounded s (cfg .offer i (a+j)) j (cfg .offer (i+j) a) := by
  induction j generalizing i with
  | zero =>
    simp only [Nat.add_zero]
    refine ⟨.nil _, fun u hu z run b => ?_⟩
    obtain rfl : u=0 := by omega
    have := trace_endpoint_unique run (.nil _)
    subst z
    cases b <;> simp [cfg, cursor] <;> omega
  | succ j ih =>
    have fst := single (next_slot i (a+j)) (s := s) (by omega) (by omega) (by omega) (by omega)
    have rest := ih (i+1) (by omega)
    rw [show a+(j+1)=a+j+1 by omega, show i+(j+1)=i+1+j by omega,
      show j+1=1+j by omega]
    exact fst.trans rest

private theorem rollover (i a s : ℕ) (h : i+a+1 ≤ s) :
    Bounded s (cfg .rollover i a) (i+1) (cfg .offer 0 (a+i+1)) := by
  induction i generalizing a with
  | zero => simpa using single (begin_round a) (s := s) (by omega) (by omega) (by omega) (by omega)
  | succ i ih =>
    have fst := single (transfer i a) (s := s) (by omega) (by omega) (by omega) (by omega)
    have rest := ih (a+1) (by omega)
    have h := fst.trans rest
    rwa [show 1+(i+1)=(i+1)+1 by omega, show a+1+i+1=a+(i+1)+1 by omega] at h

/-- All `s+1` slots of a round and its rollover cost exactly `2*(s+1)`
control transitions apart from running the offered attempts. -/
theorem round (s B : ℕ) (h : s+1 ≤ B) :
    Bounded B (cfg .offer 0 s) (2*(s+1)) (cfg .offer 0 (s+1)) := by
  have first := slots 0 0 s B (by omega)
  have mid := single (enter_rollover s) (s := B) (by omega) (by omega) (by omega) (by omega)
  have last := rollover s 0 B (by omega)
  simp only [Nat.zero_add] at first last
  convert (first.trans mid).trans last using 1
  omega

/-- The physical controller, starting on two blank tapes, reaches the beginning
of round `s+1` after the stated control overhead, with two intervals of `s+1` cells. -/
theorem after_rounds (s : ℕ) :
    FencedRun rule (fun _ => 0) (fun _ => (s : ℤ)) initial (1+s*(s+1)) (cfg .offer 0 s) := by
  suffices hs : ∀ r ≤ s, Bounded s initial (1+r*(r+1)) (cfg .offer 0 r) by exact hs s le_rfl
  intro r hr
  induction r with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero]
    refine ⟨.single start, ?_⟩
    intro u hu z run b
    rcases (show u=0 ∨ u=1 by omega) with rfl | rfl
    · have := trace_endpoint_unique run (.nil _)
      subst z; simp [initial, TM.Tape.loaded]
    · have := trace_endpoint_unique run (.single start)
      subst z; cases b <;> simp [cfg,cursor]
  | succ r ih =>
    have h := (ih (by omega)).trans (round r s hr)
    convert h using 1
    ring

end RoundControl

end NearSquareRoot
end Computability
end OAI

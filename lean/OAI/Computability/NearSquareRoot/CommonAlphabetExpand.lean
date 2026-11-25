import OAI.Computability.NearSquareRoot.CommonAlphabetSweep
import OAI.Computability.NearSquareRoot.ScheduleInterpreterReset

/-! # Expanding a physical input stream into fixed-width alphabet blocks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Expand
open IntegerMultiplication TM
variable {A B : Type}

/-- The public source occupies tape `false`. The destination is tape `true`. -/
inductive Phase (A : Type) (w : ℕ)
  | scan | emit (x : A) (j : Fin w) | back | skip (j : Fin w) | done
  deriving Fintype

def pair {T : Type} (src dst : T) : Bool → T
  | false => src | true => dst

def rule (c : Code A) (parse : B → Option A) (put : Option Bool → B) :
    Rule B (Phase A c.width) Bool := fun q h =>
  let unchanged q' (s d : Move) := some (q', pair (h false,s) (h true,d))
  match q with
  | .scan => match parse (h false) with
    | none => unchanged .back .left .stay
    | some x => unchanged (.emit x (first c)) .right .stay
  | .emit x j => some (atIndex _ (.emit x) .scan (j.val+1),
      pair (h false,.stay) (put (c.enc x j),.right))
  | .back => match parse (h false) with
    | none => unchanged .done .right .stay
    | some _ => unchanged (.skip (first c)) .left .stay
  | .skip j => unchanged (atIndex _ .skip .back (j.val+1)) .stay .left
  | .done => none

/-- Absolute contents of a finite word, including the two blank rays. -/
def word (blank : B) (xs : List B) := (Tape.loaded blank xs).absolute

def marked (blank : B) (xs : List B) (n : ℕ) (p : ℤ) :=
  if p < n then word blank xs p else blank

theorem word_nat (blank : B) (xs : List B) (j : ℕ) :
    word blank xs j = xs[j]?.getD blank := by simp [word, Tape.loaded, Tape.absolute]

theorem word_neg (blank : B) (xs : List B) : word blank xs (-1) = blank := rfl

@[simp] theorem marked_zero (blank : B) (xs : List B) :
    marked blank xs 0 = fun _ => blank := by
  funext p
  cases p <;> simp [marked, word, Tape.absolute, Tape.loaded]

theorem marked_step (blank : B) (xs : List B) (j : ℕ) (v : B) (read : word blank xs j = v) :
    Function.update (marked blank xs j) (j:ℤ) v = marked blank xs (j+1) := by
  funext p
  by_cases he : p = j
  · subst p
    simp [marked,read]
  · by_cases hl : p < j
    · simp [Function.update, marked, he, hl, show p ≤ (j : ℤ) by omega]
    · simp [Function.update, marked, he, hl, show ¬p ≤ (j : ℤ) by omega]

@[simp] theorem marked_all (blank : B) (xs : List B) : marked blank xs xs.length = word blank xs := by
  funext p
  by_cases hp : p < xs.length
  · simp [marked, hp]
  · have hg := (Nat.cast_nonneg xs.length : (0:ℤ) ≤ xs.length)
    lift p to ℕ using (by omega)
    simp [marked, hp, word_nat, List.getElem?_eq_none (by omega : xs.length ≤ p)]

def cfg {P : Type} (q : P) (s d : ℤ) (f g : ℤ → B) : Config B P Bool :=
  ⟨q,pair (Reset.atHead s f) (Reset.atHead d g)⟩

theorem step {P : Type} (m : Rule B P Bool) (q q' : P) (s d : ℤ) (f g : ℤ → B)
    (v : B) (a b : Move)
    (h : m q (pair (f s) (g d)) = some (q', pair (f s,a) (v,b))) :
    advance m (cfg q s d f g) =
      some (cfg q' (s+a.shift) (d+b.shift) f (Function.update g d v)) := by
  unfold advance
  have hread : (fun i => ((cfg q s d f g).tape i).view 0) = pair (f s) (g d) := by
    funext i
    cases i <;> simp [cfg,pair,Reset.atHead]
  rw [hread]
  change (m q (pair (f s) (g d))).map _ = _
  rw [h]
  simp only [Option.map_some, Option.some.injEq, cfg, Config.mk.injEq, true_and]
  funext i
  cases i <;> simp [pair,Reset.atHead_apply,Function.update_eq_self]

theorem move {P : Type} (m : Rule B P Bool) (q q' : P) (s d : ℤ) (f g : ℤ → B)
    (a b : Move)
    (h : m q (pair (f s) (g d)) = some (q', pair (f s,a) (g d,b))) :
    advance m (cfg q s d f g) = some (cfg q' (s+a.shift) (d+b.shift) f g) := by
  simpa only [Function.update_eq_self] using step m q q' s d f g (g d) a b h

/-- A complete fixed-length scan between two known configurations, assembled from unit moves. -/
theorem steps {G P I : Type} (m : Rule G P I) (F : ℕ → Config G P I) (n : ℕ)
    (h : ∀ j, j < n → advance m (F j) = some (F (j+1))) :
    Trace (advance m) (F 0) n (F n) := by
  induction n with
  | zero => exact .nil _
  | succ k ih => exact (ih fun j hj => h j (by omega)).trans (.single (h k (by omega)))

end CommonAlphabet.Expand

end NearSquareRoot
end Computability
end OAI

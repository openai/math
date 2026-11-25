import OAI.Computability.NearSquareRoot.ScheduleInterpreterReset
import OAI.Computability.NearSquareRoot.ScheduleInterpreterParallel
import OAI.Computability.NearSquareRoot.ScheduleInterpreter

/-! # Reusing the digit-call tapes

Each head seeks its left fence, clears every cell through the right fence,
and returns to the marked origin. The immutable marks survive the sweep, so
the next digit pair starts on the same empty fenced bank.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingReset

open IntegerMultiplication TM Uniform

variable {B I : Type}

/-- The staging alphabet exposes three immutable markers and a local write
that restores the empty symbol while preserving those markers. -/
structure Marks (B : Type) where
  left : B → Bool
  right : B → Bool
  origin : B → Bool
  clear : B → B

def headRule (M : Marks B) : Rule B Reset.Phase Unit := fun q h =>
  let v := h ()
  match q with
  | .seekLeft => if M.left v then some (.erase, fun _ => (v,.stay))
    else some (.seekLeft, fun _ => (v,.left))
  | .erase => if M.right v then some (.rewind, fun _ => (M.clear v,.stay))
    else some (.erase, fun _ => (M.clear v,.right))
  | .rewind => if M.origin v then some (.done, fun _ => (v,.stay))
    else some (.rewind, fun _ => (v,.left))
  | .done => none

/-- All digit tapes are erased concurrently. A finished head waits at zero. -/
def rule [Fintype I] (M : Marks B) : Rule B (I → Reset.Phase) I :=
  Parallel.rule (fun _ => headRule M)

private def cfg (q : Reset.Phase) (p : ℤ) (f : ℤ → B) : Config B Reset.Phase Unit :=
  ⟨q, fun _ => Reset.atHead p f⟩

private def checked (M : Marks B) (R : ℕ) (c : Config B Reset.Phase Unit) :=
  if -(R : ℤ) ≤ (c.tape ()).pos ∧ (c.tape ()).pos ≤ R then advance (headRule M) c else none

private theorem step (M : Marks B) {R : ℕ} {q q' : Reset.Phase} {p : ℤ}
    {f : ℤ → B} {v : B} {d : Move} (hp : -(R : ℤ) ≤ p ∧ p ≤ R)
    (h : headRule M q (fun _ => f p) = some (q', fun _ => (v,d))) :
    checked M R (cfg q p f) = some (cfg q' (p+d.shift) (Function.update f p v)) := by
  simp only [checked, cfg, Reset.atHead, hp, and_self, ite_true, advance, add_zero]
  rw [h]
  change some (Config.mk _ (fun _ => (Reset.atHead p f).apply (v,d))) = _
  rw [Reset.atHead_apply]
  rfl

private theorem backward {X : Type} {s : X → Option X} (x : ℕ → X) (n : ℕ)
    (next : ∀ k < n, s (x (k+1)) = some (x k)) : Trace s (x n) n (x 0) := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    simpa [Nat.add_comm] using Trace.cons (next n (by omega)) (ih (fun k hk => next k (by omega)))

private theorem forward {X : Type} {s : X → Option X} (x : ℕ → X) (n : ℕ)
    (next : ∀ k < n, s (x k) = some (x (k+1))) : Trace s (x 0) n (x n) := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    exact (ih (fun k hk => next k (by omega))).trans (.single (next n (by omega)))

private theorem checked_sound (M : Marks B) {R : ℕ} {x y : Config B Reset.Phase Unit} {n}
    (h : Trace (checked M R) x n y) : Trace (advance (headRule M)) x n y := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    unfold checked at hs
    split at hs
    · exact .cons hs ih
    · cases hs

private theorem checked_prefix (M : Marks B) {R : ℕ} {x y : Config B Reset.Phase Unit} {n}
    (h : Trace (checked M R) x n y) (halt : advance (headRule M) y = none)
    (endpos : -(R : ℤ) ≤ (y.tape ()).pos ∧ (y.tape ()).pos ≤ R)
    {k z} (cut : Trace (advance (headRule M)) x k z) :
    -(R : ℤ) ≤ (z.tape ()).pos ∧ (z.tape ()).pos ≤ R := by
  induction h generalizing k with
  | nil =>
    cases cut with
    | nil => exact endpos
    | cons hs => rw [halt] at hs; cases hs
  | cons hs _ ih =>
    unfold checked at hs
    split at hs
    · rename_i inside
      cases cut with
      | nil => exact inside
      | cons ht tail => rw [hs] at ht; cases ht; exact ih halt endpos tail
    · cases hs

/-- A sweep from any starting head position in the fence, with the target
given at every absolute address, including permanently untouched exterior cells. -/
private theorem head_reset (M : Marks B) (R : ℕ) (p : ℤ) (f fresh : ℤ → B)
    (hp : -(R : ℤ) ≤ p ∧ p ≤ R)
    (hl : ∀ z, M.left (f z) = decide (z = -(R : ℤ)))
    (hr : ∀ z, M.right (f z) = decide (z = (R : ℤ)))
    (ho : ∀ z, M.origin (fresh z) = decide (z = 0))
    (hc : ∀ z, M.clear (f z) = fresh z)
    (outside : ∀ z, z < -(R : ℤ) ∨ (R : ℤ) < z → f z = fresh z) :
    ∃ n ≤ 5*R+3, Trace (advance (headRule M)) (cfg .seekLeft p f) n (cfg .done 0 fresh) ∧
      ∀ {k c}, Trace (advance (headRule M)) (cfg .seekLeft p f) k c →
        -(R : ℤ) ≤ (c.tape ()).pos ∧ (c.tape ()).pos ≤ R := by
  let l := -(R : ℤ)
  let a (k : ℕ) := l + k
  let stage (k : ℕ) (z : ℤ) := if l ≤ z ∧ z < a k then fresh z else f z
  have here (k : ℕ) : stage k (a k) = f (a k) := by simp [stage]
  have write (k : ℕ) : Function.update (stage k) (a k) (fresh (a k)) = stage (k+1) := by
    funext z
    by_cases e : z = a k
    · subst z
      simp [stage,a]
    · rw [Function.update_of_ne e]
      simp only [stage]
      dsimp [a] at *
      split_ifs <;> first | rfl | omega
  let d := (p-l).toNat
  have hd : a d = p := by dsimp [a,d,l]; omega
  have h₁ := backward (s := checked M R) (fun k => cfg .seekLeft (a k) f) d (by
    intro k hk
    have hn : a (k+1) ≠ l := by dsimp [a]; omega
    have st := step M (q := .seekLeft) (q' := .seekLeft) (d := .left) (p := a (k+1))
      (f := f) (v := f (a (k+1))) (R := R) (by dsimp [a,d,l] at *; omega)
      (by simp [headRule,hl,← show l = -(R:ℤ) from rfl,hn])
    rw [show a (k+1) + Move.left.shift = a k by dsimp [a,Move.shift]; omega] at st
    simpa using st)
  have t₁ := step M (q := .seekLeft) (q' := .erase) (d := .stay) (p := l) (R := R)
    (f := f) (v := f l) (by dsimp [l]; omega) (by simp [headRule,hl,l])
  have h₂ := forward (s := checked M R) (fun k => cfg .erase (a k) (stage k)) (2*R) (by
    intro k hk
    have hn : a k ≠ R := by dsimp [a,l]; omega
    have st := step M (q := .erase) (q' := .erase) (d := .right) (p := a k)
      (f := stage k) (v := fresh (a k)) (R := R) (by dsimp [a,l]; omega)
      (by simp [headRule,here,hr,hn,hc])
    simpa [write,a,Move.shift,add_assoc] using st)
  have ha : a (2*R) = R := by dsimp [a,l]; omega
  have hg : stage (2*R+1) = fresh := by
    funext z
    simp only [stage]
    split
    · rfl
    · apply outside
      dsimp [a,l] at *
      omega
  have t₂ := step M (q := .erase) (q' := .rewind) (d := .stay) (p := a (2*R))
    (f := stage (2*R)) (v := fresh (a (2*R))) (R := R) (by rw [ha]; omega)
    (by simp only [headRule, here, hr, hc]; simp [ha])
  have h₃ := backward (s := checked M R) (fun k => cfg .rewind k fresh) R (by
    intro k hk
    have st := step M (q := .rewind) (q' := .rewind) (d := .left) (p := ((k+1:ℕ):ℤ))
      (f := fresh) (v := fresh (k+1:ℕ)) (R := R) (by omega)
      (by simp [headRule,ho]; omega)
    rw [show ((k+1:ℕ):ℤ) + Move.left.shift = k by simp [Move.shift]] at st
    simpa using st)
  have t₃ := step M (q := .rewind) (q' := .done) (d := .stay) (p := 0) (R := R)
    (f := fresh) (v := fresh 0) (by omega) (by simp [headRule,ho])
  have hzero : stage 0 = f := by
    funext z
    simp [stage,a,show ¬(l ≤ z ∧ z < l) by omega]
  rw [hd, show a 0 = l by simp [a]] at h₁
  simp only [Move.shift, add_zero, Function.update_eq_self] at t₁ t₃
  rw [write, hg, ha] at t₂
  simp only [Move.shift, add_zero] at t₂
  rw [ha] at h₂
  rw [hzero, show a 0 = l by simp [a]] at h₂
  have run := ((((h₁.trans (.single t₁)).trans h₂).trans (.single t₂)).trans h₃).trans (.single t₃)
  exact ⟨_, by dsimp [d,l]; omega, checked_sound M run,
    fun h => checked_prefix M run rfl (by change -(R:ℤ) ≤ 0 ∧ 0 ≤ (R:ℤ); omega) h⟩

def entry (T : I → Tape B) : Config B (I → Reset.Phase) I :=
  ⟨fun _ => .seekLeft, T⟩

def done (fresh : I → ℤ → B) : Config B (I → Reset.Phase) I :=
  ⟨fun _ => .done, fun i => Reset.atHead 0 (fresh i)⟩

private theorem atHead_absolute (T : Tape B) : Reset.atHead T.pos T.absolute = T := by
  cases T
  simp [Reset.atHead, Tape.absolute]

/-- The endpoint fixes the whole contents of every tape and places every
head at the origin. All prefixes of the simultaneous reset fit in the fence.
The same rule serves every radius and every digit call. -/
theorem reset [Fintype I] (M : Marks B) (R : ℕ) (T : I → Tape B) (fresh : I → ℤ → B)
    (hp : ∀ i, -(R : ℤ) ≤ (T i).pos ∧ (T i).pos ≤ R)
    (hl : ∀ i z, M.left ((T i).absolute z) = decide (z = -(R : ℤ)))
    (hr : ∀ i z, M.right ((T i).absolute z) = decide (z = (R : ℤ)))
    (ho : ∀ i z, M.origin (fresh i z) = decide (z = 0))
    (hc : ∀ i z, M.clear ((T i).absolute z) = fresh i z)
    (outside : ∀ i z, z < -(R : ℤ) ∨ (R : ℤ) < z → (T i).absolute z = fresh i z) :
    ∃ n ≤ 5*R+3, Trace (advance (rule M)) (entry T) n (done fresh) ∧
      advance (rule M) (done fresh) = none ∧
      ∀ {k c}, Trace (advance (rule M)) (entry T) k c →
        ∀ i, -(R : ℤ) ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ R := by
  let x i := cfg .seekLeft (T i).pos (T i).absolute
  let y i := cfg .done 0 (fresh i)
  have each i := head_reset M R (T i).pos (T i).absolute (fresh i) (hp i) (hl i) (hr i)
    (ho i) (hc i) (outside i)
  have start : entry T = Parallel.pack x := by
    simp [entry, Parallel.pack, x, cfg, atHead_absolute]
  change ∃ n ≤ _, Trace _ _ n (Parallel.pack y) ∧ _ ∧ _
  rw [start]
  obtain ⟨n, hn, run, halt⟩ := Parallel.trace (fun _ => headRule M) x y (5*R+3) (fun i => by
    obtain ⟨t, ht, h, _⟩ := each i
    exact ⟨t, ht, h⟩) (fun _ => rfl)
  refine ⟨n,hn,run,halt,fun cut i => ?_⟩
  obtain ⟨z,rfl,hz⟩ := Parallel.project_prefix (fun _ => headRule M) x cut
  obtain ⟨_,_,_,fits⟩ := each i
  obtain ⟨_,_,localRun⟩ := hz i
  exact fits localRun

variable {A Q : Type}

/-- The digit-call fence is augmented with an immutable origin bit. -/
abbrev Symbol (A : Type) := Fence.Symbol A × Bool

def marks (blank : A) : Marks (Symbol A) :=
  ⟨fun v => v.1.2.1, fun v => v.1.2.2, Prod.snd, fun v => ((blank,v.1.2),v.2)⟩

def symbol (R : ℕ) (z : ℤ) (a : A) : Symbol A :=
  ((a,Fence.bits (-(R : ℤ)) R z),decide (z = 0))

def markedTape (R : ℕ) (t : Tape A) : Tape (Symbol A) :=
  ⟨t.pos, fun j => symbol R (t.pos+j) (t.view j)⟩

@[simp] theorem markedTape_absolute (R : ℕ) (t : Tape A) (z : ℤ) :
    (markedTape R t).absolute z = symbol R z (t.absolute z) := by
  simp [markedTape,Tape.absolute]

/-- Clearing a guarded bank leaves the two boundary bits and the origin bit
at their original absolute addresses and erases all payload, on every tape. -/
theorem reset_marked [Fintype I] (blank : A) (R : ℕ) (T : I → Tape A)
    (hp : ∀ i, -(R : ℤ) ≤ (T i).pos ∧ (T i).pos ≤ R)
    (outside : ∀ i z, z < -(R : ℤ) ∨ (R : ℤ) < z → (T i).absolute z = blank) :
    let bank := fun i => markedTape R (T i)
    let fresh := fun (_ : I) z => symbol R z blank
    ∃ n ≤ 5*R+3, Trace (advance (rule (marks blank))) (entry bank) n (done fresh) ∧
      advance (rule (marks blank)) (done fresh) = none ∧
      ∀ {k c}, Trace (advance (rule (marks blank))) (entry bank) k c →
        ∀ i, -(R : ℤ) ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ R := by
  apply reset (marks blank) R _ _ hp
  · simp [marks,symbol,Fence.bits]
  · simp [marks,symbol,Fence.bits]
  · simp [marks,symbol]
  · simp [marks,symbol]
  · intro i z hz
    simp [outside i z hz]

/-- During a confined call and during output harvesting, all exterior cells
keep the values they had when the bank was loaded. -/
theorem outside_eq_of_confined (m : Rule B Q I) (R : ℕ) {x y t}
    (run : Trace (advance m) x t y)
    (fits : ∀ {k c}, k ≤ t → Trace (advance m) x k c →
      ∀ i, -(R : ℤ) ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ R)
    (i : I) (z : ℤ) (hz : z < -(R : ℤ) ∨ (R : ℤ) < z) :
    (y.tape i).absolute z = (x.tape i).absolute z := by
  induction run with
  | nil => rfl
  | @cons x u y t hs _ ih =>
    rw [ih (fun hk cut => fits (by omega) (.cons hs cut))]
    have hx := fits (Nat.zero_le _) (.nil x) i
    cases h : m x.pc (fun j => (x.tape j).view 0) with
    | none => simp [advance, h] at hs
    | some qr =>
      obtain ⟨q,ops⟩ := qr
      simp only [advance,h,Option.map_some,Option.some.injEq] at hs
      subst u
      simp [Tape.absolute_apply,show z ≠ (x.tape i).pos by omega]

end StagingReset

end NearSquareRoot
end Computability
end OAI

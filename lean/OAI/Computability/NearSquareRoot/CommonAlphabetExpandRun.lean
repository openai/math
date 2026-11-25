import OAI.Computability.NearSquareRoot.CommonAlphabetExpand

/-! # Exact run and return-to-origin theorem for stream expansion -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Expand
open IntegerMultiplication TM
variable {A B : Type} (c : Code A) (parse : B → Option A) (put : Option Bool → B)

private theorem emit (blank : B) (xs : List A) (i : ℕ) (hi : i < xs.length) (f : ℤ → B) :
    let out := (c.encodeList xs).map put
    Trace (advance (rule c parse put))
      (cfg (.emit xs[i] (first c)) (i+1 : ℕ) (i*c.width : ℕ) f (marked blank out (i*c.width)))
      c.width (cfg .scan (i+1 : ℕ) ((i+1)*c.width : ℕ) f (marked blank out ((i+1)*c.width))) := by
  let out := (c.encodeList xs).map put
  let F (k : ℕ) : Config B (Phase A c.width) Bool := cfg (atIndex c.width (.emit xs[i]) .scan k)
    (i+1 : ℕ) (i*c.width+k : ℕ) f (marked blank out (i*c.width+k))
  have run := steps (rule c parse put) F c.width fun k hk => by
    let j : Fin c.width := ⟨k,hk⟩
    have get : word blank out (i*c.width+k : ℕ) = put (c.enc xs[i] j) := by
      rw [word_nat]
      simp only [out, List.getElem?_map]
      change ((c.encodeList xs)[i*c.width+j.val]?.map put).getD blank = _
      rw [c.getElem?_encodeList xs i hi j]
      rfl
    have one := step (rule c parse put) (.emit xs[i] j) (atIndex c.width (.emit xs[i]) .scan (k+1))
      (i+1 : ℕ) (i*c.width+k : ℕ) f (marked blank out (i*c.width+k)) (put (c.enc xs[i] j))
      .stay .right rfl
    rw [marked_step blank out _ _ get] at one
    simpa [F, atIndex, hk, j, Move.shift, add_assoc] using one
  simpa [F, atIndex, c.pos, first, Nat.succ_mul, out] using run

private theorem forward (blank : B) (xs : List A) (f : ℤ → B)
    (read : ∀ j : ℕ, parse (f j) = xs[j]?) (j : ℕ) (hj : j ≤ xs.length) :
    let out := (c.encodeList xs).map put
    Trace (advance (rule c parse put)) (cfg .scan 0 0 f (fun _ => blank)) ((c.width+1)*j)
      (cfg .scan j (j*c.width : ℕ) f (marked blank out (j*c.width))) := by
  intro out
  induction j with
  | zero => simp [out]; exact .nil _
  | succ j ih =>
    have hj' : j < xs.length := by omega
    have get : parse (f j) = some xs[j] := (read j).trans (List.getElem?_eq_getElem hj')
    have start := move (rule c parse put) .scan (.emit xs[j] (first c)) j (j*c.width : ℕ)
      f (marked blank out (j*c.width)) .right .stay (by simp [rule, pair, get])
    have h := (ih (by omega)).trans ((Trace.single (by simpa [Move.shift] using start)).trans
      (emit c parse put blank xs j hj' f))
    simpa only [Nat.mul_succ, Nat.add_comm 1 c.width] using h

private theorem skip (u d : ℤ) (f g : ℤ → B) :
    Trace (advance (rule c parse put)) (cfg (.skip (first c)) u d f g)
      c.width (cfg .back u (d-c.width) f g) := by
  let F (k : ℕ) : Config B (Phase A c.width) Bool := cfg (atIndex c.width .skip .back k) u (d-k) f g
  have run := steps (rule c parse put) F c.width fun k hk => by
    let j : Fin c.width := ⟨k,hk⟩
    have one := move (rule c parse put) (.skip j) (atIndex c.width .skip .back (k+1))
      u (d-k) f g .stay .left rfl
    simpa [F, atIndex, hk, j, Move.shift, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using one
  simpa [F, atIndex, c.pos, first] using run

private theorem backward (xs : List A) (f g : ℤ → B)
    (read : ∀ j : ℕ, parse (f j) = xs[j]?) (stop : parse (f (-1)) = none)
    (j : ℕ) (hj : j ≤ xs.length) :
    Trace (advance (rule c parse put)) (cfg .back ((j:ℤ)-1) (j*c.width : ℕ) f g)
      ((c.width+1)*j+1) (cfg .done 0 0 f g) := by
  induction j with
  | zero =>
    have h := move (rule c parse put) .back .done (-1) 0 f g .right .stay
      (by simp [rule,pair,stop])
    simpa [Move.shift] using Trace.single h
  | succ j ih =>
    have hj' : j < xs.length := by omega
    have get : parse (f j) = some xs[j] := (read j).trans (List.getElem?_eq_getElem hj')
    have h := move (rule c parse put) .back (.skip (first c)) j ((j+1)*c.width : ℕ) f g
      .left .stay (by simp [rule,pair,get])
    have sk := skip c parse put ((j:ℤ)-1) ((j+1)*c.width : ℕ) f g
    have t := (Trace.single (by simpa [Move.shift, sub_eq_add_neg] using h)).trans
      ((by simpa [Nat.succ_mul,sub_eq_add_neg,add_mul] using sk : Trace _ _ _ _).trans (ih (by omega)))
    convert t using 1 <;> simp [Nat.mul_succ]
    omega

/-- A public letter stream can use ordinary zero, one and separator symbols. The decoder of
a legal source cell determines its block. Blank is the scan delimiter in both directions.
The final source and destination are *loaded* tapes with both heads back at zero. -/
theorem run (blank : B) (xs : List A) (input : List B) (empty : parse blank = none)
    (read : ∀ j : ℕ, parse (word blank input j) = xs[j]?) :
    let m := rule c parse put
    let start : Config B (Phase A c.width) Bool :=
      ⟨.scan, pair (Tape.loaded blank input) (Tape.loaded blank [])⟩
    let finish : Config B (Phase A c.width) Bool :=
      ⟨.done, pair (Tape.loaded blank input) (Tape.loaded blank ((c.encodeList xs).map put))⟩
    Trace (advance m) start (2*(c.width+1)*xs.length+2) finish ∧ advance m finish = none := by
  let f := word blank input
  let out := (c.encodeList xs).map put
  have len : out.length = xs.length*c.width := by simp [out]
  have sim := forward c parse put blank xs f read xs.length le_rfl
  change Trace (advance (rule c parse put)) _ _ (cfg .scan _ _ f (marked blank out _)) at sim
  rw [← len, marked_all] at sim
  have get : parse (f xs.length) = none := by simpa using read xs.length
  have pivot := move (rule c parse put) .scan .back xs.length (xs.length*c.width : ℕ) f
    (word blank out) .left .stay (by simp [rule,pair,get])
  have back := backward c parse put xs f (word blank out) read
    (by simpa [f,word_neg] using empty) xs.length le_rfl
  have trace := sim.trans ((Trace.single (by simpa [← len, Move.shift, sub_eq_add_neg] using pivot)).trans
    (by simpa [← len, sub_eq_add_neg] using back : Trace _ _ _ _))
  have atZero (v : List B) : Reset.atHead 0 (word blank v) = Tape.loaded blank v := by
    simp [Reset.atHead, word, Tape.loaded, Tape.absolute]
  have blankAt : Reset.atHead 0 (fun _ : ℤ => blank) = Tape.loaded blank [] := by
    suffices word blank [] = fun _ : ℤ => blank by rw [← this, atZero]
    funext p
    cases p <;> simp [word,Tape.loaded,Tape.absolute]
  refine ⟨?_, rfl⟩
  convert trace using 1 <;> first | simp [cfg, f, out, atZero, blankAt] | ring

end CommonAlphabet.Expand

end NearSquareRoot
end Computability
end OAI

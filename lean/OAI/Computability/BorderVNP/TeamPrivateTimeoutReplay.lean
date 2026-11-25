import OAI.Computability.BorderVNP.TeamPrivateTimeout
import OAI.Computability.BorderVNP.TeamPrivateCall

/-! # Exact branch choices of the native timeout

The timer uses no choice bits. On bounded data it preserves each separate
signed or zero return and the exact spelling of the private path. On other
data its extra terminal represents a zero at the clock boundary.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateTimeout

open TeamPrivateTape TeamPrivateValue TeamPrivateCall
open scoped Classical

variable {Q Γ : Type} {m g : ℕ}

/-- Replay on symbol tapes, retaining the precise sign (including zero) and
rejecting a noncanonical surplus or shortage of private choice bits. -/
def symbolEval (P : TapeTable Q Γ m) (blank : Γ) :
    ℕ → Q → (Fin m → SymbolTape Γ) → List Bool → Option (Option Bool)
  | 0, _, _, _ => none
  | f+1, q, ts, bits =>
    match P q (fun i => (ts i).head) with
    | .halt a s => if bits = [] then some (if a then some s else none) else none
    | .one c => symbolEval P blank f c.next (c.apply blank ts) bits
    | .two l r => match bits with
      | [] => none
      | b :: tail => let c := if b then r else l
                     symbolEval P blank f c.next (c.apply blank ts) tail

/-- The bit-track interpreter and the symbol interpreter recognize exactly
the same path spellings and signed returns. -/
theorem symbolEval_tracks (a : Alphabet Γ g) (P : TapeTable Q Γ m) (f : ℕ)
    (q : Q) (ts : Fin m → SymbolTape Γ) (bits : List Bool) :
    (evaluate (trackTable a P) f q (tracks a ts) bits).map Prod.fst = symbolEval P a.blank f q ts bits := by
  induction f generalizing q ts bits with
  | zero => rfl
  | succ f ih =>
    have he : (fun i : Fin m => a.read (fun j => heads (tracks a ts) (finProdFinEquiv (i,j)))) =
        fun i => (ts i).head := by
      funext i
      simpa only [heads,tracks,Equiv.symm_apply_apply,SymbolTape.track] using a.read_bits (ts i).head
    rw [evaluate,symbolEval]
    unfold trackTable
    rw [he]
    cases h : P q (fun i => (ts i).head) with
    | halt accept sign => by_cases hb : bits = [] <;> simp [hb]
    | one c =>
      change (evaluate (trackTable a P) f c.next ((c.tracks a).apply (tracks a ts)) bits).map Prod.fst = _
      rw [tracks_apply,ih]
    | two l r =>
      cases bits with
      | nil => rfl
      | cons b tail =>
        cases b with
        | false =>
          change (evaluate (trackTable a P) f l.next ((l.tracks a).apply (tracks a ts)) tail).map Prod.fst =
            symbolEval P a.blank f l.next (l.apply a.blank ts) tail
          rw [tracks_apply,ih]
        | true =>
          change (evaluate (trackTable a P) f r.next ((r.tracks a).apply (tracks a ts)) tail).map Prod.fst =
            symbolEval P a.blank f r.next (r.apply a.blank ts) tail
          rw [tracks_apply,ih]

variable (blank mark : Γ) (P : TapeTable Q Γ m)

/-- No timeout occurs along a bounded original call. All zero returns, signed
returns and exact private bit strings coincide path by path. -/
theorem symbolEval_at_stops (n : ℕ) (q : Q) (left : List Γ) (ts : Fin m → SymbolTape Γ)
    (bits : List Bool) (bounded : TapeStops P blank (n+1) q ts) :
    symbolEval (table blank mark P) blank (n+1) q (timedTapes blank mark left n ts) bits =
      symbolEval P blank (n+1) q ts bits := by
  induction n generalizing q left ts bits with
  | zero =>
    rw [TapeStops] at bounded
    cases h : P q (fun i => (ts i).head) with
    | halt a s => simp [symbolEval,table,timedTapes,h]
    | one c => simp [h,TapeStops] at bounded
    | two l r => simp [h,TapeStops] at bounded
  | succ n ih =>
    have head_eq : (fun i => (timedTapes blank mark left (n+1) ts i.succ).head) =
        fun i => (ts i).head := by funext i; simp [timedTapes]
    have hm : (timedTapes blank mark left (n+1) ts 0).head = mark := by simp [timedTapes,meter]
    rw [TapeStops] at bounded
    rw [symbolEval.eq_2,symbolEval.eq_2]
    simp only [table,head_eq,hm]
    cases h : P q (fun i => (ts i).head) with
    | halt a s => rfl
    | one c =>
      simp only [h] at bounded
      simp only [↓reduceIte,command_apply]
      exact ih c.next _ _ bits bounded
    | two l r =>
      simp only [h] at bounded
      cases bits with
      | nil => rfl
      | cons b bs =>
        cases b <;> simp only [Bool.false_eq_true,↓reduceIte,command_apply]
        · exact ih l.next _ _ bs bounded.1
        · exact ih r.next _ _ bs bounded.2

/-- Even on malformed inputs, the finite timer introduces no new positive
or negative returns. A newly reached timeout returns zero. -/
theorem symbolEval_signed (hmark : blank ≠ mark) (n : ℕ) (q : Q) (left : List Γ)
    (ts : Fin m → SymbolTape Γ) (bits : List Bool) :
    (symbolEval (table blank mark P) blank (n+1) q (timedTapes blank mark left n ts) bits).join =
      (symbolEval P blank (n+1) q ts bits).join := by
  induction n generalizing q left ts bits with
  | zero =>
    cases h : P q (fun i => (ts i).head) <;>
      cases bits <;> simp [symbolEval,table,timedTapes,meter,h,hmark]
  | succ n ih =>
    have heads_eq : (fun i => (timedTapes blank mark left (n+1) ts i.succ).head) =
      fun i => (ts i).head := by funext i; simp [timedTapes]
    have hm : (timedTapes blank mark left (n+1) ts 0).head = mark := by simp [timedTapes,meter]
    rw [symbolEval.eq_2,symbolEval.eq_2]
    simp only [table,heads_eq,hm]
    cases h : P q (fun i => (ts i).head) with
    | halt a s => rfl
    | one c =>
      simp only [↓reduceIte,command_apply]
      exact ih c.next _ _ bits
    | two l r =>
      cases bits with
      | nil => rfl
      | cons b bs =>
        cases b <;> simp only [Bool.false_eq_true,↓reduceIte,command_apply]
        · exact ih l.next _ _ bs
        · exact ih r.next _ _ bs

end TeamPrivateTimeout

end BorderVNP
end Computability
end OAI

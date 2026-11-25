import OAI.Computability.NearSquareRoot.ScheduleStagingSerialize

/-! # Absolute contents and the streaming write instruction -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingSerialize

open IntegerMultiplication TM Code CommonAlphabet
open CommonAlphabet.Expand (cfg pair)
open ChunkControl (Driver)
open StagingProtection (Cell blank)

variable (d : Driver)

def content (s : List Ltr) : ℤ → Cell d := Expand.word (blank d) (s.map (put d))

@[simp] theorem content_nil : content d [] = fun _ => blank d := by
  funext i
  cases i <;> simp [content,Expand.word,Tape.absolute,Tape.loaded]

@[simp] theorem at_zero (s : List Ltr) :
    Reset.atHead 0 (content d s) = Tape.loaded (blank d) (s.map (put d)) := by
  simp [Reset.atHead,content,Expand.word,Tape.absolute,Tape.loaded]

theorem content_at (s : List Ltr) (j : ℕ) :
    content d s j = (s[j]?.map (put d)).getD (blank d) := by
  simp only [content,Expand.word_nat,List.getElem?_map]

theorem content_get (s : List Ltr) (j : ℕ) (hj : j < s.length) :
    content d s j = put d s[j] := by simp [content_at,List.getElem?_eq_getElem hj]

@[simp] theorem content_end (s : List Ltr) : content d s s.length = blank d := by simp [content_at]
@[simp] theorem content_neg (s : List Ltr) : content d s (-1) = blank d := rfl

theorem content_next (pre tail : List Ltr) (a : Ltr) :
    content d (pre ++ a :: tail) pre.length = put d a := by
  simp [content_at]

theorem content_snoc (old : List Ltr) (a : Ltr) :
    Function.update (content d old) (old.length:ℤ) (put d a) = content d (old++[a]) := by
  funext i
  cases i with
  | negSucc n =>
    rw [Function.update_of_ne (by omega : Int.negSucc n ≠ (old.length : ℤ))]
    rfl
  | ofNat n =>
    change Function.update (content d old) (old.length:ℤ) (put d a) (n:ℤ) = content d (old++[a]) n
    by_cases h : n=old.length
    · subst n
      rw [Function.update_self,content_next]
    · rw [Function.update_of_ne (by omega : (n:ℤ) ≠ (old.length : ℤ))]
      by_cases lt : n < old.length
      · simp [content_at,List.getElem?_append_left lt]
      · simp only [content_at,List.getElem?_append_right (by omega : old.length ≤ n),
          List.getElem?_eq_none (by omega : old.length ≤ n),
          List.getElem?_eq_none (by simp; omega : [a].length ≤ n-old.length)]

def cursor {k : ℕ} (q : Phase k) (before after out : List Ltr) :=
  cfg q (before.length : ℤ) (out.length : ℤ) (content d (before++after)) (content d out)

/-- Extending the serialized word requires one physical write. The publication
head may either stay on the cell it wrote or advance to the next blank. -/
theorem write_step {k : ℕ} (q q' : Phase k) (source out : List Ltr) (s : ℤ) (v : Ltr)
    (a b : Move)
    (h : rule d k q (pair (content d source s) (blank d)) =
      some (q',pair (content d source s,a) (put d v,b))) :
    advance (rule d k) (cfg q s out.length (content d source) (content d out)) =
      some (cfg q' (s+a.shift) ((out.length:ℤ)+b.shift) (content d source) (content d (out++[v]))) := by
  have step := Expand.step (rule d k) q q' s out.length (content d source) (content d out)
    (put d v) a b (by simpa using h)
  rwa [content_snoc] at step

end StagingSerialize

end NearSquareRoot
end Computability
end OAI

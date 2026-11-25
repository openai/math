import OAI.Computability.NearSquareRoot.ShortWordStack

/-!
# Turning a staged request into physical input and output tapes

The first scan empties the source stack and translates its digits onto the
destination tape. On the return scan the source head moves left once for every
bit, skipping the delimiter. It thereby comes to rest at the top address of
the future double-width product.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingCopy

open IntegerMultiplication IntegerMultiplication.TM

structure Alphabet (X : Type) where
  blank : X
  mark : X
  src : Option Bool → X
  dst : Option Bool → X
  readSrc : X → Option (Option Bool)
  readDst : X → Option (Option Bool)
  src_ok : ∀ a, readSrc (src a) = some a
  end_src : readSrc blank = none
  dst_ok : ∀ a, readDst (dst a) = some a
  end_dst : readDst mark = none
  mark_ne_blank : mark ≠ blank
  dst_ne_blank : ∀ a, dst a ≠ blank

namespace Alphabet

/-- A three-letter decoder on a larger tape alphabet. -/
def decode {X : Type} [DecidableEq X] (enc : Option Bool → X) (v : X) : Option (Option Bool) :=
  if v = enc none then some none else if v = enc (some false) then some (some false)
  else if v = enc (some true) then some (some true) else none

theorem decode_enc {X : Type} [DecidableEq X] {enc : Option Bool → X}
    (h : Function.Injective enc) (a : Option Bool) : decode enc (enc a) = some a := by
  cases a with
  | none => simp [decode]
  | some b => cases b <;> simp [decode,h.eq_iff]

theorem decode_other {X : Type} [DecidableEq X] {enc : Option Bool → X} {v : X}
    (h : ∀ a, v ≠ enc a) : decode enc v = none := by simp [decode,h]

/-- Construct the alphabet from two injective encodings of the request letters.
The two encodings may share any of their symbols. -/
def ofEncoders {X : Type} [DecidableEq X] (b m : X) (src dst : Option Bool → X)
    (hs : Function.Injective src) (hd : Function.Injective dst) (hm : m ≠ b)
    (hsb : ∀ a, b ≠ src a) (hdb : ∀ a, dst a ≠ b) (hdm : ∀ a, m ≠ dst a) : Alphabet X :=
  ⟨b,m,src,dst,decode src,decode dst,decode_enc hs,decode_other hsb,decode_enc hd,
    decode_other hdm,hm,hdb⟩

end Alphabet

inductive Phase | start | mark | copy | back | done deriving DecidableEq

instance : Fintype Phase where
  elems := {.start, .mark, .copy, .back, .done}
  complete p := by cases p <;> decide

def both {α : Type*} (s d : α) : Bool → α
  | false => s
  | true => d

def cfg {X : Type} (phase : Phase) (s d : Tape X) : Config X Phase Bool := ⟨phase,both s d⟩

def rule {X : Type} (e : Alphabet X) : Rule X Phase Bool
  | .start, r => some (.mark,both (r false,.stay) (r true,.left))
  | .mark, r => some (.copy,both (r false,.stay) (e.mark,.right))
  | .copy, r => match e.readSrc (r false) with
    | some a => some (.copy,both (e.blank,.right) (e.dst a,.right))
    | none => some (.back,both (e.blank,.stay) (r true,.left))
  | .back, r => match e.readDst (r true) with
    | some a => some (.back, both (r false,if a.isSome then .left else .stay) (r true,.left))
    | none => some (.done, both (r false,.stay) (e.blank,.right))
  | .done, _ => none

def zip {X : Type} (blank : X) (p : ℤ) (l r : List X) : Tape X :=
  ⟨p,fun | .ofNat n => r[n]?.getD blank | .negSucc n => l[n]?.getD blank⟩

@[simp] theorem zip_head {X : Type} (blank : X) (p : ℤ) (l r : List X) :
    (zip blank p l r).view 0 = r.head?.getD blank := by cases r <;> rfl

theorem cfg_step {X : Type} {e : Alphabet X} {q q' : Phase} {s d : Tape X}
    {so do' : X × Move} (h : rule e q (both (s.view 0) (d.view 0)) = some (q',both so do')) :
    advance (rule e) (cfg q s d) = some (cfg q' (s.apply so) (d.apply do')) := by
  unfold advance
  have hr : (fun i => ((cfg q s d).tape i).view 0) = both (s.view 0) (d.view 0) := by
    funext i; cases i <;> rfl
  rw [hr, show (cfg q s d).pc = q from rfl,h]
  simp only [Option.map_some, Option.some.injEq, cfg, Config.mk.injEq, true_and]
  funext i
  cases i <;> rfl

theorem zip_right {X : Type} (b v : X) (p : ℤ) (l r : List X) :
    (zip b p l r).apply (v,.right) = zip b (p+1) (v::l) r.tail := by
  unfold zip Tape.apply
  congr 1
  funext i
  cases i with
  | ofNat k =>
    change (if (↑k : ℤ)+1 = 0 then _ else _) = _
    rw [ite_eq_right (by omega : ¬(↑k : ℤ)+1=0)]
    cases r <;> rfl
  | negSucc k =>
    cases k with
    | zero => rfl
    | succ k =>
      change (if Int.negSucc (k+1)+1=0 then _ else _) = _
      rw [ite_eq_right (by omega : ¬Int.negSucc (k+1)+1=0)]
      rfl

theorem zip_left {X : Type} (b v : X) (p : ℤ) (l r : List X) :
    (zip b p l r).apply (v,.left) = zip b (p-1) l.tail (l.head?.getD b :: v :: r.tail) := by
  unfold Tape.apply zip
  simp only [Move.shift, Tape.mk.injEq]
  refine ⟨by omega, ?_⟩
  funext i
  cases i with
  | ofNat n =>
    cases n with
    | zero => cases l <;> rfl
    | succ n => cases n with
      | zero => rfl
      | succ n =>
        change (if (↑(n+2) : ℤ)+(-1)=0 then _ else _) = _
        rw [ite_eq_right (by omega : ¬(↑(n+2) : ℤ)+(-1)=0)]
        rw [show Int.ofNat (n+1+1)+(-1) = Int.ofNat (n+1) by simp]
        cases r <;> rfl
  | negSucc n => cases l <;> rfl

@[simp] theorem zip_left_blank {X : Type} (b : X) (p : ℤ) (r : List X) :
    zip b p [b] r = zip b p [] r := by
  unfold zip
  congr 1
  funext i
  cases i with
  | ofNat => rfl
  | negSucc n => cases n <;> rfl

theorem zip_right_end {X : Type} (b : X) (p : ℤ) (l r : List X) :
    zip b p l (r ++ [b]) = zip b p l r := by
  unfold zip
  congr 1
  funext i
  cases i with
  | negSucc => rfl
  | ofNat n =>
    change (r ++ [b])[n]?.getD b = r[n]?.getD b
    by_cases h : n < r.length
    · rw [List.getElem?_append_left h]
    · simp [List.getElem?_append_right (by omega : r.length ≤ n),
        List.getElem?_eq_none (by omega : r.length ≤ n)]
      cases n-r.length <;> rfl


private theorem advance_forward {X : Type} (e : Alphabet X) (p q : ℤ)
    (a : Option Bool) (xs : List (Option Bool)) (old : List X) :
    advance (rule e)
      (cfg .copy (zip e.blank p [] ((e.src a) :: xs.map e.src)) (zip e.blank q old [])) =
    some (cfg .copy (zip e.blank (p + 1) [] (xs.map e.src))
      (zip e.blank (q + 1) (e.dst a :: old) [])) := by
  have h := cfg_step (e := e) (s := zip e.blank p [] (e.src a :: xs.map e.src))
    (d := zip e.blank q old []) (so := (e.blank,.right)) (do' := (e.dst a,.right))
    (q := .copy) (q' := .copy) (by simp [rule,both,e.src_ok])
  simpa [zip_right] using h

/-- The forward scan erases the source and writes the translated word immediately
after the existing destination prefix, using one transition per letter. -/
theorem forward_trace {X : Type} (e : Alphabet X) (xs : List (Option Bool))
    (p q : ℤ) (old : List X) :
    Trace (advance (rule e))
      (cfg .copy (zip e.blank p [] (xs.map e.src)) (zip e.blank q old [])) xs.length
      (cfg .copy (zip e.blank (p + xs.length) [] [])
        (zip e.blank (q + xs.length) ((xs.map e.dst).reverse ++ old) [])) := by
  induction xs generalizing p q old with
  | nil => simp [Trace.nil]
  | cons a xs ih =>
    have tr := Trace.cons (advance_forward e p q a xs old) (ih (p + 1) (q + 1) (e.dst a :: old))
    simpa [List.reverse_cons, List.append_assoc, add_assoc, add_comm, add_left_comm] using tr


private theorem blank_left {X : Type} (b : X) (p : ℤ) :
    (zip b p [] []).apply (b,.left) = zip b (p-1) [] [] := by
  rw [zip_left]
  change zip b (p-1) [] ([b] ++ [b]) = _
  rw [zip_right_end]
  exact zip_right_end b _ [] []

private theorem zip_stay {X : Type} (b : X) (p : ℤ) (l r : List X) :
    (zip b p l r).apply (r.head?.getD b,.stay) = zip b p l r := by
  simpa only [zip_head] using SM.Action.apply_stay (zip b p l r)

private def pointed {X : Type} (e : Alphabet X) (q : ℤ)
    (pending : List (Option Bool)) (past : List X) : Tape X :=
  let l := pending.map e.dst ++ [e.mark]
  zip e.blank q l.tail (l.head?.getD e.blank :: past)

private theorem back_one {X : Type} (e : Alphabet X) (a : Option Bool) (xs : List (Option Bool))
    (past : List X) (p q : ℤ) :
    advance (rule e) (cfg .back (zip e.blank p [] []) (pointed e q (a::xs) past)) =
    some (cfg .back (zip e.blank (p - (if a.isSome then 1 else 0)) [] [])
      (pointed e (q-1) xs (e.dst a :: past))) := by
  have h := cfg_step (q := .back) (q' := .back) (s := zip e.blank p [] [])
    (d := pointed e q (a::xs) past) (so := (e.blank,if a.isSome then .left else .stay))
    (do' := (e.dst a,.left)) (e := e) (by simp [rule,pointed,both,e.dst_ok])
  have hd : (pointed e q (a::xs) past).apply (e.dst a,.left) =
      pointed e (q-1) xs (e.dst a::past) := by simp [pointed,zip_left]
  rw [hd] at h
  cases a with
  | none =>
    have hz := zip_stay e.blank p [] []
    simpa using h.trans (by simpa using congrArg (fun w => some (cfg Phase.back w
      (pointed e (q-1) xs (e.dst none :: past)))) hz)
  | some a => simpa [blank_left] using h

private theorem backward_trace {X : Type} (e : Alphabet X) (xs : List (Option Bool))
    (past : List X) (p q : ℤ) :
    Trace (advance (rule e)) (cfg .back (zip e.blank p [] []) (pointed e q xs past))
      (xs.length+1) (cfg .done (zip e.blank (p - (xs.countP Option.isSome : ℤ)) [] [])
        (zip e.blank (q-(xs.length : ℤ)+1) [] (xs.reverse.map e.dst ++ past))) := by
  induction xs generalizing p q past with
  | nil =>
    have h := cfg_step (e:=e) (q:=.back) (q':=.done) (s:=zip e.blank p [] [])
      (d:=pointed e q [] past) (so:=(e.blank,.stay)) (do':=(e.blank,.right))
      (by simp [rule,pointed,both,e.end_dst])
    have hz := zip_stay e.blank p [] []
    simp at hz
    simpa [pointed,zip_right,hz] using Trace.cons h (Trace.nil _)
  | cons a xs ih =>
    have h := Trace.cons (back_one e a xs past p q)
      (ih (e.dst a :: past) (p - (if a.isSome then 1 else 0)) (q-1))
    cases a <;>
      simpa [List.countP_cons,List.reverse_cons,List.append_assoc,sub_eq_add_neg,
        add_assoc,add_comm,add_left_comm] using h

private theorem start_trace {X : Type} (e : Alphabet X) (s : Tape X) :
    Trace (advance (rule e)) (cfg .start s (zip e.blank 0 [] [])) 2
      (cfg .copy s (zip e.blank 0 [e.mark] [])) := by
  have h := cfg_step (e:=e) (q:=.start) (q':=.mark) (s:=s) (d:=zip e.blank 0 [] [])
    (so:=(s.view 0,.stay)) (do':=(e.blank,.left)) (by simp [rule,both])
  have j := cfg_step (e:=e) (q:=.mark) (q':=.copy) (s:=s) (d:=zip e.blank (-1) [] [])
    (so:=(s.view 0,.stay)) (do':=(e.mark,.right)) (by rfl)
  rw [SM.Action.apply_stay,blank_left] at h
  rw [SM.Action.apply_stay,zip_right] at j
  exact .cons h (.cons j (.nil _))


/-- The canonical bounded word at an arbitrary head coordinate. -/
def atPos {X : Type} (blank : X) (p : ℤ) (word : List X) : Tape X :=
  ⟨p,(Tape.loaded blank word).view⟩

theorem zip_atPos {X : Type} (b : X) (p : ℤ) (w : List X) :
    zip b p [] w = atPos b p w := by
  rfl

theorem atPos_zero {X : Type} (b : X) (w : List X) : atPos b 0 w = Tape.loaded b w := rfl

/-- Consume the stacked word, leave its public encoding on the second tape at
origin, and align the erased first tape at minus the number of bits. -/
theorem copy_word {X : Type} (e : Alphabet X) (w : List (Option Bool)) :
    Trace (advance (rule e))
      (cfg .start (atPos e.blank (-(w.length : ℤ)) (w.map e.src)) (Tape.loaded e.blank []))
      (2*w.length+4)
      (cfg .done (atPos e.blank (-(w.countP Option.isSome : ℤ)) [])
        (Tape.loaded e.blank (w.map e.dst))) := by
  let src := zip e.blank (-(w.length:ℤ)) [] (w.map e.src)
  have f := forward_trace e w (-(w.length:ℤ)) 0 [e.mark]
  simp only [neg_add_cancel,zero_add] at f
  have z := cfg_step (e:=e) (q:=.copy) (q':=.back) (s:=zip e.blank 0 [] [])
    (d:=zip e.blank (w.length:ℤ) ((w.map e.dst).reverse ++ [e.mark]) [])
    (so:=(e.blank,.stay)) (do':=(e.blank,.left)) (by simp [rule,both,e.end_src])
  have hz := zip_stay e.blank 0 [] []
  simp at hz
  rw [hz,zip_left] at z
  have z' : advance (rule e) (cfg .copy (zip e.blank 0 [] [])
      (zip e.blank (w.length:ℤ) ((w.map e.dst).reverse ++ [e.mark]) [])) =
      some (cfg .back (zip e.blank 0 [] []) (pointed e ((w.length:ℤ)-1) w.reverse [e.blank])) := by
    simpa [pointed,List.map_reverse] using z
  have h := ((start_trace e src).trans f).trans
    ((Trace.single z').trans (backward_trace e w.reverse [e.blank] 0 ((w.length:ℤ)-1)))
  have times : 2+w.length+(1+(w.reverse.length+1)) = 2*w.length+4 := by simp; omega
  have coord : (w.length:ℤ) - 1 - (w.reverse.length:ℤ) + 1 = 0 := by simp
  rw [times,coord] at h
  simpa only [src,List.reverse_reverse,List.countP_reverse,zero_sub,zip_right_end,
    zip_atPos,atPos_zero] using h

/-- Delimiter-separated public request, with digits stored most significant first. -/
def word (x y : List Bool) : List (Option Bool) := x.map some ++ none :: y.map some

@[simp] theorem word_length (x y : List Bool) : (word x y).length = x.length + y.length + 1 := by
  simp [word,add_assoc]

@[simp] theorem word_bits (x y : List Bool) :
    (word x y).countP Option.isSome = x.length+y.length := by
  simp [word,List.countP_append,List.countP_map,Function.comp_def]

theorem copy_request {X : Type} (e : Alphabet X) (x y : List Bool) :
    Trace (advance (rule e))
      (cfg .start (atPos e.blank (-(x.length+y.length+1 : ℤ)) ((word x y).map e.src))
        (Tape.loaded e.blank []))
      (2*(x.length+y.length+1)+4)
      (cfg .done (atPos e.blank (-(x.length+y.length : ℤ)) [])
        (Tape.loaded e.blank ((word x y).map e.dst))) := by
  simpa using copy_word e (word x y)

theorem copy_request_equal_width {X : Type} (e : Alphabet X) {x y : List Bool} {u : ℕ}
    (hx : x.length = u) (hy : y.length = u) :
    Trace (advance (rule e))
      (cfg .start (atPos e.blank (-(2*u+1 : ℤ)) ((word x y).map e.src))
        (Tape.loaded e.blank []))
      (4*u+6)
      (cfg .done (atPos e.blank (-(2*u : ℤ)) [])
        (Tape.loaded e.blank ((word x y).map e.dst))) := by
  have h := copy_request e x y
  rw [hx,hy] at h
  rw [show (u:ℤ)+u = 2*(u:ℤ) by omega,
    show 2*(u+u+1)+4 = 4*u+6 by omega] at h
  exact h

@[simp] theorem done_halts {X : Type} (e : Alphabet X) (s d : Tape X) :
    advance (rule e) (cfg .done s d) = none := rfl

/-- An absolute physical strip for every prefix of an equal-width request. -/
theorem copy_request_prefix {X : Type} (e : Alphabet X) (x y : List Bool) {u t : ℕ}
    {z : Config X Phase Bool} (ht : t ≤ 4*u+6)
    (h : Trace (advance (rule e))
      (cfg .start (atPos e.blank (-(2*u+1 : ℤ)) ((word x y).map e.src))
        (Tape.loaded e.blank [])) t z) (i : Bool) :
    -(6*u+7 : ℤ) ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ (4*u+6 : ℤ) := by
  have he := head_excursion h i
  cases i <;> simp [cfg,both,atPos,Tape.loaded] at he <;> omega

end StagingCopy

end NearSquareRoot
end Computability
end OAI

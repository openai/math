import OAI.Computability.NearSquareRoot.ScheduleGeneratorROMDigits
import OAI.Computability.NearSquareRoot.ScheduleInterpreterReset
import OAI.Computability.NearSquareRoot.ShortWordSpace
import Mathlib.Data.Fintype.Option
import Mathlib.Data.ZMod.Defs

/-!
# Finite-control decoder for generated candidate ROMs

The generator's main stack emits a Mathlib `trList` of natural numbers. A fixed
two-tape transducer reads their little-endian digits and separators. Its two
finite registers keep the residue and place value modulo the alphabet size.
Each separator writes one literal target letter. A final backwards scan puts the
output head at zero. The source tape is read-only and may begin at any address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorROM
open IntegerMultiplication TM Turing.PartrecToTM2
open scoped Fin.NatCast Fin.CommRing

variable {C D : Type} {M : ℕ}

/-- Numerical registers at the left-to-right scan phase; the other phases rewind or halt. -/
abbrev Control (M : ℕ) := (Fin (M+1) × Fin (M+1)) ⊕ Bool

private abbrev scan (a w : Fin (M+1)) : Control M := .inl (a,w)
private abbrev returning : Control M := .inr false
private abbrev done : Control M := .inr true

private def issue (q : Control M) (a b : D) (m n : Move) :
    Option (Control M × (Bool → D × Move)) :=
  some (q, fun i => if i then (b,n) else (a,m))

/-- This rule is fixed once the source decoder and literal target alphabet are fixed.
Tape false reads the list of numerals; tape true accumulates the output word. -/
def rule [DecidableEq D] (enum : C ≃ Fin (M+1)) (read : D → Option Γ') (out : C → D)
    (blank : D) : Rule D (Control M) Bool := fun q heads =>
  let a := heads false
  let b := heads true
  match q with
  | .inl (s,w) =>
    match read a with
    | some .bit0 => issue (scan s (w+w)) a b .right .stay
    | some .bit1 => issue (scan (s+w) (w+w)) a b .right .stay
    | some .cons => issue (scan 0 1) a (out (enum.symm s)) .right .right
    | _ => issue returning a b .stay .left
  | .inr false =>
    if b = blank then issue done a b .stay .right else issue returning a b .stay .left
  | .inr true => none

/-- Actual literal symbols are at absolute coordinates zero through the word length minus one. -/
def contents (blank : D) (xs : List D) : ℤ → D := (Tape.loaded blank xs).view

def config (q : Control M) (f : ℤ → D) (p : ℤ) (blank : D) (xs : List D) (u : ℤ) :
    Config D (Control M) Bool :=
  ⟨q,fun i => if i then Reset.atHead u (contents blank xs) else Reset.atHead p f⟩

def Reads (read : D → Option Γ') (f : ℤ → D) (p : ℤ) (s : List Γ') :=
  ∀ i : ℕ, read (f (p+i)) = s[i]?

private theorem head_reads {read : D → Option Γ'} {f : ℤ → D} {p s} {g : Γ'}
    (h : Reads read f p (g::s)) : read (f p) = some g := by simpa using h 0

private theorem tail_reads {read : D → Option Γ'} {f : ℤ → D} {p s} {g : Γ'}
    (h : Reads read f p (g::s)) : Reads read f (p+1) s := by
  intro i
  simpa [Int.add_assoc,Int.add_comm 1] using h (i+1)

private theorem append_contents (blank v : D) (xs : List D) :
    Function.update (contents blank xs) (xs.length:ℤ) v = contents blank (xs ++ [v]) := by
  funext k
  cases k with
  | negSucc n => simp [Function.update,contents,Tape.loaded]
  | ofNat i =>
    by_cases e : i = xs.length
    · subst i
      simp [contents,Tape.loaded]
    · by_cases hl : i < xs.length
      · simp [Function.update, e,contents,Tape.loaded, List.getElem?_append_left hl]
      · have hge : xs.length + 1 ≤ i := by omega
        simp [Function.update,e,contents,Tape.loaded, List.getElem?_eq_none (by omega : xs.length ≤ i),
          List.getElem?_eq_none (show (xs++[v]).length ≤ i by simpa using hge)]

private theorem unchanged {X : Type} (f : ℤ → X) (p : ℤ) (m : Move) :
    (Reset.atHead p f).apply (f p,m) = Reset.atHead (p+m.shift) f := by
  rw [Reset.atHead_apply, Function.update_eq_self]

section
variable [DecidableEq D] (enum : C ≃ Fin (M+1)) (read : D → Option Γ') (out : C → D) (blank : D)
local notation "δ" => advance (rule enum read out blank)

private theorem advance_at {q q' : Control M} {p u : ℤ} {xs ys : List D} {f : ℤ → D}
    {m n : Move} {v : D}
    (h : rule enum read out blank q (fun i => if i then contents blank xs u else f p) =
      issue q' (f p) v m n)
    (w : (Reset.atHead u (contents blank xs)).apply (v,n) =
      Reset.atHead (u+n.shift) (contents blank ys)) :
    δ (config q f p blank xs u) = some (config q' f (p+m.shift) blank ys (u+n.shift)) := by
  unfold advance
  have hv : (fun i => ((config q f p blank xs u).tape i).view 0) =
      (fun i => if i then contents blank xs u else f p) := by
    funext i; cases i <;> simp [config, Reset.atHead]
  change Option.map _ (rule enum read out blank q _) = _
  rw [hv, h]
  change some (Config.mk q' _) = some (Config.mk q' _)
  apply congrArg (some ∘ Config.mk q')
  funext i
  cases i
  · exact unchanged _ _ _
  · exact w

private theorem digit {p u : ℤ} {xs : List D} {f : ℤ → D} (s w : Fin (M+1))
    (g : Γ') (hg : g=.bit0 ∨ g=.bit1) (h : read (f p) = some g) :
    δ (config (scan s w) f p blank xs u) =
      some (config (scan (s + if g=.bit1 then w else 0) (w+w)) f (p+1) blank xs u) := by
  obtain rfl | rfl := hg
  case inl =>
    have ht := advance_at enum read out blank (m := .right) (n := .stay) (xs := xs) (f := f)
      (u := u) (p := p) (q := scan s w) (q' := scan s (w+w)) (by simp [rule,h])
      (unchanged (contents blank xs) u .stay)
    simpa [Move.shift] using ht
  case inr =>
    have ht := advance_at enum read out blank (m := .right) (n := .stay) (xs := xs) (f := f)
      (u := u) (p := p) (q := scan s w) (q' := scan (s+w) (w+w)) (by simp [rule,h]) (unchanged (contents blank xs) u .stay)
    simpa [Move.shift] using ht

private theorem scan_digits (gs tail : List Γ') (f : ℤ → D) (p u : ℤ) (xs : List D)
    (s w : Fin (M+1)) (valid : ∀ g ∈ gs, g=.bit0 ∨ g=.bit1)
    (h : Reads read f p (gs++tail)) :
    ∃ w', Trace δ (config (scan s w) f p blank xs u) gs.length
      (config (scan (s+w*(Nat.cast (R := Fin (M+1)) (digitsValue gs))) w') f (p+gs.length) blank xs u) ∧
      Reads read f (p+gs.length) tail := by
  induction gs generalizing s w p with
  | nil => exact ⟨w,by simpa [digitsValue] using Trace.nil (step := δ) (config (scan s w) f p blank xs u),
                    by simpa using h⟩
  | cons g gs ih =>
    have hd := digit enum read out blank (p := p) (u := u) (xs := xs) s w g
      (valid g (by simp)) (head_reads h)
    obtain ⟨w',hr,ht⟩ := ih (p+1) _ (w+w) (fun z hz => valid z (by simp [hz])) (tail_reads h)
    have tr := Trace.cons hd hr
    have off : p+1+gs.length = p+((g::gs).length:ℤ) := by simp; omega
    rw [off] at tr ht
    refine ⟨w',?_,ht⟩
    rw [show (g::gs).length = 1+gs.length by simp [Nat.add_comm]]
    convert tr using 3
    · obtain rfl | rfl := valid g (by simp) <;>
        simp [digitsValue,mul_add,add_mul,two_mul]
      all_goals abel
    · simp [Nat.add_comm]

private theorem emit (c : C) (s : List Γ') (f : ℤ → D) (p : ℤ) (xs : List D)
    (w : Fin (M+1)) (h : Reads read f p (.cons::s)) :
    δ (config (scan (enum c) w) f p blank xs xs.length) =
      some (config (scan 0 1) f (p+1) blank (xs++[out c]) (xs.length+1)) := by
  apply advance_at enum read out blank (m := .right) (n := .right) (v := out c)
  · simp [rule,head_reads h]
  · rw [Reset.atHead_apply,append_contents]

private theorem scan_list (v : List C) (xs : List D) (f : ℤ → D) (p : ℤ)
    (h : Reads read f p (trList (v.map (fun c => (enum c).val)))) :
    Trace δ (config (scan 0 1) f p blank xs xs.length)
      (trList (v.map (fun c => (enum c).val))).length
      (config (scan 0 1) f (p+(trList (v.map (fun c => (enum c).val))).length)
        blank (xs++v.map out) (xs++v.map out).length) ∧
    read (f (p+(trList (v.map (fun c => (enum c).val))).length)) = none := by
  induction v generalizing xs p with
  | nil => exact ⟨by simpa using Trace.nil (step := δ) (config (scan 0 1) f p blank xs xs.length),
                  by simpa using h 0⟩
  | cons c v ih =>
    let gs := trNat (enum c).val
    let tail := trList (v.map (fun e => (enum e).val))
    obtain ⟨w,hr,ht⟩ := scan_digits enum read out blank gs (.cons::tail) f p xs.length xs 0 1
      (digits_only _) h
    have hh : ((0:Fin (M+1)) + 1*(Nat.cast (R := Fin (M+1)) (digitsValue gs))) = enum c := by
      simp [gs,digitsValue_nat]
    rw [hh] at hr
    have sep := emit enum read out blank c tail f (p+gs.length) xs w ht
    obtain ⟨suffix,ended⟩ := ih (xs++[out c]) (p+gs.length+1) (tail_reads ht)
    rw [show (xs++[out c]).length = xs.length+1 by simp, Nat.cast_add, Nat.cast_one] at suffix
    have tr := (hr.trans (.single sep)).trans suffix
    have pos : p+gs.length+1+tail.length = p+(gs++Γ'.cons::tail).length := by simp; omega
    change read (f (p+gs.length+1+tail.length))=none at ended
    rw [pos] at ended
    refine ⟨?_,ended⟩
    change Trace δ _ (gs++Γ'.cons::tail).length
      (config _ f (p+(gs++Γ'.cons::tail).length) blank _ _)
    simpa [gs,tail, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Int.add_assoc,Int.add_comm,Int.add_left_comm] using tr

private theorem rewind (w : List D) (nw : ∀ d ∈ w, d ≠ blank) (f : ℤ → D) (p : ℤ)
    (k : ℕ) (hk : k ≤ w.length) :
    Trace δ (config returning f p blank w ((k:ℤ)-1)) (k+1)
      (config done f p blank w 0) := by
  induction k with
  | zero =>
    have hy := advance_at enum read out blank (m := .stay) (n := .right)
      (q := returning) (q' := done) (f := f) (p := p) (xs := w) (u := -1)
      (by simp [rule,show contents blank w (-1) = blank from rfl]) (unchanged (contents blank w) (-1) .right)
    exact Trace.single (by simpa [Move.shift,sub_eq_add_neg] using hy)
  | succ k ih =>
    have hlt : k < w.length := hk
    have hn : contents blank w k ≠ blank := by
      simpa [contents,Tape.loaded,List.getElem?_eq_getElem hlt] using nw w[k] (List.getElem_mem hlt)
    have hy := advance_at enum read out blank (m := .stay) (n := .left)
      (q := returning) (q' := returning) (f := f) (p := p) (xs := w) (u := (k:ℤ))
      (by simp [rule,hn]) (unchanged (contents blank w) k .left)
    have hr := ih (by omega)
    have st : δ (config returning f p blank w (k:ℤ)) = some (config returning f p blank w ((k:ℤ)-1)) :=
      by simpa [Move.shift,sub_eq_add_neg] using hy
    simpa [Nat.add_comm 1] using Trace.cons st hr

abbrev encoded (c : C) := (enum c).val

/-- The stream decoder writes the complete finite ROM starting at absolute address
zero. All token parsing, delimiter tests, rewinding and termination are charged. -/
theorem decode (v : List C) (f : ℤ → D) (p : ℤ) (hout : ∀ c, out c ≠ blank)
    (h : Reads read f p (trList (v.map (encoded enum)))) :
    let tokens := trList (v.map (encoded enum))
    let xs := v.map out
    let start := config (scan 0 1) f p blank [] 0
    let finish := config done f (p+tokens.length) blank xs 0
    Trace δ start (tokens.length + xs.length + 2) finish ∧ δ finish = none ∧
      finish.tape true = Tape.loaded blank xs := by
  let tokens := trList (v.map (encoded enum))
  let xs := v.map out
  let pend := p + tokens.length
  obtain ⟨hscan,hend⟩ := scan_list enum read out blank v [] f p h
  change read (f pend)=none at hend
  have scan' : Trace δ (config (scan 0 1) f p blank [] 0) tokens.length
      (config (scan 0 1) f pend blank xs xs.length) := by simpa [tokens,pend,xs,encoded] using hscan
  have h₁ := advance_at enum read out blank (m := .stay) (n := .left) (q := scan 0 1)
    (q' := returning) (p := pend) (f := f) (xs := xs) (u := (xs.length:ℤ))
    (by simp [rule,hend]) (unchanged (contents blank xs) _ .left)
  have turn : δ (config (scan 0 1) f pend blank xs xs.length) =
    some (config returning f pend blank xs ((xs.length:ℤ)-1)) := by simpa [Move.shift,sub_eq_add_neg] using h₁
  have nw : ∀ x ∈ xs, x ≠ blank := by
    intro x hx
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hx
    exact hout _
  have allSteps := (scan'.trans (Trace.single turn)).trans
    (rewind enum read out blank xs nw f pend xs.length le_rfl)
  refine ⟨?_,rfl,?_⟩
  · change Trace δ _ (tokens.length+xs.length+2) (config done f pend blank xs 0)
    convert allSteps using 1
    omega
  · change Reset.atHead 0 (contents blank xs) = Tape.loaded blank xs
    simp only [Reset.atHead,contents,Tape.loaded,zero_add]

/-- The decoder occupies fixed intervals around its initial heads, including any
partial run aborted by a clock or space fence. -/
theorem decode_space (v : List C) (f : ℤ → D) (p : ℤ) :
    let t := (trList (v.map (encoded enum))).length + v.length + 2
    let x := config (scan 0 1) f p blank [] 0
    VisitsAtMost (rule enum read out blank) x t (2*(2*t+1)) := by
  dsimp only
  let x := config (scan (M := M) 0 1) f p blank [] 0
  let t := (trList (v.map (encoded enum))).length + v.length + 2
  have space := visitsAtMost_of_tape_fences
    (m := rule enum read out blank) (init := x) (steps := t)
    (fun i => (x.tape i).pos - t) (fun i => (x.tape i).pos + t)
    (by intro u hu c hc i; have he := head_excursion hc i; omega)
  convert space using 1
  have hsize (i : Bool) : ((x.tape i).pos + t + 1 - ((x.tape i).pos - t)).toNat = 2*t+1 := by omega
  change 2*(2*t+1) = _
  simp_rw [hsize]
  simp

end
end GeneratorROM

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.NearSquareRoot.CommonAlphabetSweep
import OAI.Computability.NearSquareRoot.ScheduleInterpreterReset

/-! # A two-tape fixed-width decoder

Each scan reads a complete code block from tape `false` and advances once per
cell. A decoded bit is written on tape `true`. After the terminal block, the
contiguous output bits guide the return of both physical heads to the origin.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Compact

open IntegerMultiplication TM

inductive Phase (w : ℕ)
  | scan (buf : Letters w) (j : Fin w)
  | emit (bit : Option Bool)
  | back (j : Fin w)
  | prev
  | done
deriving Fintype

variable {A B : Type} (c : Code A)

def start : Phase c.width := .scan (fun _ => none) (first c)

private def ops (s d : B × Move) : Bool → B × Move
  | false => s
  | true => d

/-- Source digits and literal output symbols can have separate embeddings in
the common physical alphabet. `isBlank` is only inspected on the output. -/
def rule (digit : B → Option Bool) (decode : A → Option Bool) (bit : Bool → B)
    (isBlank : B → Bool) : Rule B (Phase c.width) Bool := fun q h =>
  let go (q' : Phase c.width) (x y : Move) :=
    some (q', ops (h false,x) (h true,y))
  match q with
  | .scan buf j =>
    let buf' := Function.update buf j (digit (h false))
    go (atIndex _ (.scan buf') (.emit (decode (c.dec buf'))) (j.val + 1)) .right .stay
  | .emit (some b) => some (start c, ops (h false,.stay) (bit b,.right))
  | .emit none => go (.back (first c)) .stay .left
  | .back j => go (atIndex _ .back .prev (j.val + 1)) .left .stay
  | .prev =>
    if isBlank (h true) then go .done .stay .right else go (.back (first c)) .stay .left
  | .done => none

def tapes (f g : ℤ → B) (p h : ℤ) : Bool → Tape B
  | false => Reset.atHead p f
  | true => Reset.atHead h g

def config {w : ℕ} (q : Phase w) (f g : ℤ → B) (p h : ℤ) : Config B (Phase w) Bool :=
  ⟨q, tapes f g p h⟩

variable (digit : B → Option Bool) (decode : A → Option Bool) (bit : Bool → B)
    (isBlank : B → Bool)

local notation "M" => rule c digit decode bit isBlank

private theorem writeStep {q q' : Phase c.width} {f g : ℤ → B} {p h : ℤ}
    (v : B) (s d : Move)
    (hh : ∀ a : Bool → B, a false = f p → a true = g h →
      M q a = some (q',ops (a false,s) (v,d))) :
    advance M (config q f g p h) =
      some (config q' f (Function.update g h v) (p+s.shift) (h+d.shift)) := by
  let a (i : Bool) := ((tapes f g p h) i).view 0
  have hs : a false = f p := by simp [a,tapes,Reset.atHead]
  have hd : a true = g h := by simp [a,tapes,Reset.atHead]
  change (M q a).map _ = _
  rw [hh a hs hd]
  simp only [Option.map_some, Option.some.injEq]
  congr 1
  funext i
  cases i
  · simpa [config,tapes,ops,hs,Function.update_eq_self] using
      Reset.atHead_apply p f (a false) s
  · exact Reset.atHead_apply h g v d

private theorem moveStep {q q' : Phase c.width} {f g : ℤ → B} {p h : ℤ}
    (s d : Move)
    (hh : ∀ a : Bool → B, a false = f p → a true = g h →
      M q a = some (q',ops (a false,s) (a true,d))) :
    advance M (config q f g p h) = some (config q' f g (p+s.shift) (h+d.shift)) := by
  simpa only [Function.update_eq_self] using writeStep c digit decode bit isBlank (q := q) (q' := q')
    (p := p) (h := h) (f := f) (g := g) (g h) s d
    (by intro a hx hy; rw [← hy]; exact hh a hx hy)

private theorem walk {γ : Type} {step : γ → Option γ} (n : ℕ) (x : ℕ → γ)
    (next : ∀ j, j < n → step (x j) = some (x (j+1))) : Trace step (x 0) n (x n) := by
  induction n with
  | zero => exact .nil _
  | succ n ih => exact (ih (fun j hj => next j (by omega))).trans (.single (next n (by omega)))

private def buf (word : Letters c.width) (k : ℕ) : Letters c.width :=
  fun j => if j.val < k then word j else none

private theorem buf_update (word : Letters c.width) (j : Fin c.width) :
    Function.update (buf c word j.val) j (word j) = buf c word (j.val+1) := by
  funext d
  by_cases hd : d = j
  · subst d; simp [buf]
  · have hn : d.val ≠ j.val := fun e => hd (Fin.ext e)
    have hl : d.val < j.val + 1 ↔ d.val < j.val := by omega
    simp [buf,Function.update_of_ne hd,hl]

/-- One scan reads all the digits and enters the output phase carrying the decoded bit. -/
theorem readBlock (f g : ℤ → B) (p h : ℤ) (word : Letters c.width)
    (read : ∀ j : Fin c.width, digit (f (p + j.val)) = word j) :
    Trace (advance M) (config (start c) f g p h) c.width
      (config (.emit (decode (c.dec word))) f g (p+c.width) h) := by
  let inner (d : Fin c.width) := Phase.scan (buf c word d.val) d
  let emitState := Phase.emit (w := c.width) (decode (c.dec word))
  let x (j : ℕ) := config (atIndex c.width inner emitState j) f g (p+j) h
  have step (j : ℕ) (hj : j < c.width) : advance M (x j) = some (x (j+1)) := by
    let d : Fin c.width := ⟨j,hj⟩
    have full : buf c word c.width = word := by funext v; simp [buf,v.isLt]
    have instr : ∀ a : Bool → B, a false = f (p+j) → a true = g h →
        M (inner d) a = some (atIndex c.width inner emitState (j+1),
          ops (a false,.right) (a true,.stay)) := by
      intro a ha _
      have hd : digit (f (p+j)) = word d := read d
      simp only [rule,inner,ha,hd,buf_update]
      by_cases hn : j+1 < c.width
      · simp [atIndex,d,hn]
      · have he : j+1 = c.width := by omega
        simp [atIndex,d,he,full,emitState]
    simpa [x,atIndex,hj,d,Move.shift,add_assoc] using
      moveStep c digit decode bit isBlank .right .stay instr
  have hist := walk c.width x step
  have empty : buf c word 0 = fun _ => none := by funext d; simp [buf]
  simpa [x,inner,emitState,atIndex,c.pos,empty,start,first] using hist

/-- The counted inverse sweep moves only the encoded source head. -/
theorem backBlock (f g : ℤ → B) (p h : ℤ) :
    Trace (advance M) (config (.back (first c)) f g (p+c.width) h) c.width
      (config .prev f g p h) := by
  let x (j : ℕ) := config (atIndex c.width .back .prev j) f g (p+c.width-j) h
  have step (j : ℕ) (hj : j < c.width) : advance M (x j) = some (x (j+1)) := by
    let d : Fin c.width := ⟨j,hj⟩
    have hist := moveStep c digit decode bit isBlank (q := .back d)
      (q' := atIndex c.width .back .prev (j+1)) (f := f) (g := g)
      (p := p+c.width-j) (h := h) .left .stay (by intro a _ _; rfl)
    have hp : p+c.width-j+Move.left.shift = p+c.width-(j+1:ℕ) := by simp [Move.shift]; omega
    rw [hp] at hist
    simpa [x,atIndex,hj,d,Move.shift] using hist
  simpa [x,atIndex,first,c.pos] using walk c.width x step

theorem emitBit (f g : ℤ → B) (p h : ℤ) (b : Bool) :
    advance M (config (.emit (some b)) f g p h) =
      some (config (start c) f (Function.update g h (bit b)) p (h+1)) := by
  simpa [Move.shift] using writeStep c digit decode bit isBlank (p := p) (h := h)
    (f := f) (g := g) (q := .emit (some b)) (q' := start c) (bit b) .stay .right
    (by intro a _ _; rfl)

theorem emitEnd (f g : ℤ → B) (p h : ℤ) :
    advance M (config (.emit none) f g p h) = some (config (.back (first c)) f g p (h-1)) := by
  simpa [Move.shift,sub_eq_add_neg] using moveStep c digit decode bit isBlank (p := p) (h := h)
    (f := f) (g := g) (q := .emit none) (q' := .back (first c)) .stay .left (by intro a _ _; rfl)

theorem prevBit (f g : ℤ → B) (p h : ℤ) (hh : isBlank (g h) = false) :
    advance M (config .prev f g p h) = some (config (.back (first c)) f g p (h-1)) := by
  simpa [Move.shift,sub_eq_add_neg] using moveStep c digit decode bit isBlank (p := p) (h := h)
    (f := f) (g := g) (q := .prev) (q' := .back (first c)) .stay .left
    (by intro a _ hd; simp [rule,hd,hh])

theorem prevEnd (f g : ℤ → B) (p h : ℤ) (hh : isBlank (g h) = true) :
    advance M (config .prev f g p h) = some (config .done f g p (h+1)) := by
  simpa [Move.shift] using moveStep c digit decode bit isBlank (p := p) (h := h)
    (f := f) (g := g) (q := .prev) (q' := .done) .stay .right
    (by intro a _ hd; simp [rule,hd,hh])

end CommonAlphabet.Compact

end NearSquareRoot
end Computability
end OAI

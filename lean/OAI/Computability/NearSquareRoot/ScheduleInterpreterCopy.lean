import OAI.Computability.NearSquareRoot.ScheduleInterpreterRestart

/-!
# Copying the successful tentative product to the literal output tape

The source has frontier and origin marks. Its head first finds the left frontier,
then the original zero position. From there both heads move to the right once per
decoded product bit. Other work tapes stay still. The dedicated output tape
starts blank and ends with the exact bit string at addresses starting at zero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Copy

open IntegerMultiplication TM

variable {A I : Type} [DecidableEq I]

inductive Phase | seek | rewind | copy deriving DecidableEq

instance : Fintype Phase := ⟨{.seek,.rewind,.copy}, by intro q; cases q <;> simp⟩

private def ops (src : I) (heads : Option I → A) (v : A) (input output : Move) :
    Option I → A × Move
  | none => (v,output)
  | some i => (heads (some i), if i = src then input else .stay)

def rule (src : I) (left origin : A → Bool) (decode : A → Option Bool) (bit : Bool → A) :
    Rule A Phase (Option I) := fun q h =>
  let read := h (some src)
  let go q' d := some (q', ops src h (h none) d .stay)
  match q with
  | .seek => if left read then go .rewind .stay else go .seek .left
  | .rewind => if origin read then go .copy .stay else go .rewind .right
  | .copy => (decode read).map fun b => (.copy, ops src h (bit b) .right .right)

def config (src : I) (other : I → Tape A) (q : Phase) (p h : ℤ)
    (source dest : ℤ → A) : Config A Phase (Option I) :=
  ⟨q, fun i => match i with
    | none => Reset.atHead h dest
    | some j => if j = src then Reset.atHead p source else other j⟩

private theorem stay (t : Tape A) : t.apply (t.view 0, Move.stay) = t := by
  cases t with
  | mk p f =>
    simp [Tape.apply, Move.shift]
    funext k
    split <;> simp_all

section
variable (src : I) (other : I → Tape A) (left origin : A → Bool)
    (decode : A → Option Bool) (bit : Bool → A) (f : ℤ → A)

private theorem step {q q' : Phase} {p h : ℤ} {g : ℤ → A} (v : A) (d o : Move)
    (expected : ∀ heads : Option I → A, heads (some src) = f p → heads none = g h →
      rule src left origin decode bit q heads = some (q', ops src heads v d o)) :
    advance (rule src left origin decode bit) (config src other q p h f g) =
      some (config src other q' (p+d.shift) (h+o.shift) f (Function.update g h v)) := by
  let old := config src other q p h f g
  let heads := fun i => (old.tape i).view 0
  have hr : heads (some src) = f p := by simp [heads, old, config, Reset.atHead]
  have ho : heads none = g h := by simp [heads, old, config, Reset.atHead]
  change (rule src left origin decode bit q heads).map _ = _
  rw [expected _ hr ho]
  simp only [Option.map_some, Option.some.injEq]
  congr 1
  funext i
  cases i with
  | none => exact Reset.atHead_apply h g v o
  | some i =>
    by_cases he : i = src
    · subst i
      simpa [config, ops, hr, Function.update_eq_self] using Reset.atHead_apply p f (f p) d
    · simp [config, ops, he, heads, old, stay]

private theorem move {q q' : Phase} {p h : ℤ} {g : ℤ → A} (d : Move)
    (expected : ∀ heads : Option I → A, heads (some src) = f p →
      rule src left origin decode bit q heads = some (q', ops src heads (heads none) d .stay)) :
    advance (rule src left origin decode bit) (config src other q p h f g) =
      some (config src other q' (p+d.shift) h f g) := by
  have unchanged : Function.update g h (g h) = g := by
    funext i
    by_cases he : i = h <;> simp [Function.update,he]
  calc
    _ = _ := step src other left origin decode bit f (g h) d .stay (fun hs hin hout => hout ▸ expected hs hin)
    _ = _ := by
      change some (config src other q' (p+d.shift) (h+0) f (Function.update g h (g h))) = _
      rw [add_zero, unchanged]

private theorem seek (l : ℤ) (k : ℕ) (g : ℤ → A)
    (mark : ∀ i, left (f i) = decide (i = l)) :
    Trace (advance (rule src left origin decode bit)) (config src other .seek (l+k) 0 f g) (k+1)
      (config src other .rewind l 0 f g) := by
  induction k with
  | zero =>
    simpa [Move.shift] using Trace.single
      (move src other left origin decode bit f (p := l) (h := 0) (g := g)
        (q := .seek) (q' := .rewind) .stay (by intro r hread; simp [rule,hread,mark]))
  | succ k ih =>
    have h := move src other left origin decode bit f (p := l+(k+1:ℕ)) (h := 0) (g := g)
      (q := .seek) (q' := .seek) .left (by intro r hread; simp [rule,hread,mark]; omega)
    have he : l+(k+1:ℕ) + Move.left.shift = l+k := by simp [Move.shift]; omega
    simpa only [Nat.add_comm 1] using Trace.cons (by simpa only [he] using h) ih

private theorem rewind (k : ℕ) (g : ℤ → A)
    (mark : ∀ i, origin (f i) = decide (i = 0)) :
    Trace (advance (rule src left origin decode bit)) (config src other .rewind (-(k:ℤ)) 0 f g) (k+1)
      (config src other .copy 0 0 f g) := by
  induction k with
  | zero =>
    simpa [Move.shift] using Trace.single
      (move src other left origin decode bit f (p := 0) (h := 0) (g := g)
        (q := .rewind) (q' := .copy) .stay (by intro r hread; simp [rule,hread,mark]))
  | succ k ih =>
    have h := move src other left origin decode bit f (p := -((k+1:ℕ):ℤ)) (h := 0) (g := g)
      (q := .rewind) (q' := .rewind) .right (by intro r hread; simp [rule,hread,mark]; omega)
    have he : -((k+1:ℕ):ℤ) + Move.right.shift = -(k:ℤ) := by simp [Move.shift]
    simpa only [Nat.add_comm 1] using Trace.cons (by simpa only [he] using h) ih

end

/-- The requested literal output layout, addressed independently of its head. -/
def rendering (blank : A) (bit : Bool → A) (z : List Bool) (p : ℤ) : A :=
  (Tape.loaded blank (z.map bit)).absolute p

/-- Contents of the literal output tape after writing its first `k` bits. -/
def written (blank : A) (bit : Bool → A) (z : List Bool) (k : ℕ) (p : ℤ) : A :=
  if p < k then rendering blank bit z p else blank

theorem written_zero (blank : A) (bit : Bool → A) (z : List Bool) :
    written blank bit z 0 = fun _ => blank := by
  funext p
  cases p <;> simp [written, rendering, Tape.absolute, Tape.loaded]

theorem written_succ (blank : A) (bit : Bool → A) (z : List Bool) (k : ℕ) (hk : k < z.length) :
    Function.update (written blank bit z k) (k:ℤ) (bit z[k]) = written blank bit z (k+1) := by
  funext p
  by_cases he : p = k
  · subst p
    simp [written, rendering, Tape.absolute, Tape.loaded, Function.update, List.getElem?_eq_getElem hk]
  · by_cases hl : p < k
    · simp [written, Function.update, he, hl, show p ≤ (k : ℤ) by omega]
    · simp [written, Function.update, he, hl, show ¬p ≤ (k : ℤ) by omega]

theorem written_all (blank : A) (bit : Bool → A) (z : List Bool) :
    written blank bit z z.length = rendering blank bit z := by
  funext p
  by_cases hl : p < z.length
  · simp [written,hl]
  · have hp := (Nat.cast_nonneg z.length : (0:ℤ) ≤ z.length)
    lift p to ℕ using (by omega)
    simp [written, hl, rendering, Tape.absolute, Tape.loaded,
      List.getElem?_eq_none (by omega : z.length ≤ p)]

private theorem writes (src : I) (other : I → Tape A) (left origin : A → Bool)
    (decode : A → Option Bool) (blank : A) (bit : Bool → A) (z : List Bool)
    (f : ℤ → A) (read : ∀ j : ℕ, decode (f j) = z[j]?) :
    ∀ k ≤ z.length, Trace (advance (rule src left origin decode bit))
      (config src other .copy 0 0 f (fun _ => blank)) k
      (config src other .copy k k f (written blank bit z k)) := by
  intro k hk
  induction k with
  | zero => simpa only [written_zero, Nat.cast_zero] using
      Trace.nil (step := advance (rule src left origin decode bit)) (config src other .copy 0 0 f (fun _ => blank))
  | succ k ih =>
    have hl : k < z.length := by omega
    have hs := step src other left origin decode bit f (p := k) (h := k) (g := written blank bit z k)
      (q := .copy) (q' := .copy) (bit z[k]) .right .right
      (by intro r hr _; simp only [rule,hr,read,List.getElem?_eq_getElem hl,Option.map_some])
    exact (ih (by omega)).trans (.single (by simpa [Move.shift, written_succ blank bit z k hl] using hs))

theorem run (src : I) (other : I → Tape A) (left origin : A → Bool) (decode : A → Option Bool)
    (blank : A) (bit : Bool → A) (z : List Bool) (f : ℤ → A) (l p : ℤ)
    (left_mark : ∀ i, left (f i) = decide (i = l))
    (origin_mark : ∀ i, origin (f i) = decide (i = 0))
    (hl : l ≤ p) (hz : l ≤ 0) (read : ∀ j : ℕ, decode (f j) = z[j]?) :
    let stop := config src other .copy z.length z.length f (rendering blank bit z)
    let t := (p-l).toNat+(-l).toNat+z.length+2
    Trace (advance (rule src left origin decode bit)) (config src other .seek p 0 f (fun _ => blank)) t stop ∧
      advance (rule src left origin decode bit) stop = none ∧
      whole blank (z.map bit) (stop.tape none) := by
  have h₁ := seek src other left origin decode bit f l (p-l).toNat (fun _ => blank) left_mark
  have h₂ := rewind src other left origin decode bit f (-l).toNat (fun _ => blank) origin_mark
  have h₃ := writes src other left origin decode blank bit z f read z.length le_rfl
  rw [show l+((p-l).toNat : ℤ)=p by omega] at h₁
  rw [show -((-l).toNat : ℤ)=l by omega] at h₂
  rw [written_all] at h₃
  refine ⟨?_, ?_, ?_⟩
  · convert (h₁.trans h₂).trans h₃ using 1; omega
  · simp [advance, rule, config, Reset.atHead, read]
  · funext i
    simp [Tape.absolute, Reset.atHead, config, rendering, Tape.loaded]

/-- Attach a dedicated blank output tape to an existing physical configuration. -/
def beginCopy (blank : A) (tape : I → Tape A) : Config A Phase (Option I) :=
  ⟨.seek, fun i => match i with | none => Tape.loaded blank [] | some j => tape j⟩

private theorem literal_read {D : Type} (blank : D) (bit : Bool → D) (decode : D → Option Bool)
    (t : Tape D) (z : List Bool) (output : whole blank (z.map bit) t)
    (db : decode blank = none) (di : ∀ b, decode (bit b) = some b) (j : ℕ) :
    decode (t.absolute j) = z[j]? := by
  rw [show t.absolute = (Tape.loaded blank (z.map bit)).absolute from output]
  simp only [Tape.absolute, Tape.loaded, sub_zero, List.getElem?_map]
  cases e : z[j]? <;> simp [db,di]

/-- Specialization at the successful frontier-marked configuration. The copied
bits can use any literal alphabet embedding, including the same embedding that
encoded the original input. The frontier width bounds all extra rewind time. -/
theorem release_of_decode {D F Q : Type} (src : I) (fixed : I → ℤ → F) (orig lo hi : I → ℤ)
    (x : Config D Q I) (z : List Bool)
    (decode : D → Option Bool) (blank : Reset.Cell D F) (bit : Bool → Reset.Cell D F)
    (read : ∀ j : ℕ, decode ((x.tape src).absolute j) = z[j]?)
    (start_zero : orig src = 0) (pos_lo : lo src ≤ (x.tape src).pos)
    (pos_hi : (x.tape src).pos ≤ hi src) (zero_lo : lo src ≤ 0) (zero_hi : 0 ≤ hi src) :
    let old := Frontier.config fixed orig lo hi x
    let m := rule src Reset.Cell.leftEnd Reset.Cell.origin (fun v => decode v.val) bit
    let t := ((x.tape src).pos-lo src).toNat+(-(lo src)).toNat+z.length+2
    ∃ w, Trace (advance m) (beginCopy blank old.tape) t w ∧ advance m w = none ∧
      whole blank (z.map bit) (w.tape none) ∧ t ≤ 2*(hi src-lo src).toNat+z.length+2 := by
  let old := Frontier.config fixed orig lo hi x
  let f := Reset.marked (lo src) (hi src) 0 (x.tape src).absolute (fixed src)
  have ready : beginCopy blank old.tape =
      config src old.tape .seek (x.tape src).pos 0 f (fun _ => blank) := by
    unfold beginCopy config
    congr 1
    funext i
    cases i with
    | none =>
      simp only [Tape.loaded,Reset.atHead,Tape.mk.injEq,true_and]
      funext j
      cases j <;> simp
    | some i =>
      by_cases he : i = src
      · subst i
        simp only [ite_true]
        change Frontier.tape (fixed src) (orig src) (lo src) (hi src) (x.tape src) = _
        rw [Frontier.tape_eq_reset, start_zero]
      · simp [he]
  obtain ⟨hist,halt,full⟩ := run src old.tape Reset.Cell.leftEnd Reset.Cell.origin
    (fun v => decode v.val) blank bit z f (lo src) (x.tape src).pos (fun _ => rfl) (fun _ => rfl)
    pos_lo zero_lo read
  exact ⟨_,ready ▸ hist,halt,full,by omega⟩

/-- A whole raw product tape supplies the sequential decoding hypothesis. -/
theorem release {D F Q : Type} (src : I) (fixed : I → ℤ → F) (orig lo hi : I → ℤ)
    (x : Config D Q I) (z : List Bool) (rawBlank : D) (rawBit : Bool → D)
    (decode : D → Option Bool) (blank : Reset.Cell D F) (bit : Bool → Reset.Cell D F)
    (db : decode rawBlank = none) (di : ∀ b, decode (rawBit b) = some b)
    (output : whole rawBlank (z.map rawBit) (x.tape src))
    (start_zero : orig src = 0) (pos_lo : lo src ≤ (x.tape src).pos)
    (pos_hi : (x.tape src).pos ≤ hi src) (zero_lo : lo src ≤ 0) (zero_hi : 0 ≤ hi src) :
    let old := Frontier.config fixed orig lo hi x
    let m := rule src Reset.Cell.leftEnd Reset.Cell.origin (fun v => decode v.val) bit
    let t := ((x.tape src).pos-lo src).toNat+(-(lo src)).toNat+z.length+2
    ∃ w, Trace (advance m) (beginCopy blank old.tape) t w ∧ advance m w = none ∧
      whole blank (z.map bit) (w.tape none) ∧ t ≤ 2*(hi src-lo src).toNat+z.length+2 := by
  exact release_of_decode src fixed orig lo hi x z decode blank bit
    (literal_read _ _ _ _ _ output db di) start_zero pos_lo pos_hi zero_lo zero_hi

/-- Read a tentative data bit through the static guard and work/clock symbol tag. -/
def readWork {D : Type} (decode : D → Option Bool) : (Fence.Symbol D ⊕ Option Bool) → Option Bool
  | .inl v => decode v.1
  | .inr _ => none

/-- On the successful branch of the guarded clocked trial all three encodings
(work/clock, tape fences, and frontier) decode to the literal output bits. -/
theorem release_clocked {D Q : Type} (src : I) (fixed : (I ⊕ Bool) → ℤ → (Fence.Symbol D ⊕ Option Bool))
    (orig left right : (I ⊕ Bool) → ℤ) (lo hi : I → ℤ)
    (x : Config D Q I) (c : ScheduleClock.ClockConfiguration) (z : List Bool)
    (rawBlank : D) (rawBit : Bool → D) (decode : D → Option Bool)
    (blank : Reset.Cell (Fence.Symbol D ⊕ Option Bool) (Fence.Symbol D ⊕ Option Bool))
    (bit : Bool → Reset.Cell (Fence.Symbol D ⊕ Option Bool) (Fence.Symbol D ⊕ Option Bool))
    (db : decode rawBlank = none) (di : ∀ b, decode (rawBit b) = some b)
    (output : whole rawBlank (z.map rawBit) (x.tape src)) (start_zero : orig (.inl src) = 0)
    (left_pos : left (.inl src) ≤ (x.tape src).pos) (right_pos : (x.tape src).pos ≤ right (.inl src))
    (left_zero : left (.inl src) ≤ 0) (right_zero : 0 ≤ right (.inl src)) :
    let old := Frontier.config fixed orig left right (Timed.pack (Fence.marked lo hi false x) c)
    let m := rule (.inl src) Reset.Cell.leftEnd Reset.Cell.origin (fun v => readWork decode v.val) bit
    let t := ((x.tape src).pos-left (.inl src)).toNat+(-left (.inl src)).toNat+z.length+2
    ∃ w, Trace (advance m) (beginCopy blank old.tape) t w ∧ advance m w = none ∧
      whole blank (z.map bit) (w.tape none) ∧
      t ≤ 2*(right (.inl src)-left (.inl src)).toNat+z.length+2 := by
  refine release_of_decode (I := I ⊕ Bool) (Sum.inl src) fixed orig left right (Timed.pack (Fence.marked lo hi false x) c)
    z (readWork decode) blank bit ?_ start_zero left_pos right_pos left_zero right_zero
  intro j
  change decode ((x.tape src).absolute j) = _
  exact literal_read rawBlank rawBit decode (x.tape src) z output db di j

end Uniform.Copy

end NearSquareRoot
end Computability
end OAI

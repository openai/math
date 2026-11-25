import OAI.Computability.NearSquareRoot.ScheduleChunkGuard
import OAI.Computability.NearSquareRoot.ScheduleInterpreterInit
import Batteries.Tactic.OpenPrivate

/-!
# Installing a common radius while preserving the candidate input

The fence sweeps inspect only the external width tape. Every work tape keeps
its own data symbols, including a candidate operand stream already loaded at
the origin. On return the work tapes have exactly the representation expected
by the guarded transition rule.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkGuard

open IntegerMultiplication IntegerMultiplication.TM
open NearSquareRoot.Uniform

open private ops from OAI.Computability.NearSquareRoot.ScheduleInterpreterInit

variable {A J : Type}

private def keepData (a : ℤ → A) (T : Tape (Fence.Symbol A)) : Tape (Fence.Symbol A) :=
  ⟨T.pos, fun j => (a (T.pos+j), (T.view j).2)⟩

private theorem keep_apply (a : ℤ → A) (T : Tape (Fence.Symbol A)) (v : Fence.Symbol A) (d : Move) :
    (keepData a T).apply ((a T.pos,v.2), d) = keepData a (T.apply (v,d)) := by
  unfold keepData Tape.apply
  congr 1
  funext j
  by_cases h : j + d.shift = 0
  · have eq : T.pos + d.shift + j = T.pos := by omega
    simp [h, eq]
  · have eq : T.pos + d.shift + j = T.pos + (j + d.shift) := by omega
    simp [h, eq]

private def preserve (w : J → ℤ → A) (c : Config (Fence.Symbol A) FenceInit.Control (Option J)) :
    Config (Fence.Symbol A) FenceInit.Control (Option J) :=
  ⟨c.pc, fun j => match j with
    | none => c.tape none
    | some i => keepData (w i) (c.tape (some i))⟩

private theorem same_ops (w : J → ℤ → A) (x : Config (Fence.Symbol A) FenceInit.Control (Option J))
    (pc : FenceInit.Control) (src dst : Move) (f : Fence.Symbol A → Fence.Symbol A)
    (hf : ∀ a v, f (a, v.2) = (a, (f v).2)) :
    (⟨pc, fun i => ((preserve w x).tape i).apply
      (ops (fun j => ((preserve w x).tape j).view 0) src dst f i)⟩ :
        Config (Fence.Symbol A) FenceInit.Control (Option J)) =
    preserve w ⟨pc, fun i => (x.tape i).apply (ops (fun j => (x.tape j).view 0) src dst f i)⟩ := by
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  cases j with
  | none => rfl
  | some i =>
    change (keepData _ _).apply (f ((keepData _ _).view 0), dst) = keepData _ ((x.tape _).apply _)
    rw [show (keepData (w i) (x.tape (some i))).view 0 =
      (w i (x.tape (some i)).pos, ((x.tape (some i)).view 0).2) by simp [keepData], hf]
    exact keep_apply _ _ _ _

variable [DecidableEq A] (sep blank : A)

private theorem preserve_step (w : J → ℤ → A) {x y}
    (h : advance (FenceInit.rule sep blank) x = some y) :
    advance (FenceInit.rule sep blank) (preserve w x) = some (preserve w y) := by
  obtain ⟨q, T⟩ := x
  cases q with
  | done => simp [advance, FenceInit.rule] at h
  | scan right =>
    by_cases hs : ((T none).view 0).1 = sep
    · simp only [advance, FenceInit.rule, hs, ↓reduceIte, Option.map_some, Option.some.injEq] at h
      subst y
      change (if ((T none).view 0).1 = sep then some _ else some _).map _ = _
      rw [ite_eq_left hs]
      apply congrArg some
      apply same_ops
      intro a v
      cases right <;> simp [FenceInit.setEnd]
    · simp only [advance, FenceInit.rule, hs, ↓reduceIte, Option.map_some, Option.some.injEq] at h
      subst y
      change (if ((T none).view 0).1 = sep then some _ else some _).map _ = _
      rw [ite_eq_right hs]
      apply congrArg some
      exact same_ops _ _ _ _ _ id (fun _ _ => rfl)
  | rewind right =>
    by_cases hb : ((T none).view 0).1 = blank
    all_goals
      simp only [advance, FenceInit.rule, hb, ↓reduceIte, Option.map_some, Option.some.injEq] at h
      subst y
      change (if ((T none).view 0).1 = blank then some _ else some _).map _ = _
      simp only [hb, ↓reduceIte, Option.map_some, Option.some.injEq]
      exact same_ops _ _ _ _ _ id (fun _ _ => rfl)

private theorem preserve_trace (w : J → ℤ → A) {x y t}
    (run : Trace (advance (FenceInit.rule sep blank)) x t y) :
    Trace (advance (FenceInit.rule sep blank)) (preserve w x) t (preserve w y) := by
  induction run with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (preserve_step sep blank w hs) ih

/-- `none` is the read-only width tape. The other tapes are independently
loaded streams, with every marker initially clear. -/
def beforeInit (s : List A) (words : J → List A) : Config (Fence.Symbol A) FenceInit.Control (Option J) :=
  ⟨.scan true, fun j => Tape.loaded (FenceInit.plain blank)
    (((match j with | none => s | some i => words i)).map FenceInit.plain)⟩

def afterInit (s : List A) (words : J → List A) (R : ℕ) : Config (Fence.Symbol A) FenceInit.Control (Option J) :=
  ⟨.done, fun j => match j with
    | none => Tape.loaded (FenceInit.plain blank) (s.map FenceInit.plain)
    | some i => Fence.markedTape (-(R : ℤ)) R (Tape.loaded blank (words i))⟩

omit [DecidableEq A] in
private theorem loaded_plain (l : List A) (j : ℤ) :
    (Tape.loaded (FenceInit.plain blank) (l.map FenceInit.plain)).view j =
      FenceInit.plain ((Tape.loaded blank l).view j) := by
  cases j <;> simp [Tape.loaded, List.getElem?_map, Option.getD_map]

/-- The sweep takes `4R+6` actual transitions even when each candidate tape
starts with different data and a marker is placed on a nonblank symbol. -/
theorem initialize_loaded (first tail : List A) (words : J → List A)
    (hs : sep ∉ first) (hb : blank ∉ first) (ne : sep ≠ blank) :
    let s := first ++ sep :: tail
    Trace (advance (FenceInit.rule sep blank)) (beforeInit blank s words)
      (4*first.length+6) (afterInit blank s words first.length) := by
  dsimp only
  let s := first ++ sep :: tail
  let w (i : J) := (Tape.loaded blank (words i)).view
  have run := preserve_trace sep blank w (FenceInit.initialize_delimited sep blank first tail hs hb ne)
  convert run using 1
  · change Config.mk _ _ = Config.mk _ _
    congr 1
    funext j
    cases j with
    | none => rfl
    | some i =>
      change Tape.mk _ _ = Tape.mk _ _
      congr 1
      funext z
      change (Tape.loaded (FenceInit.plain blank) ((words i).map FenceInit.plain)).view z =
        (w i (0+z), ((Tape.loaded (FenceInit.plain blank) []).view z).2)
      rw [loaded_plain]
      cases z with
      | ofNat n => simp [w, Tape.loaded, FenceInit.plain]
      | negSucc m => simp [w, Tape.loaded, FenceInit.plain]
  · change Config.mk _ _ = Config.mk _ _
    congr 1
    funext j
    cases j with
    | none => rfl
    | some i =>
      simp only [FenceInit.withInput, keepData, Fence.markedTape, w, Tape.loaded,
        zero_add, FenceInit.fenced, Fence.bits]


variable {Q : Type}

/-- The extra width tape is parked while the guarded program executes. -/
def controller (m : Rule (Fence.Symbol A) Q J) (q₀ : Q) :
    Rule (Fence.Symbol A) (FenceInit.Control ⊕ Q) (Option J) :=
  fun q h => match q with
    | .inl c => match FenceInit.rule sep blank c h with
      | some (c', ops) => some (.inl c', ops)
      | none => some (.inr q₀, fun j => (h j, .stay))
    | .inr v => (m v (fun i => h (some i))).map fun (v',ops) =>
      (.inr v', fun j => match j with | none => (h none, .stay) | some i => ops i)

def installing (x : Config (Fence.Symbol A) FenceInit.Control (Option J)) :
    Config (Fence.Symbol A) (FenceInit.Control ⊕ Q) (Option J) := ⟨.inl x.pc, x.tape⟩

def executing (width : Tape (Fence.Symbol A)) (x : Config (Fence.Symbol A) Q J) :
    Config (Fence.Symbol A) (FenceInit.Control ⊕ Q) (Option J) :=
  ⟨.inr x.pc, fun j => match j with | none => width | some i => x.tape i⟩

private theorem installing_step (m : Rule (Fence.Symbol A) Q J) (q₀ : Q) {x y}
    (h : advance (FenceInit.rule sep blank) x = some y) :
    advance (controller sep blank m q₀) (installing x) = some (installing y) := by
  cases he : FenceInit.rule sep blank x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance, he] at h
  | some op =>
    cases op
    simp only [advance, he, Option.map_some, Option.some.injEq] at h
    subst y
    simp [advance, controller, installing, he]

private theorem install_trace (m : Rule (Fence.Symbol A) Q J) (q₀ : Q) {x y t}
    (h : Trace (advance (FenceInit.rule sep blank)) x t y) :
    Trace (advance (controller sep blank m q₀)) (installing x) t (installing y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (installing_step sep blank m q₀ hs) ih

private theorem execute_step (m : Rule (Fence.Symbol A) Q J) (q₀ : Q) (width : Tape (Fence.Symbol A))
    {x y} (h : advance m x = some y) :
    advance (controller sep blank m q₀) (executing width x) = some (executing width y) := by
  cases he : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance, he] at h
  | some op =>
    cases op
    simp only [advance, he, Option.map_some, Option.some.injEq] at h
    subst y
    simp only [advance, controller, executing, he, Option.map_some, Option.some.injEq, Config.mk.injEq,
      true_and]
    funext j
    cases j with
    | none => exact SM.Action.apply_stay _
    | some j => rfl

theorem execute_trace (m : Rule (Fence.Symbol A) Q J) (q₀ : Q) (width : Tape (Fence.Symbol A))
    {x y t} (h : Trace (advance m) x t y) :
    Trace (advance (controller sep blank m q₀)) (executing width x) t (executing width y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (execute_step sep blank m q₀ width hs) ih

theorem executing_halts (m : Rule (Fence.Symbol A) Q J) (q₀ : Q) (width : Tape (Fence.Symbol A))
    (y : Config (Fence.Symbol A) Q J) (halt : advance m y = none) :
    advance (controller sep blank m q₀) (executing width y) = none := by
  cases h : m y.pc (fun i => (y.tape i).view 0) with
  | none => simp [advance, controller, executing, h]
  | some op => simp [advance, h] at halt

/-- The exact transition switching from completed fence installation to the
real program. All heads and data stay in their final setup positions. -/
theorem installed (m : Rule (Fence.Symbol A) Q J) (q₀ : Q) (s : List A)
    (words : J → List A) (R : ℕ) :
    advance (controller sep blank m q₀) (installing (afterInit blank s words R)) =
      some (executing (Tape.loaded (FenceInit.plain blank) (s.map FenceInit.plain))
        ⟨q₀, fun j => Fence.markedTape (-(R : ℤ)) R (Tape.loaded blank (words j))⟩) := by
  change some (Config.mk _ _) = some (Config.mk _ _)
  rw [Option.some.injEq, Config.mk.injEq]
  refine ⟨rfl, funext fun j => ?_⟩
  cases j <;> apply SM.Action.apply_stay

/-- The full guarded run preceded by a single fence installation and handoff.
The `4R+7` preparation overhead is independent of the number of data tapes. -/
theorem install_then_run (m : Rule (Fence.Symbol A) Q J) (q₀ : Q) (first tail : List A)
    (words : J → List A) (hs : sep ∉ first) (hb : blank ∉ first) (ne : sep ≠ blank)
    {t y} (h : Trace (advance m)
      ⟨q₀, fun j => Fence.markedTape (-(first.length : ℤ)) first.length (Tape.loaded blank (words j))⟩ t y) :
    let s := first ++ sep :: tail
    Trace (advance (controller sep blank m q₀)) (installing (beforeInit blank s words))
      (4*first.length + 7 + t)
      (executing (Tape.loaded (FenceInit.plain blank) (s.map FenceInit.plain)) y) := by
  exact ((install_trace sep blank m q₀ (initialize_loaded sep blank first tail words hs hb ne)).trans
    (.single (installed sep blank m q₀ _ _ _))).trans (execute_trace sep blank m q₀ _ h)

private theorem reflected (m : Rule (Fence.Symbol A) Q J) (q₀ : Q) (width : Tape (Fence.Symbol A))
    {x t z} (h : Trace (advance (controller sep blank m q₀)) (executing width x) t z) :
    ∃ y, Trace (advance m) x t y ∧ z = executing width y := by
  generalize hx : executing width x = init at h
  induction h generalizing x with
  | nil a => exact ⟨x, .nil _, hx.symm⟩
  | @cons a u v n step _ ih =>
    subst a
    cases ho : advance m x with
    | none => rw [executing_halts sep blank m q₀ width x ho] at step; contradiction
    | some y =>
      have he := execute_step sep blank m q₀ width ho
      obtain ⟨z, rest, eq⟩ := ih (Option.some.inj (he.symm.trans step))
      exact ⟨z, .cons ho rest, eq⟩

/-- An absolute space charge for setup and all subsequent guarded steps,
valid with no halting or correctness assumptions about the candidate. -/
theorem installed_visits [Fintype J] (m : Rule A Q J) (q₀ : Q) (first tail : List A)
    (words : J → List A) (hs : sep ∉ first) (hb : blank ∉ first) (ne : sep ≠ blank)
    (budget : ℕ) :
    let s := first ++ sep :: tail
    VisitsAtMost (controller sep blank (Fence.guard m) (false,q₀)) (installing (beforeInit blank s words))
      budget (Fintype.card (Option J) * (8*first.length+15)) := by
  dsimp only
  let s := first ++ sep :: tail
  let R := first.length
  let width := Tape.loaded (FenceInit.plain blank) (s.map FenceInit.plain)
  let x : Config A Q J := ⟨q₀, fun j => Tape.loaded blank (words j)⟩
  let guardRule := controller sep blank (Fence.guard m) (false,q₀)
  have setup : Trace (advance guardRule) (installing (beforeInit blank s words)) (4*R+7)
        (executing width (Fence.marked (left R) (right R) false x)) :=
    (install_trace sep blank (Fence.guard m) (false,q₀)
      (initialize_loaded sep blank first tail words hs hb ne)).trans
        (.single (installed sep blank (Fence.guard m) _ _ _ _))
  have box (u : ℕ) (z) (h : Trace (advance guardRule) (installing (beforeInit blank s words)) u z)
      (j : Option J) : -(4*(R : ℤ)+7) ≤ (z.tape j).pos ∧ (z.tape j).pos ≤ 4*(R : ℤ)+7 := by
    by_cases hu : u ≤ 4*R+7
    · have he := head_excursion h j
      have hz : ((installing (Q := Bool × Q) (beforeInit blank s words)).tape j).pos = 0 := rfl
      rw [hz] at he
      omega
    · obtain ⟨v, pre, rest⟩ := trace_split h (show 4*R+7 ≤ u by omega)
      have eq := trace_endpoint_unique pre setup
      subst v
      obtain ⟨y, inside, rfl⟩ := reflected sep blank (Fence.guard m) (false,q₀) width rest
      have fits : Fence.within (left R) (right R) x := by
        intro i
        change -(R : ℤ) ≤ 0 ∧ 0 ≤ (R : ℤ)
        omega
      obtain ⟨v, tag, hv, rfl⟩ := Fence.trace_within m _ _ fits inside
      cases j with
      | none =>
        change -(4*(R : ℤ)+7) ≤ 0 ∧ 0 ≤ 4*(R : ℤ)+7
        omega
      | some j =>
        have hz := hv j
        change -(R : ℤ) ≤ _ ∧ _ ≤ (R : ℤ) at hz
        change -(4*(R : ℤ)+7) ≤ (v.tape j).pos ∧ (v.tape j).pos ≤ 4*(R : ℤ)+7
        omega
  have cover := visitsAtMost_of_common_fence (m := guardRule) (steps := budget)
    (init := installing (beforeInit blank s words)) (-(4*(R : ℤ)+7)) (4*(R : ℤ)+7)
    (fun u _ z h j => box u z h j)
  convert cover using 2
  dsimp only [R]
  omega

section Release
variable {I : Type} [DecidableEq I] [Fintype I]

/-- Specialization from raw loaded stacks through guard creation, the released
physical computation, and the output tape. The width tape already contains a
word of the selected radius; the two endpoint bits begin clear everywhere. -/
theorem install_segment (delimiter : Option A) (first tail : List (Option A))
    (hs : delimiter ∉ first) (hb : none ∉ first) (ne : delimiter ≠ none)
    {n H : ℕ} {i k : I} {s : List A} {q : Q} {g : SM.Rule A Q I} {x}
    (call : Schoolbook.Segment g (SM.origin q i s) n x H) (stop : SM.advance g x = none)
    (room : 2*H+2 ≤ first.length) :
    let width := first ++ delimiter :: tail
    let words (j : Option I) := if j = some i then s.map some else []
    let program := controller delimiter none (rule k g) (false, some (.inl q))
    let init := installing (beforeInit none width words)
    let t := 4*first.length+7+(2*n+1+(x.stack k).length)
    ∃ z, Trace (advance program) init t z ∧ advance program z = none ∧
      whole none ((x.stack k).map some) (data (z.tape (some none))) ∧
      VisitsAtMost program init t (Fintype.card (Option (Option I)) * (8*first.length+15)) := by
  dsimp only
  let words (j : Option I) := if j = some i then s.map some else []
  let width := first ++ delimiter :: tail
  let widthTape := Tape.loaded (FenceInit.plain none) (width.map FenceInit.plain)
  obtain ⟨y, ok, halt, _, out⟩ := success (k := k) call stop room
  have e (j : Option I) : (origin q i s).tape j = Tape.loaded none (words j) := by
    by_cases hj : j = some i <;> simp [origin, words, hj]
  have init : initial first.length q i s =
      ⟨(false,some (.inl q)), fun j => Fence.markedTape (-(first.length : ℤ)) first.length
        (Tape.loaded none (words j))⟩ := by
    change Config.mk _ _ = Config.mk _ _
    congr 1
    funext j
    exact congrArg (Fence.markedTape _ _) (e j)
  rw [init] at ok
  exact ⟨executing widthTape y,
    install_then_run delimiter none (rule k g) _ first tail words hs hb ne ok,
    executing_halts delimiter none (rule k g) _ widthTape y halt, out,
    installed_visits delimiter none (SM.complete k g) _ first tail words hs hb ne _⟩

end Release
end ChunkGuard

end NearSquareRoot
end Computability
end OAI

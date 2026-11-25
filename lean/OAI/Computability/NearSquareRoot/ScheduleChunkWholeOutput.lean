import OAI.Computability.NearSquareRoot.ScheduleChunkWhole

/-!
# A clean output tape for the initialized chunk machine

An additional head follows the tentative output head and receives its data
writes with the fence marks cleared. Both heads start at the origin on blank
tapes. This is one extra simultaneous tape operation per physical transition.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkWhole.Mirror

open IntegerMultiplication IntegerMultiplication.TM

variable {A Q I : Type}

def tape (f : A → A) (T : Tape A) : Tape A := ⟨T.pos, fun i => f (T.view i)⟩

theorem apply_tape (f : A → A) (T : Tape A) (a : A × Move) :
    (tape f T).apply (f a.1, a.2) = tape f (T.apply a) := by
  simp only [tape, Tape.apply, Tape.mk.injEq, true_and]
  funext i
  split <;> simp_all

def pack (f : A → A) (out : I) (x : Config A Q I) : Config A Q (Option I) :=
  ⟨x.pc, fun j => match j with | none => tape f (x.tape out) | some i => x.tape i⟩

def rule (f : A → A) (out : I) (m : Rule A Q I) : Rule A Q (Option I) :=
  fun q reads => (m q (fun i => reads (some i))).map fun (v, ops) =>
    (v, fun j => match j with | none => (f (ops out).1, (ops out).2) | some i => ops i)

theorem advance_pack (f : A → A) (out : I) (m : Rule A Q I) (x : Config A Q I) :
    advance (rule f out m) (pack f out x) = (advance m x).map (pack f out) := by
  cases e : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance, pack, rule, e]
  | some op =>
    rcases op with ⟨y,acts⟩
    simp only [advance, rule, pack, e, Option.map_some, Option.some.injEq, Config.mk.injEq, true_and]
    funext j
    cases j with
    | none => exact apply_tape _ _ _
    | some i => rfl

theorem run (f : A → A) (out : I) (m : Rule A Q I) {x y t} (h : Trace (advance m) x t y) :
    Trace (advance (rule f out m)) (pack f out x) t (pack f out y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (by simp [advance_pack,h]) ih

theorem reflect (f : A → A) (out : I) (m : Rule A Q I) {x t z}
    (h : Trace (advance (rule f out m)) (pack f out x) t z) :
    ∃ y, Trace (advance m) x t y ∧ z = pack f out y := by
  generalize he : pack f out x = start at h
  induction h generalizing x with
  | nil y => exact ⟨x,.nil _,he.symm⟩
  | @cons a u v n step _ ih =>
    subst a
    rw [advance_pack] at step
    cases hx : advance m x with
    | none => simp [hx] at step
    | some w =>
      obtain ⟨y,rest,eq⟩ := ih (by simpa [hx] using step)
      exact ⟨y,.cons hx rest,eq⟩

/-- The extra tape visits a subset of the positions visited by the old output
tape, also for a prefix ending in a failed candidate. -/
theorem visited (f : A → A) (out : I) (m : Rule A Q I) (x : Config A Q I) (t N : ℕ)
    (h : VisitsAtMost m x t N) : VisitsAtMost (rule f out m) (pack f out x) t (2*N) := by
  classical
  obtain ⟨cells,hc,cv⟩ := h
  let keep (p : I × ℤ) : Option I × ℤ := (some p.1,p.2)
  let dup (p : I × ℤ) : Option I × ℤ := (none,p.2)
  refine ⟨cells.image keep ∪ cells.image dup, (Finset.card_union_le ..).trans ?_, ?_⟩
  · have h₁ : (cells.image keep).card ≤ N := Finset.card_image_le.trans hc
    have h₂ : (cells.image dup).card ≤ N := Finset.card_image_le.trans hc
    omega
  · intro u hu z hz j
    obtain ⟨y,hy,rfl⟩ := reflect f out m hz
    cases j with
    | some i => exact Finset.mem_union_left _ (Finset.mem_image_of_mem keep (cv u hu y hy i))
    | none => exact Finset.mem_union_right _ (Finset.mem_image_of_mem dup (cv u hu y hy out))

variable {B : Type}

/-- Mapping the data onto the fresh tape preserves the blank background at
all offsets, including negative positions and after the final output symbol. -/
theorem whole (plain : B → Uniform.Fence.Symbol B) (blank : B) (word : List B)
    (T : Tape (Uniform.Fence.Symbol B)) (h : TM.whole blank word (ChunkGuard.data T)) :
    TM.whole (plain blank) (word.map plain) (tape (fun x => plain x.1) T) := by
  funext j
  have e := congrFun h j
  change (T.view (j-T.pos)).1 = (Tape.loaded blank word).absolute j at e
  change plain (T.view (j-T.pos)).1 = (Tape.loaded (plain blank) (word.map plain)).absolute j
  rw [e]
  simp only [Tape.absolute, Tape.loaded, sub_zero]
  cases j <;> simp [List.getElem?_map, Option.getD_map]

end ChunkWhole.Mirror

namespace ChunkWhole

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkControl ChunkLoop ChunkTask

noncomputable section

private abbrev plain (d : Driver) (c : Cmd) := Uniform.FenceInit.plain (A := Symbols d c)

def outputBit (d : Driver) (c : Cmd) (b : Bool) :=
  plain d c (some (.inl (.bit b)))

abbrev cleanRule (d : Driver) (c : Cmd) :=
  Mirror.rule (fun a => plain d c a.1) (some none) (rule d c)

def cleanInitial (d : Driver) (c : Cmd) (R : ℕ) (s : List Ltr) :=
  Mirror.pack (fun a => plain d c a.1) (some none) (initial d c R s)

theorem clean_initial_output (d : Driver) (c : Cmd) (R : ℕ) (s : List Ltr) :
    ((cleanInitial d c R s).tape none) = TM.Tape.loaded (plain d c none) [] := by
  change TM.Tape.mk _ _ = TM.Tape.mk _ _
  congr 1
  funext j
  cases j <;> rfl

/-- The final `TM.whole` speaks about all tracks of the complete absolute
tape. Its only nonblanks are the `2*n` MSF product bits, including any leading
zeros. All inputs to the chunk routine and its radius buffer are loaded in
the same alphabet with cleared marker bits. -/
theorem clean_output_fixed_split :
    ∃ (d : Driver) (C : ℕ),
      (∀ K : ℕ, ∃ W : ℕ, ∀ c : Cmd, Nat.card (Prog.Ix (Prog.sites [] c)) ≤ K →
        ∀ n budget (s : List Ltr), VisitsAtMost (cleanRule d c)
          (cleanInitial d c (radius C n) s) budget (W*(n+1))) ∧
      ∀ (c : Cmd) (m : Operands → Word) (T : ℕ → ℕ) (L : ℕ),
        Isolated c m T (fun u => L*(u+1)) →
        (∀ q : EqualWords, (m q.val).length = 2*q.val.1.length) →
        (∀ q : EqualWords, bitValue (m q.val) = bitValue q.val.1 * bitValue q.val.2) →
        ∃ k : ℕ, ∀ p : Input, p.k = k → 2*2^k ≤ p.n →
          ∃ t ≤ (14*C+303)*((p.count+1)*(p.n+T p.u+1)), ∃ z,
            Trace (TM.advance (cleanRule d c))
              (cleanInitial d c (radius C p.n) (ChunkPhases.input p)) t z ∧
            TM.advance (cleanRule d c) z = none ∧
            TM.whole (Uniform.FenceInit.plain (none : Symbols d c))
              ((answer m p).map (outputBit d c)) (z.tape none) ∧
            (answer m p).length = 2*p.n ∧ bitValue (answer m p) = bitValue p.x * bitValue p.y := by
  obtain ⟨d,C,space,done⟩ := installed_raw_fixed_split
  refine ⟨d,C,?_,?_⟩
  · intro K
    obtain ⟨W,space⟩ := space K
    refine ⟨2*W, fun c hc n budget s => ?_⟩
    rw [Nat.mul_assoc]
    exact Mirror.visited _ _ _ _ _ _ (space c hc n budget s)
  · intro c m T L callee width correct
    obtain ⟨k, hk⟩ := done c m T L callee width correct
    refine ⟨k, ?_⟩
    intro p he hn
    obtain ⟨t, ht, z, run, halt, answerOK, len, val⟩ := hk p he hn
    have h := Mirror.whole (plain d c) none _ _ answerOK
    refine ⟨t, ht, _, Mirror.run _ _ _ run, ?_, ?_, len, val⟩
    · rw [cleanRule, Mirror.advance_pack, halt]
      rfl
    · unfold outputBit
      simpa only [List.map_map,Function.comp_def,plain,Mirror.pack] using h

end
end ChunkWhole

end NearSquareRoot
end Computability
end OAI

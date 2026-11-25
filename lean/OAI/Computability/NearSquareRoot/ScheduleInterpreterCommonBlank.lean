import OAI.Computability.NearSquareRoot.VisitedCells

/-!
# A common blank for independently coded tape banks

A distinguished symbol `none` represents the local blank on each bank. Reading
and writing use the tape index in finite control. This coding preserves every
head position and every halting time, and sends loaded or completed tapes to
the literal representation with the same single blank on every tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.CommonBlank

open IntegerMultiplication TM

variable {A Q I : Type} [DecidableEq A]

def encode (b a : A) : Option A := if a = b then none else some a

@[simp] theorem encode_getD (b a : A) : (encode b a).getD b = a := by
  by_cases h : a = b <;> simp [encode,h]

def tape (b : A) (x : Tape A) : Tape (Option A) := ⟨x.pos, encode b ∘ x.view⟩

def config (b : I → A) (x : Config A Q I) : Config (Option A) Q I :=
  ⟨x.pc,fun i => tape (b i) (x.tape i)⟩

def rule (b : I → A) (m : Rule A Q I) : Rule (Option A) Q I := fun q h =>
  (m q (fun i => (h i).getD (b i))).map fun (q',o) =>
    (q', fun i => (encode (b i) (o i).1, (o i).2))

private theorem tape_apply (b : A) (t : Tape A) (o : A × Move) :
    (tape b t).apply (encode b o.1,o.2) = tape b (t.apply o) := by
  unfold Tape.apply tape
  congr 1
  funext i
  simp only [Function.comp_apply]
  split <;> rfl

theorem advance_config (b : I → A) (m : Rule A Q I) (x : Config A Q I) :
    advance (rule b m) (config b x) = (advance m x).map (config b) := by
  cases h : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance, config, tape, rule,h]
  | some z =>
    obtain ⟨q,o⟩ := z
    simp [advance, config, tape, rule,h]
    funext i
    exact tape_apply _ _ _

theorem trace (b : I → A) (m : Rule A Q I) {x y : Config A Q I} {k : ℕ}
    (h : Trace (advance m) x k y) : Trace (advance (rule b m)) (config b x) k (config b y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by simp [advance_config, hs]) ih

theorem reflect (b : I → A) (m : Rule A Q I) {x : Config A Q I} {w : Config (Option A) Q I} {k : ℕ}
    (h : Trace (advance (rule b m)) (config b x) k w) :
    ∃ y, Trace (advance m) x k y ∧ w = config b y := by
  generalize he : config b x = start at h
  induction h generalizing x with
  | nil => exact ⟨_, .nil _,he.symm⟩
  | @cons start u w n hs _ ih =>
    subst start
    rw [advance_config] at hs
    cases step : advance m x with
    | none => simp [step] at hs
    | some y =>
      obtain ⟨z,tr,hw⟩ := ih (show config b y = u by simpa [step] using hs)
      exact ⟨z,.cons step tr,hw⟩

theorem visits_iff (b : I → A) (m : Rule A Q I) (x : Config A Q I) (k s : ℕ) :
    VisitsAtMost (rule b m) (config b x) k s ↔ VisitsAtMost m x k s := by
  constructor
  · rintro ⟨cells,hs,cover⟩
    exact ⟨cells,hs,fun j hj z h i => cover j hj _ (trace b m h) i⟩
  · rintro ⟨cells,hs,cover⟩
    refine ⟨cells,hs,fun j hj w h i => ?_⟩
    obtain ⟨z,hz,hw⟩ := reflect b m h
    subst w
    exact cover j hj z hz i

theorem loaded (b : A) (s : List A) :
    tape b (Tape.loaded b s) = Tape.loaded none (s.map (encode b)) := by
  simp only [tape,Tape.loaded,Tape.mk.injEq,true_and]
  funext i
  cases i with
  | negSucc => simp [encode]
  | ofNat n => cases h : s[n]? <;> simp [h,encode]

theorem whole_tape (b : A) (s : List A) (x : Tape A) (h : whole b s x) :
    whole none (s.map (encode b)) (tape b x) := by
  rw [whole, ← loaded]
  funext i
  exact congrArg (encode b) (congrFun h i)

end Uniform.CommonBlank

end NearSquareRoot
end Computability
end OAI

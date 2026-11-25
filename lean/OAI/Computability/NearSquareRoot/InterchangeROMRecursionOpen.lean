import OAI.Computability.NearSquareRoot.InterchangeROMRecursion
import OAI.Computability.NearSquareRoot.InterchangeCenterRetype

/-! # Unscaled stage clocks for a fixed recursive parent -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRecursion
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  NearSquareRoot.InterchangeSpace NearSquareRoot.Space NearSquareRoot.InterchangeROMFrame

variable {X : Type} {job : Job X} {parent cmd : Cmd} {sm fu : List X}
    {input output : Tree} {work park returns : ℕ}

/-- A stage may be assembled before its local polynomial has been absorbed
in the record width. Its ambient environment contains the concrete parent. -/
def At (parent cmd : Cmd) (job : Job X) (sm fu : List X) (input output : Tree)
    (work park returns : ℕ) : Prop :=
  ∀ env (time data depth : X → ℕ),
    (∀ y ∈ sm ++ fu, ∀ d base, DeckCap base d →
      BoundedFits (parent::env) parent (pile 0 (job.issue y) d) (pile 0 (job.reply y) d)
        (time y) (base+data y) (depth y)) → ∀ d base, DeckCap base d →
      BoundedFits (parent::env) cmd (pile 0 input d) (pile 0 output d)
        (work + ((sm ++ fu).map time).sum)
        (base + max (work + childPeak data sm) (park + childPeak data fu))
        (max (work + childPeak depth sm) (returns + childPeak depth fu))

theorem At.ofCenterRun (h : CenterBody.CenterRun job sm fu cmd input output work park returns) :
    At parent cmd job sm fu input output work park returns := h parent

theorem At.mono (h : At parent cmd job sm fu input output work park returns) {w reserve d : ℕ}
    (hw : work ≤ w) (hp : park ≤ reserve) (hd : returns ≤ d) :
    At parent cmd job sm fu input output w reserve d := by
  intro env t a r call deck base live
  exact (h env t a r call deck base live).mono (Nat.add_le_add_right hw _)
    (Nat.add_le_add_left (max_le_max (Nat.add_le_add_right hw _) (Nat.add_le_add_right hp _)) _)
    (max_le_max (Nat.add_le_add_right hw _) (Nat.add_le_add_right hd _))

/-- Forgetting a subtype witness preserves the concrete command, both exact
call lists, each occurrence's time, and each class's peak. -/
theorem At.restrict_calls (run : At parent cmd job sm fu input output work park returns)
    (valid : X → Prop) (s f : List (Subtype valid))
    (hs : s.map Subtype.val = sm) (hf : f.map Subtype.val = fu) :
    At parent cmd (⟨fun z : Subtype valid => job.issue z.val, fun z => job.reply z.val⟩ : Job _)
      s f input output work park returns := by
  classical
  intro env time data depth children deck base hcap
  let extend (g : Subtype valid → ℕ) (x : X) := if hx : valid x then g ⟨x,hx⟩ else 0
  have value (g : Subtype valid → ℕ) (z : Subtype valid) : extend g z.val = g z := by
    simp [extend,z.property]
  have peak (g : Subtype valid → ℕ) (zs : List (Subtype valid)) :
      childPeak (extend g) (zs.map Subtype.val) = childPeak g zs := by
    induction zs with
    | nil => rfl
    | cons z zs ih =>
      change max (extend g z.val) (childPeak (extend g) (zs.map Subtype.val)) = _
      rw [value,ih]
      rfl
  have erase : (s ++ f).map Subtype.val = sm ++ fu := by
    rw [List.map_append,hs,hf]
  have child (y : X) (hy : y ∈ sm ++ fu) (d : Deck) (b : ℕ) (hd : DeckCap b d) :
      BoundedFits (parent::env) parent (pile 0 (job.issue y) d) (pile 0 (job.reply y) d)
        (extend time y) (b+extend data y) (extend depth y) := by
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (erase.symm ▸ hy)
    simpa only [value] using children z hz d b hd
  have total : ((sm ++ fu).map (extend time)).sum = ((s ++ f).map time).sum := by
    rw [← erase, List.map_map]
    simp only [Function.comp_def,value]
  have actual := run env (extend time) (extend data) (extend depth) child deck base hcap
  rw [total,← hs,← hf] at actual
  simpa only [peak] using actual


/-- Attach the actual prelude before a selected stage, prior to the eventual
choice of thickness degree. The full-volume park and pending returns are
preserved because the front end has already returned before any child call. -/
theorem At.node {prelude stage : Cmd} {b n : ℕ} {sel : Bool} {middle : Tree} {t : ℕ}
    (selected : At (node prelude stage b n) (bif sel then stage else .pass) job sm fu middle output work park returns)
    (front : ∀ env d, Fits (node prelude stage b n::env) prelude
      (pile 0 (.fork (literal b n) input) d) (pile 0 (.fork (.atom sel) middle) d) t) :
    At (node prelude stage b n) (node prelude stage b n) job sm fu input output
      (5*(literal b n).count + t + input.count + middle.count + work + 20) park returns := by
  intro env time data depth invoke d base hd
  apply (node_run b n prelude stage _ d base hd input middle output sel _ _ _ _ (front env d)
    (selected env time data depth invoke d base hd)).mono <;> omega

end InterchangeROMRecursion

end NearSquareRoot
end Computability
end OAI

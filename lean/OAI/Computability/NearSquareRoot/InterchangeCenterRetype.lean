import OAI.Computability.NearSquareRoot.InterchangeCenterBody

/-!
# Restricting the center program to admissible requests

The same center command runs against the subtype oracle when its small and
full-volume requests all satisfy the admissibility predicate.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  IntegerMultiplication.Strip NearSquareRoot.Space

namespace CenterBody

variable {I X : Type} {r : Regime I} {n l : I → ℕ} {job : Job X}
    {small full : I → List X} {park : I → ℕ} {p q : I → Tree}

/-- The resource bounds for one execution of the center command on a fixed
input. Both kinds of child may choose time, data and return-depth bounds
independently. -/
abbrev CenterRun (job : Job X) (sm fu : List X) (cmd : Cmd) (input output : Tree)
    (work park returns : ℕ) : Prop :=
  ∀ (parent : Cmd) (env : Env) (time data depth : X → ℕ),
    (∀ y ∈ sm ++ fu, ∀ d b, DeckCap b d →
      BoundedFits (parent::env) parent (pile 0 (job.issue y) d) (pile 0 (job.reply y) d)
        (time y) (b+data y) (depth y)) → ∀ d base, DeckCap base d →
      BoundedFits (parent::env) cmd (pile 0 input d) (pile 0 output d)
        (work + ((sm ++ fu).map time).sum)
        (base + max (work + childPeak data sm) (park + childPeak data fu))
        (max (work + childPeak depth sm) (returns + childPeak depth fu))

/-- A certified subtype preserves the command and its concrete numerical
allowances before the local degree and multiplicative constant are hidden. -/
theorem CenterRun.restrict_calls {sm fu : List X} {cmd : Cmd} {input output : Tree}
    {work reserve returns : ℕ} (run : CenterRun job sm fu cmd input output work reserve returns)
    (valid : X → Prop) (s f : List (Subtype valid))
    (hs : s.map Subtype.val = sm) (hf : f.map Subtype.val = fu) :
    CenterRun (⟨fun z : Subtype valid => job.issue z.val, fun z => job.reply z.val⟩ : Job _)
      s f cmd input output work reserve returns := by
  classical
  intro parent env time data depth children deck base hcap
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
  have actual := run parent env (extend time) (extend data) (extend depth) child deck base hcap
  rw [total,← hs,← hf] at actual
  simpa only [peak] using actual

/-- Retype the recursive calls with exact erasures of both ledgers. The
original time coefficients, parked volumes, and pending returns are preserved. -/
theorem restrict_calls (h : CenterBody r n l job small full park p q)
    (valid : X → Prop) (s f : I → List (Subtype valid))
    (hs : ∀ i, (s i).map Subtype.val = small i)
    (hf : ∀ i, (f i).map Subtype.val = full i) :
    CenterBody r n l
      (⟨fun z : Subtype valid => job.issue z.val, fun z => job.reply z.val⟩ : Job _)
      s f park p q := by
  obtain ⟨k,K,cmd,run⟩ := h.build
  refine ⟨k,K,cmd,?_⟩
  intro i
  exact CenterRun.restrict_calls (run i) valid (s i) (f i) (hs i) (hf i)

/-- Construct the two admissible ledgers in their original order. -/
theorem restrict_valid_calls (h : CenterBody r n l job small full park p q)
    (valid : X → Prop) (closed : ∀ i y, y ∈ small i ++ full i → valid y) :
    ∃ s f : I → List (Subtype valid), (∀ i, (s i).map Subtype.val = small i) ∧
      (∀ i, (f i).map Subtype.val = full i) ∧
      CenterBody r n l
        (⟨fun z : Subtype valid => job.issue z.val, fun z => job.reply z.val⟩ : Job _)
        s f park p q := by
  let s (i : I) := (small i).attachWith valid fun y hy => closed i y (List.mem_append_left _ hy)
  let f (i : I) := (full i).attachWith valid fun y hy => closed i y (List.mem_append_right _ hy)
  have hs (i : I) : (s i).map Subtype.val = small i := by simp [s]
  have hf (i : I) : (f i).map Subtype.val = full i := by simp [f]
  exact ⟨s,f,hs,hf,h.restrict_calls valid s f hs hf⟩

end CenterBody

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI

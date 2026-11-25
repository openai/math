import OAI.ThreeFlat.Diagonal.PhysicalStageProgram
import OAI.ThreeFlat.Diagonal.BlockDegreeSchedule

namespace OAI
/-! # A repeatable physical program from fixed shrink and refresh tables -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Expander LinearAlgebra.SpectralBooks
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

/-- The literal scalar table and degree operands of one physical pass. The
refresh table retains its actual graph and dimension in its dependent type. -/
inductive StaticMotif (F : Type) [Field F] : Type 1 where
  | shrink (s D : ℕ) (T : ShrinkMotif.Table F)
  | refresh (s h pad : ℕ) (c : Fin (2^s)→Fin (2^s)→ℕ) (C : ℝ)
      (T : RefreshMotif.Table F c (1+h+pad) C)

/-- Scheduler-side support for every literal stage of a chronological program. -/
def Program.SupportedBy {s : ℕ} (P : Program F s) (allow : StaticMotif F→Prop) : Prop :=
  match P with
  | .done _ => True
  | .shrink s t T _ tail => allow (.shrink s (2^t) T) ∧ Program.SupportedBy tail allow
  | .refresh s _ h pad c _ C T _ _ _ _ _ _ _ tail =>
      allow (.refresh s h pad c C T) ∧ Program.SupportedBy tail allow

theorem Program.supported_cast {s t : ℕ} (e : s=t) (P : Program F s) (allow : StaticMotif F→Prop)
    (supported : P.SupportedBy allow) : (e ▸ P : Program F t).SupportedBy allow := by
  cases e
  exact supported

/-- A single finite grid and the dyadic graph data shared by all repetitions. -/
structure Block (F : Type) [Field F] where
  levels : ℕ
  positive : 0 < levels
  exponent : ℕ → ℕ
  shrink : ShrinkMotif.Table F
  small : ∀ i, ((2^(2*(2^exponent i)+1)*(2^exponent i)*(2^exponent i):ℕ):ℝ) /
    2^exponent (i+1) ≤ 1/1024
  h : ℕ
  pad : ℕ
  γ : ℝ
  graph : Fin (2^exponent levels) → Fin (2^exponent levels) → ℕ
  hh : 0<h
  hm : 2≤2^exponent levels
  symmetric : ∀ i j, graph i j=graph j i
  degree : ∀ i, ∑ j, graph i j=h
  loopless : ∀ i, graph i i=0
  connected : Bound (transition graph h) ℝ γ
  restore : 1+h+pad=2^exponent 0
  refresh : RefreshMotif.Table F graph (1+h+pad) (RefreshMotif.leading h (1+h+pad) γ+1)
  contracts : ((1+h+pad:ℕ) + 2*(RefreshMotif.leading h (1+h+pad) γ+1):ℝ) *
    (126/127:ℝ)^levels ≤ 1/4

namespace Block

variable (B : Block F)

/-- Compile the contiguous range of shrink levels immediately before its continuation. -/
def shrinkPrefix : (n i : ℕ) → Program F (B.exponent (i+n)) → Program F (B.exponent i)
  | 0, _, tail => tail
  | n+1, i, tail =>
      let e : B.exponent (i+(n+1)) = B.exponent ((i+1)+n) := congrArg B.exponent (by omega)
      .shrink _ _ B.shrink (B.small i) (shrinkPrefix n (i+1) (e ▸ tail))

def «prefix» (tail : Program F (B.exponent 0)) : Program F (B.exponent 0) :=
  let e : B.exponent B.levels = B.exponent (0+B.levels) :=
    congrArg B.exponent (Nat.zero_add B.levels).symm
  let last : Program F (B.exponent B.levels) :=
    .refresh _ _ B.h B.pad B.graph B.γ _ B.refresh B.hm B.hh B.symmetric B.degree B.loopless
      B.connected B.restore tail
  B.shrinkPrefix B.levels 0 (e ▸ last)

/-- A list of real pass programs with one refresh and `levels` shrink updates per block. -/
def «repeat» : ℕ → Program F (B.exponent 0)
  | 0 => .done _
  | n+1 => B.prefix («repeat» n)

/-- Exactly the fixed scalar grids that the public ROM can select. -/
def publicTemplate (q : StaticMotif F) : Prop :=
  (∃ i : Fin B.levels,q=.shrink (B.exponent i.val) (2^B.exponent (i.val+1)) B.shrink) ∨
    q=.refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh

theorem public_shrink {s D : ℕ} {T : ShrinkMotif.Table F} (ok : B.publicTemplate (.shrink s D T)) :
    ∃ i : Fin B.levels,s=B.exponent i.val ∧ D=2^B.exponent (i.val+1) ∧ T=B.shrink := by
  rcases ok with ⟨i,eq⟩|eq
  · exact ⟨i,StaticMotif.shrink.inj eq⟩
  · cases eq

theorem public_refresh {s h pad : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C : ℝ}
    {T : RefreshMotif.Table F c (1+h+pad) C} (ok : B.publicTemplate (.refresh s h pad c C T)) :
    StaticMotif.refresh s h pad c C T=.refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh := by
  rcases ok with ⟨i,eq⟩|eq
  · cases eq
  · exact eq

private theorem shrinkPrefix_supported (n i : ℕ) (P : Program F (B.exponent (i+n))) (limit : i+n≤B.levels)
    (allowed : P.SupportedBy B.publicTemplate) : (B.shrinkPrefix n i P).SupportedBy B.publicTemplate := by
  induction n generalizing i with
  | zero=>exact allowed
  | succ n ih=>
    simp only [shrinkPrefix,Program.SupportedBy]
    constructor
    · exact Or.inl ⟨⟨i,by omega⟩,rfl⟩
    · apply ih (i+1) _ (by omega)
      exact Program.supported_cast _ P B.publicTemplate allowed

theorem repeat_supported (n : ℕ) : (B.repeat n).SupportedBy B.publicTemplate := by
  induction n with
  | zero=>trivial
  | succ n ih=>
    unfold «repeat» «prefix»
    apply B.shrinkPrefix_supported B.levels 0 _ (by omega)
    apply Program.supported_cast
    exact ⟨Or.inr rfl,ih⟩

end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI

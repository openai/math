import OAI.Computability.VPVNP.CompressorShrinkABSliceOperands
import OAI.Computability.VPVNP.CompressorScheduledSliceRates
import OAI.Computability.VPVNP.CompressorSourceObservableFrame

/-!
# Replay of an admitted AB trace with another clock and header snapshot

The flattened parameters depend only on the eight planner head values.
Thus the accepted deterministic trace is unique even when the graph
builder and the online packet maker use different source clocks or
equivalent saved header memories.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkABSliceRecipe

open BurstRAM PhaseRecipe BlockPlanner
open scoped Fin.CommRing

variable {w m n rows first : ℕ} {t p : Fin 5 → Word w}
variable {pub : Fin 5 → Word w} {state : Word w} {ref mem : Memory w} (I : Inputs)
local notation "eqWord" => fun e : Expr => Expr.eval pub state ref e = Expr.eval pub state mem e

private theorem args_eq {k : ℕ} (par : Fin k → Affine) (cursor : ℕ)
    (parEq : ∀ j, eqWord (par j).1 ∧ eqWord (par j).2) (j : Fin (FlatRows.Params k)) :
    eqWord (arguments par cursor j) := by
  let a := finProdFinEquiv.symm j
  have all (i : Fin (k+1)) : let e := Fin.snoc (α := fun _ => Affine) par (constant cursor) i
      eqWord e.1 ∧ eqWord e.2 := by
    cases i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact ⟨rfl,rfl⟩
    | cast j => simpa only [Fin.snoc_castSucc] using parEq j
  let e := Fin.snoc (α := fun _ => Affine) par (constant cursor) a.1
  change eqWord (![e.1,e.2,.lit 0] a.2)
  have pair := all a.1
  generalize a.2 = c
  fin_cases c <;> first | exact pair.1 | exact pair.2 | rfl

theorem params_eq (d : Describes I pub state ref t p rows first) (e : Describes I pub state mem t p rows first)
    (j : Stage m n) (i : Fin (stage I j).worker.params) : eqWord ((stage I j).params i) := by
  have bank (off : ℕ) : eqWord (bankField I m n off).1 ∧ eqWord (bankField I m n off).2 :=
    ⟨congrArg (·+(off : Word w)) (d.start.trans e.start.symm),rfl⟩
  cases j with
  | clear k => exact args_eq (clearParams I m n) k.val (fun _ => bank 0) i
  | pair k =>
    apply args_eq (pairParams I m n) k.val _ i
    intro u; fin_cases u
    exacts [⟨rfl,rfl⟩,⟨d.oldStarts.trans e.oldStarts.symm,d.oldStride.trans e.oldStride.symm⟩,
      ⟨d.oldWidths.trans e.oldWidths.symm,d.oldStride.trans e.oldStride.symm⟩,
      ⟨d.newStarts.trans e.newStarts.symm,d.newStride.trans e.newStride.symm⟩,
      ⟨d.newWidths.trans e.newWidths.symm,d.newStride.trans e.newStride.symm⟩,bank (m+n)]
  | refs k =>
    apply args_eq (refParams I m n) k.val _ i
    intro u; fin_cases u
    exacts [⟨rfl,rfl⟩,⟨rfl,rfl⟩,bank (m+n),bank 0,bank (m+n+3*(m*n)),bank m,bank (m+n+4*(m*n))]

open private useFixedFuel abTotal from OAI.Computability.VPVNP.CompressorScheduledSliceRates

private theorem short_walk (d : Describes I pub state ref t p rows first) (e : Describes I pub state mem t p rows first)
    {js : List (Stage m n)} {s : Memory w} {rs : List (Report w)} {cap : ℕ}
    (walk : SourceWalk (Source I pub state ref rows cap) js s rs) : SourceWalk
      (fun j cur xs => Source I pub state mem rows (ScheduledRates.abFuel j) j cur xs) js s rs := by
  induction walk with
  | done => exact .done _
  | @next j _ cur xs _ h _ ih =>
    let P := stage I j
    change runSegment (P.worker.table.instantiate w (fun k => (P.params k).eval pub state ref)).program cap
      (some 0) cur (List.replicate rows []) = some xs at h
    rw [show (fun k => (P.params k).eval pub state ref) = (fun k => (P.params k).eval pub state mem) from
      funext (params_eq I d e j)] at h
    exact .next (useFixedFuel _ (abTotal I j _) h) ih

/-- Accepted native AB schedules with the same installed heads give the
same report list and memory endpoint, independently of the source cap. -/
theorem walk_unique (d : Describes I pub state ref t p rows first) (e : Describes I pub state mem t p rows first)
    {js : List (Stage m n)} {s : Memory w} {xs ys : List (Report w)} {c₁ c₂ : ℕ}
    (a : SourceWalk (Source I pub state ref rows c₁) js s xs)
    (b : SourceWalk (Source I pub state mem rows c₂) js s ys) : xs = ys :=
  SourceTransport.walk_deterministic (fun _ _ _ _ h g => Option.some.inj (h.symm.trans g))
    (short_walk I d e a) (short_walk I e e b)

end CompressorRecords.ShrinkABSliceRecipe

end VPVNP
end Computability
end OAI

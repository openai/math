import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloOrdinals
import OAI.Computability.IntegerMultiplication.Short

/-! # Native stock layout for the two equal interchangeable fields -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryHalo

open IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Adic IntegerMultiplication.Loom

noncomputable section

private def naturalView {T : Type} (data : Series T) {k : ℕ} (h : data.count = k) :
    Adopt (Series.natural k) data := h ▸ data.native.back

/-- The natural address of each segment follows the literal order of its native records. -/
def nativeView (s : Shape) (w b e : ℕ) (P G B : Tape)
    (hp : s.P = room P) (hg : s.G = room G) (hb : s.B = room B) (hw : w = b^e) :
    Adopt (series s w) (stock b P G B e) :=
  let wing := naturalView (line b e) ((lineSize b e).trans hw.symm)
  (naturalView (layout P) ((space P).trans hp.symm)).split (wing.split
    ((naturalView (layout G) ((space G).trans hg.symm)).split
      (wing.split (naturalView (layout B) ((space B).trans hb.symm)))))

variable {s : Shape} {w b e : ℕ} {P G B : Tape}
variable (hp : s.P = room P) (hg : s.G = room G) (hb : s.B = room B) (hw : w = b^e)

local notation "view" => nativeView s w b e P G B hp hg hb hw

/-- Native records and mixed-radix records agree as lists, including their order. -/
theorem stock_tab {A : Type} (f : SpanKey P G B (Block b e) → A) :
    (stock b P G B e).tab f = stream (f ∘ (view).cast) := ((view).route f).trans (series_tab _)

/-- The ordinal in the physical native file is the mixed-radix rank. -/
theorem stock_rank (x : Addr s w) :
    ((stock b P G B e).index ((view).cast x)).val = (rank s w x).val := by
  let stockRows := stock b P G B e
  let j := stockRows.index ((view).cast x)
  have obs := congrArg (fun l : List (Fin (s.P*w*s.G*w*s.B)) => l[j.val]?)
    (stock_tab hp hg hb hw (fun y => rank s w ((view).cast.symm y)))
  change (stockRows.tab _)[j.val]? = _ at obs
  rw [List.getElem?_eq_getElem (by simpa only [Series.card] using j.isLt), stockRows.get _ j] at obs
  simp only [j,Equiv.symm_apply_apply] at obs
  have hj : j.val < s.P*w*s.G*w*s.B := by
    have q := congrArg List.length (stock_tab hp hg hb hw (fun _ => ()))
    simp only [Series.card, stream, List.length_ofFn] at q
    exact q ▸ j.isLt
  rw [List.getElem?_eq_getElem (by simpa [stream] using hj)] at obs
  simpa only [stream, List.getElem_ofFn, Function.comp_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, Option.map_some, Option.some.injEq] using (congrArg (Option.map Fin.val) obs).symm

/-- The segment relabeling acts identically on both wings. -/
theorem nativeView_swap (x : Addr s w) :
    (view).cast (swap x) = swapper P G B ((view).cast x) := rfl

/-- A swapped native tabulation is the same physical stream as the logical transpose. -/
theorem logical_swap {A : Type} (f : SpanKey P G B (Block b e) → A) :
    (stock b P G B e).tab (f ∘ swapper P G B) = stream ((f ∘ (view).cast) ∘ swap) := by
  rw [stock_tab hp hg hb hw]
  rfl

end
end BinaryHalo

end NearSquareRoot
end Computability
end OAI

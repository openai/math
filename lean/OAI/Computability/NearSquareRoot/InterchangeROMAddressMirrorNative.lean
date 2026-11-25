import OAI.Computability.NearSquareRoot.InterchangeROMAddressMirror
import OAI.Computability.NearSquareRoot.InterchangeROMAddressMirrorHeader

/-! # The physical field reversal implements the signed affine mirror -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMMirror

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic NearSquareRoot.Space

variable {A : Type} {p f : ℕ} [NeZero p] {P S : Tape} {s : Series A}

private def nestedRows (P : Tape) (p f : ℕ) (S : Tape)
    (v : Pin P × Block p f × Pin S → Tree) :=
  (layout P).tab (fun z => (line p f).tab (fun i => (layout S).tab (fun w => v (z,i,w))))

omit [NeZero p] in
private theorem field_solid (hp : 2 ≤ p) : solid (field p f) := by
  induction f with
  | zero => exact fun _ h => False.elim (List.not_mem_nil h)
  | succ f ih => exact (solid_cons ..).mpr ⟨hp,ih⟩

omit [NeZero p] in
private theorem flat_rows (w : Pin P × Block p f × Pin S → Tree) :
    (nestedRows P p f S w).flatten.flatten = (Board P (line p f) S).tab w := by
  rw [Series.grouped]
  simp only [Series.grouped (line p f) (layout S)]
  unfold nestedRows Series.tab
  induction (layout P).explore with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons,List.flatten_cons,List.flatten_append,ih]

private theorem reverse_rows (w : Pin P × Block p f × Pin S → Tree) :
    (nestedRows P p f S w).map List.reverse =
      nestedRows P p f S (fun x => w (x.1,mirror x.2.1,x.2.2)) := by
  unfold nestedRows
  rw [Series.map_tab]
  congr 1
  funext z
  exact returning _

/-- Realize the current flat stream as a rectangular list of suffix blocks. -/
def native (e : Slot s P (line p f) S) (hp : 2 ≤ p) (hP : solid P) (hS : solid S)
    (v : A → Tree) : Instance where
  before := P
  axis := field p f
  after_ := S
  hbefore := hP
  haxis := field_solid hp
  hafter := hS
  rows := nestedRows P p f S (v ∘ e.view.cast.symm)
  outer := by simp only [nestedRows,Series.card,space]
  middle x h := by
    obtain ⟨z,rfl⟩ := (Series.elements ..).mp h
    exact (Series.card ..).trans (space _)
  inner x h := by
    obtain ⟨row,hrow,hx⟩ := List.mem_flatten.mp h
    obtain ⟨z,rfl⟩ := (Series.elements ..).mp hrow
    obtain ⟨i,rfl⟩ := (Series.elements ..).mp hx
    exact (Series.card ..).trans (space _)

omit [NeZero p] in
theorem native_query (e : Slot s P (line p f) S) (hp : 2 ≤ p) (hP : solid P) (hS : solid S)
    (v : A → Tree) :
    (native e hp hP hS v).query =
      Tree.fork (send (shape P,shape (field p f),shape S)) (stripe s v) := by
  change Tree.fork _ (send (nestedRows P p f S (v ∘ e.view.cast.symm)).flatten.flatten) = _
  rw [flat_rows,e.view.route,stripe_eq]
  simp [Function.comp_def,Instance.dims,native]

theorem native_answer (e : Slot s P (line p f) S) (hp : 2 ≤ p) (hP : solid P) (hS : solid S)
    (v : A → Tree) :
    (native e hp hP hS v).answer = stripe s (v ∘ (e.tune mirror).symm) := by
  change send (((nestedRows P p f S (v ∘ e.view.cast.symm)).map List.reverse).flatten.flatten) = _
  rw [reverse_rows,flat_rows,e.view.route,stripe_eq]
  rfl

omit [NeZero p] in
theorem native_cells (e : Slot s P (line p f) S) (hp : 2 ≤ p) (hP : solid P) (hS : solid S)
    (v : A → Tree) : (native e hp hP hS v).cells = s.count := by
  rw [e.view.cost]
  simp only [Instance.cells,native,Board,Series.count_cart,space,line]
  ac_rfl

/-- The same command implements all native negative-width mirrors. It charges
the input header, the one stream of records and one unit per cell. -/
theorem native_command :
    ∃ C : ℕ, ∀ {A : Type} {p f : ℕ} [NeZero p] {P S : Tape} {s : Series A}
      (e : Slot s P (line p f) S) (_ : 2 ≤ p) (_ : solid P) (_ : solid S)
      (v : A → Tree) env d base, DeckCap base d →
      let input := Tree.fork (send (shape P, shape (field p f), shape S)) (stripe s v)
      let cost := C * (input.count + s.count + 1)
      BoundedFits env command (pile 0 input d) (pile 0 (stripe s (v ∘ (e.tune mirror).symm)) d)
        cost (base+cost) cost := by
  obtain ⟨C,h⟩ := command_fits
  refine ⟨C,?_⟩
  intro A p f inst P S s e hp hP hS v env d base hcap
  simpa only [Instance.work,native_cells,native_query,native_answer] using h (native e hp hP hS v) env d base hcap

end InterchangeROMMirror

end NearSquareRoot
end Computability
end OAI

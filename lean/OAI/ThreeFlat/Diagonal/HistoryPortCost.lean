import OAI.ThreeFlat.Diagonal.HistoryPostorder
import OAI.ThreeFlat.Diagonal.HistoryPortLayout
import OAI.ThreeFlat.Diagonal.HistoryWork

namespace OAI
/-! # Per-slot pin-map generation and the global binary width account -/

namespace ThreeFlat.Diagonal.HistoryContraction

open scoped Classical BigOperators

variable {Pins F : Type*} [CommSemiring F] {S : Shape}

/-- Every wire width is charged exactly once at each of its two endpoints,
including a loop's distinct tail and head half-ports. -/
theorem PortLayout.sum_halfBits (L : PortLayout S Pins) :
    (∑ v, L.halfBits v) = 2*∑ e, L.width e := by
  let site (i : S.Edge × Bool) := S.graph.vertex i.1 i.2
  let f (i : S.Edge × Bool) := L.width i.1
  calc
    _ = ∑ v, ∑ x : {i // site i=v}, f x.val := by
      apply Finset.sum_congr rfl
      intro v _
      exact (L.port v).sum_comp (fun i : S.graph.Port v => f i.val)
    _ = ∑ i : S.Edge × Bool, f i := Fintype.sum_fiberwise site f
    _ = _ := by rw [Fintype.sum_prod_type]; simp [f,two_mul,← Finset.sum_add_distrib]

variable {R : Rewrite S F} {t : Fin R.count} {V : Form S Pins} {W : Form (R.target t) Pins}

/-- This exact recurrence counts the *emitted* parent maps of the selected
terminal ancestry only, with one scalar word per addressed child pin. -/
theorem Stage.pinWords_assemble (A : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) :
    (Tree.footprint (A.assemble N v)).pins =
      (Tree.footprint (A.root v)).pins+A.rootWidth v +
      ∑ i, ((Tree.footprint (N (A.child v i).val)).pins + V.width (A.child v i).val) := by
  change (∑ i, (A.tapeFactor N v i).footprint.pins) + (∑ i, A.tapeArity N v i) = _
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Finset.sum_add_distrib]
  change ((A.root v).footprint.pins + ∑ i, (N (A.child v i).val).footprint.pins) +
    (A.rootWidth v + ∑ i, V.width (A.child v i).val) = _
  omega

theorem Stage.sum_pinWords_assemble (A : Stage R t V W) (N : Forest F V) :
    (∑ v, (Tree.footprint (A.assemble N v)).pins) =
      (∑ v, ((Tree.footprint (A.root v)).pins + A.rootWidth v)) +
      ∑ i, ((Tree.footprint (N i)).pins + V.width i) := by
  simp only [A.pinWords_assemble,Finset.sum_add_distrib]
  rw [A.sum_children (fun i => (N i).footprint.pins), A.sum_children V.width]

/-- The inherited external pin intervals form a partition of all original
external pins. Copying one full layer of maps charges their lengths once. -/
theorem PortLayout.sum_inherit (L : PortLayout S Pins) (K : PortLayout (R.target t) Pins)
    (count : (R.target t).Site → ℕ) (ord : ∀ v, Fin (count v) ≃ {i // R.owner t i=v}) :
    (∑ v, (L.inherit K count ord).ext v) = ∑ i, L.ext i := by
  change (∑ v, ∑ j, L.ext (ord v j).val) = _
  calc
    _ = ∑ v, ∑ i : {i // R.owner t i = v}, L.ext i.val := by
      apply Finset.sum_congr rfl
      intro v _
      exact (ord v).sum_comp (fun j => L.ext j.val)
    _ = _ := Fintype.sum_fiberwise _ _

theorem PortLayout.sum_form (L : PortLayout S Pins) :
    (∑ v, L.form.width v) = (∑ v, L.ext v) + 2*∑ e, L.width e := by
  change (∑ v, (L.ext v+L.halfBits v)) = _
  rw [Finset.sum_add_distrib,L.sum_halfBits]

end ThreeFlat.Diagonal.HistoryContraction

end OAI

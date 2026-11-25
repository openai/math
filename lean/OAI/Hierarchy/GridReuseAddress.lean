import OAI.Hierarchy.GridThrough

namespace OAI
/-! # The parallel lines of a spliced catalyst grid

A line label consists of its direction, all transverse grid coordinates, and
the original catalyst slot in that direction. Each passage is used once. -/

noncomputable section
namespace Hierarchy.GridReuse

open Catalyst GridThrough
open scoped Classical BigOperators

variable {m n : ℕ} (b : Fin (m+1) → ℕ)

def width (n : ℕ) (b : Fin (m+1) → ℕ) (j : Fin (m+1)) := (n+1)^m*b j

def rails (n : ℕ) (b : Fin (m+1) → ℕ) := Fintype.card (Wire (width n b))

theorem wire_card {k : ℕ} (bits : Fin k → ℕ) : Fintype.card (Wire bits) = ∑ j, bits j := by
  exact (Fintype.card_congr (finSigmaFinEquiv (n:=bits))).trans (Fintype.card_fin _)

theorem rails_eq : rails n b = (n+1)^m * ∑ j, b j := by
  change Fintype.card (Wire (width n b)) = _
  rw [wire_card,Finset.mul_sum]; rfl

abbrev Line (m n : ℕ) := Fin m → Fin (n+1)
abbrev Label (n : ℕ) (b : Fin (m+1) → ℕ) := Σ j, Line m n × Fin (b j)

def wireEquiv : Label n b ≃ Wire (width n b) :=
  Equiv.sigmaCongrRight fun _j => (Equiv.prodCongr finFunctionFinEquiv (Equiv.refl _)).trans finProdFinEquiv

def ordinal : Label n b ≃ Fin (rails n b) := (wireEquiv b).trans (Fintype.equivFin _)

def label (e : Fin (rails n b)) := (ordinal b).symm e

def baseline (j : Fin (m+1)) (u : Line m n) : Cell (m+1) n :=
  j.insertNth (α:=fun _ => Fin (n+1)) 0 u

private theorem update_baseline (j : Fin (m+1)) (u : Line m n) (t : Fin (n+1)) :
    GridLens.cellOnRail j (baseline j u) t = j.insertNth (α:=fun _ => Fin (n+1)) t u := by
  rw [← Fin.update_insertNth (α:=fun _ => Fin (n+1)) j 0 t u]
  funext i
  by_cases h : i=j
  · simp [GridLens.cellOnRail,h]
  · simp [GridLens.cellOnRail,h,baseline]

def program : GridThrough.Program (Fin (rails n b)) n 0 b where
  direction e := (label b e).1
  row e := baseline (label b e).1 (label b e).2.1
  touch _ := none
  data _ i := i.elim0
  data_cell _ i := i.elim0
  data_once u := by cases u.1.property
  pass c w := ordinal b ⟨w.1,w.1.removeNth c,w.2⟩
  pass_injective c := by
    rintro ⟨j,w⟩ ⟨l,z⟩ h
    have same := (ordinal b).injective h
    exact congrArg (fun v : Label n b => (⟨v.1,v.2.2⟩ : Wire b)) same
  pass_dir _ _ := by simp [label]
  pass_line c w := by
    simp only [label,Equiv.symm_apply_apply, update_baseline]
    have back := congrArg (fun z : Label n b => z.2.1)
      ((ordinal b).symm_apply_apply ⟨w.1,w.1.removeNth c,w.2⟩)
    rw [back]
    exact Fin.insertNth_self_removeNth (α:=fun _ => Fin (n+1)) w.1 c
  pass_untouched _ _ := by simp

@[simp] theorem program_direction (e : Fin (rails n b)) :
    (program b).direction e = ((Fintype.equivFin (Wire (width n b))).symm e).1 := rfl

theorem occupies (e : Fin (rails n b)) (t : Fin (n+1)) : (program b).Selected e t := by
  obtain ⟨⟨j,u,i⟩,rfl⟩ := (ordinal b).surjective e
  refine ⟨⟨j,i⟩,?_⟩
  apply congrArg (ordinal b)
  dsimp only [Program.railCell,program]
  simp [label, update_baseline]
  exact congrArg (fun z : Label n b => z.2.1) ((ordinal b).symm_apply_apply ⟨j,u,i⟩)


end Hierarchy.GridReuse

end
end OAI

import OAI.Hierarchy.DescentWholeItems
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup

namespace OAI
/-! # Removing zero-capacity destinations from ordered whole-item matching -/

noncomputable section
namespace Hierarchy.DescentPacking.Sparse
open scoped Classical
variable {C A I : Type*} [Fintype C] [DecidableEq C] [Fintype A] [DecidableEq A]

/-- Retain the first destination even when it has zero capacity, since it
receives every zero-width pack. -/
def keep (neighbors : Finset C) : Finset C :=
  match (binOrder C).head? with
  | none => neighbors
  | some v => insert v neighbors

theorem keep_size (neighbors : Finset C) : (keep neighbors).card≤neighbors.card+1 := by
  unfold keep
  cases (binOrder C).head? with
  | none => exact Nat.le_succ _
  | some v => exact Finset.card_insert_le ..

theorem neighbor_mem {neighbors : Finset C} {v : C} (h : v∈neighbors) : v∈keep neighbors := by
  unfold keep
  cases (binOrder C).head? <;> simp_all

def roster (neighbors : Finset C) := (binOrder C).filter (fun c=>decide (c∈keep neighbors))

theorem roster_nodup (neighbors : Finset C) : (roster neighbors).Nodup := by
  apply List.Nodup.filter
  exact (List.nodup_finRange _).map (Fintype.equivFin C).symm.injective

theorem roster_size (neighbors : Finset C) : (roster neighbors).length≤neighbors.card+1 := by
  calc
    _ = (roster neighbors).toFinset.card := (List.toFinset_card_of_nodup (roster_nodup neighbors)).symm
    _ = (keep neighbors).card := by
      apply congrArg Finset.card
      ext c
      simp [roster,mem_binOrder]
    _ ≤ _ := keep_size neighbors

private theorem positive_filter (xs : List C) (neighbors : Finset C)
    (cap : C→ℕ) (need : ℕ) (positive : 0<need) (support : ∀v,0<cap v→v∈keep neighbors) :
    (xs.filter (fun c=>decide (c∈keep neighbors))).find? (fun c=>decide (need≤cap c)) =
    xs.find? (fun c=>decide (need≤cap c)) := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    by_cases inside : c∈keep neighbors
    · simp [inside,List.find?_cons,ih]
    · have small : ¬need≤cap c := fun h => inside (support c (positive.trans_le h))
      simp [inside,small,ih]

theorem find_eq (neighbors : Finset C) (cap : C→ℕ) (need : ℕ)
    (support : ∀v,0<cap v→v∈keep neighbors) :
    (roster neighbors).find? (fun c=>decide (need≤cap c))=firstFit need cap := by
  cases need with
  | succ n => exact positive_filter _ _ _ _ (Nat.zero_lt_succ _) support
  | zero =>
    unfold roster firstFit
    cases order : binOrder C with
    | nil => rfl
    | cons c cs =>
      have hit : c∈keep neighbors := by simp [keep,order]
      simp [hit]

/-- Native local names may use the standard finite ordinal permutation; this
is the order equality needed by the native first-fit receipt. -/
structure Directory (neighbors : Finset C) (A : Type*) [Fintype A] where
  name : A ↪ C
  order : (binOrder A).map name = roster neighbors

/-- The public physical slot is the filtered list position, independently
of the enumeration used by the local finite type. -/
def coordinate (neighbors : Finset C) :=
  (Fintype.equivFin (Fin (roster neighbors).length)).trans (finCongr (Fintype.card_fin _))

def dense (neighbors : Finset C) : Directory neighbors (Fin (roster neighbors).length) where
  name := (coordinate neighbors).toEmbedding.trans
    ⟨(roster neighbors).get,List.nodup_iff_injective_get.mp (roster_nodup neighbors)⟩
  order := by
    apply List.ext_getElem
    · simp [binOrder]
    · intro i hi hj
      simp [binOrder,coordinate]

namespace Directory
variable {neighbors : Finset C}

omit [DecidableEq A] in
theorem choice (D : Directory neighbors A) (cap : C→ℕ) (need : ℕ)
    (support : ∀v,0<cap v→v∈keep neighbors) :
    (firstFit need (cap ∘ D.name)).map D.name=firstFit need cap := by
  rw [←find_eq neighbors cap need support,←D.order,List.find?_map]
  rfl

private theorem restrict_consume (D : Directory neighbors A) (cap : C→ℕ) (need : ℕ) (chosen : Option A) :
    consume need (cap ∘ D.name) chosen = (consume need cap (chosen.map D.name)) ∘ D.name := by
  funext a
  cases chosen with
  | none => rfl
  | some b =>
    by_cases same : a=b
    · subst b
      simp [consume,Function.comp_def]
    · have ne : D.name a≠D.name b := fun e=>same (D.name.injective e)
      simp [consume,Function.comp_def,Function.update_of_ne,same,ne]

omit [Fintype C] in
theorem consume_le (cap : C→ℕ) (need : ℕ) (chosen : Option C) (v : C) :
    consume need cap chosen v≤cap v := by
  cases chosen with
  | none => exact le_rfl
  | some c =>
    by_cases same : v=c
    · subst c
      simp [consume]
    · simp [consume,Function.update_of_ne,same]

def decode (D : Directory neighbors A) (p : I×Option A) : I×Option C := (p.1,p.2.map D.name)

theorem decisions (D : Directory neighbors A) (amount : I→ℕ) (xs : List I) (cap : C→ℕ)
    (support : ∀v,0<cap v→v∈keep neighbors) :
    (pack amount xs (cap ∘ D.name)).decisions.map D.decode=(pack amount xs cap).decisions := by
  induction xs generalizing cap with
  | nil => rfl
  | cons i xs ih =>
    let p := firstFit (amount i) (cap ∘ D.name)
    have pick := D.choice cap (amount i) support
    have rest := D.restrict_consume cap (amount i) p
    rw [show p.map D.name=firstFit (amount i) cap from pick] at rest
    rw [pack_decisions_cons,pack_decisions_cons,List.map_cons]
    apply congrArg₂ List.cons
    · exact congrArg (Prod.mk i) pick
    · rw [show consume (amount i) (cap ∘ D.name) (firstFit (amount i) (cap ∘ D.name))=
          (consume (amount i) cap (firstFit (amount i) cap)) ∘ D.name from rest]
      exact ih _ (fun v hv=>support v (hv.trans_le (consume_le ..)))

theorem assigned_decode (D : Directory neighbors A) (amount : I→ℕ) (v : A) (rows : List (I×Option A)) :
    assigned amount (D.name v) (rows.map D.decode)=assigned amount v rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨i,_|a⟩ := row
    · simp [decode,assigned,ih]
    · simp [decode,assigned,ih]

/-- The capacity already consumed at a selected target agrees at *every*
prefix, hence every issued old thick-edge offset agrees too. -/
theorem prior (D : Directory neighbors A) (amount : I→ℕ) (xs : List I) (cap : C→ℕ)
    (support : ∀v,0<cap v→v∈keep neighbors) (t : ℕ) (v : A) :
    assigned amount (D.name v) ((pack amount xs cap).decisions.take t)=
    assigned amount v ((pack amount xs (cap ∘ D.name)).decisions.take t) := by
  rw [←D.decisions amount xs cap support,←List.map_take]
  exact D.assigned_decode ..

end Directory
end Hierarchy.DescentPacking.Sparse

end
end OAI

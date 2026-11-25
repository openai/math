import OAI.Computability.BorderVNP.PackedGridBoxFactors
import OAI.Computability.BorderVNP.PackedGridLocalBounds

/-! # One private box directory for all copies at an initial grid cell

The directory orders its fine sites by their original names. It stores each site's local
factor once and uses one public repeat record for the bottom bundle. Actual `Packet.factor`
and `Packet.fieldList` word lengths bound its private description.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse Finset
open scoped Classical
variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C)
variable {m n s : ℕ} (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- Ascending fine site names among the sites retained in this cell. -/
noncomputable def siteList : List {v : N.Site // cell v = c} := by
  let order := (Function.Embedding.subtype (fun v => cell v = c)).trans siteID
  letI := LinearOrder.lift' order order.injective
  exact List.ofFn ((Fintype.orderIsoFinOfCardEq _ rfl).toEquiv)

omit [Fintype P] in
@[simp] theorem siteList_length :
    (siteList N cell c siteID).length = Fintype.card {v : N.Site // cell v = c} := List.length_ofFn

omit [Fintype P] in
@[simp] theorem mem_siteList (v : {v : N.Site // cell v = c}) :
    v ∈ siteList N cell c siteID := by
  unfold siteList
  rw [List.mem_ofFn]
  exact Equiv.surjective _ v

variable (rules : ∀ v : {v : N.Site // cell v = c}, Rule N v.val)

/-- Each local factor occurs exactly once in the stored one-copy description. -/
noncomputable def factors : List Factor :=
  (siteList N cell c siteID).map (fun v => ruleFactor N cell c edgeID portID v (Fintype.equivFin _) (rules v))

/-- The private one-copy box is repeated by one public record at the actual per-copy
assignment stride. A unary factor can refer to copy-indexed report bits outside the box. -/
noncomputable def directory (copies : ℕ) : Directory where
  boxes := [factors N cell c siteID edgeID portID rules]
  records := [.box 0 0 copies (stride N cell c)]
  reportedCounts := []

/-- Reading the public repeat record visits each stored factor at its own copy offset. -/
theorem directory_occurrences (copies : ℕ) :
    (directory N cell c siteID edgeID portID rules copies).occurrences =
      (List.range copies).flatMap (fun i => (siteList N cell c siteID).map fun v =>
        (⟨ruleFactor N cell c edgeID portID v (Fintype.equivFin _) (rules v),
          i*stride N cell c,i⟩ : Occurrence)) := by
  simp [Directory.occurrences,directory,factors,List.map_map,Function.comp_def]

private theorem mapM_present {A B : Type} (xs : List A) (f : A → Option B) :
    (xs.mapM f).isSome = true ↔ ∀ x ∈ xs, (f x).isSome = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : f x with
    | none => simp [List.mapM_cons,h,Option.pure_def]
    | some y =>
      cases hr : xs.mapM f with
      | none => simp_all [List.mapM_cons,Option.pure_def]
      | some ys => simp_all [List.mapM_cons,Option.pure_def]

/-- A cell's complete private pass condition checks every fine Boolean factor and
reported unary use in every actual copy of the physical bundle. -/
theorem directory_accepts (copies : ℕ) (bank : ℕ → Bool) :
    ((directory N cell c siteID edgeID portID rules copies).observations bank).isSome = true ↔
      ∀ i < copies, ∀ v : {v : N.Site // cell v = c},
        accepts N cell c edgeID portID v bank (i*stride N cell c) i (rules v) = true := by
  rw [Directory.observations,mapM_present,directory_occurrences]
  simp only [List.mem_flatMap,List.mem_range,List.mem_map,forall_exists_index,and_imp]
  constructor
  · intro hh i hi v
    have hp := hh _ i hi v (mem_siteList N cell c siteID v) rfl
    rw [observe_rule] at hp
    simpa using hp
  · rintro h _ i hi v _ rfl
    rw [observe_rule]
    simp [h i hi v]

/-- The entire private one-copy payload takes at most one length word plus fourteen
words per fine site. It is stored once at any positive or zero repeat count. -/
theorem box_words_le (degree : ∀ v : {v : N.Site // cell v = c}, Fintype.card (CellBox.Lane N v.val) ≤ 3) :
    (Packet.fieldList Packet.factor (factors N cell c siteID edgeID portID rules)).length ≤
      1 + 14*Fintype.card {v : N.Site // cell v = c} := by
  unfold Packet.fieldList factors
  rw [List.length_cons,List.length_flatMap,List.map_map]
  have hh := List.sum_le_sum (l := siteList N cell c siteID) (g := Function.const _ 14)
    (fun v _ => factor_words_le N cell c edgeID portID v (Fintype.equivFin _) (degree v) (rules v))
  simp only [List.map_const,List.sum_replicate,siteList_length,nsmul_eq_mul] at hh
  rw [Nat.add_comm 1, Nat.mul_comm 14]
  apply Nat.succ_le_succ
  convert! hh using 1

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI

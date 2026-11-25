import OAI.Computability.BorderVNP.PackedBottomGridSite
import OAI.Computability.BorderVNP.PackedGridAlive

/-! # Forced use choices before the external use links are added

The private one-copy staging compares each original selected wire with its
private report lane. Consequently the staged uses already have one value for
a fixed fine assignment. This local fact is independent of later placement
or the addresses chosen for external tally operands.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing CellSparse GridBoxes
open scoped Classical

/-- The original relative wire selected by each listed weighted source. -/
def selectedWires : List Factor → List ℕ
  | [] => []
  | .unary wire _ :: fs => wire :: selectedWires fs
  | _ :: fs => selectedWires fs

/-- Every actual source contributes exactly one selected wire address. -/
@[simp] theorem selectedWires_length (fs : List Factor) : (selectedWires fs).length = count fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [selectedWires,count,ih]

/-- All original factors other than the weighted report comparisons succeed. -/
def ordinaryReads (bank : ℕ → Bool) (off copy : ℕ) : List Factor → Prop
  | [] => True
  | .unary _ _ :: fs => ordinaryReads bank off copy fs
  | f :: fs => (f.observe bank off copy).isSome = true ∧ ordinaryReads bank off copy fs

/-- The original-box pass fixes every private staged use to the corresponding
selected fine wire. Each unmarked factor retains its own pass condition. -/
theorem stage_pass (bank : ℕ → Bool) (off copy next : ℕ) (fs : List Factor) :
    (∀ f ∈ stage next fs, (f.observe bank off copy).isSome = true) ↔
      ordinaryReads bank off copy fs ∧ ∀ t : Fin (count fs),
        bank (off+next+t.val) = bank (off+(selectedWires fs)[t.val]'(by simp)) := by
  induction fs generalizing next with
  | nil => simp [stage,ordinaryReads,count]
  | cons f fs ih =>
    cases f with
    | truth | sign | gadget => simp only [stage,List.forall_mem_cons,ordinaryReads,count,selectedWires,ih,and_assoc]
    | unary wire tag =>
      simp only [stage,List.forall_mem_cons,compareUse_observe,ih,ordinaryReads,count,selectedWires]
      constructor
      · rintro ⟨h,ho,ht⟩
        refine ⟨ho,?_⟩
        intro t
        refine Fin.cases ?_ (fun j => ?_) t
        · by_cases he : bank (off+wire) = bank (off+next)
          · simpa using he.symm
          · simp [he] at h
        · simpa only [Fin.val_succ,List.getElem_cons_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ht j
      · rintro ⟨ho,ht⟩
        have h := ht 0
        simp only [Fin.val_zero,List.getElem_cons_zero,Nat.add_zero] at h
        refine ⟨by simp [h],ho,?_⟩
        intro j
        simpa only [Fin.val_succ,List.getElem_cons_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ht j.succ

private theorem selected_mem (fs : List Factor) (w : ℕ) (h : w ∈ selectedWires fs) :
    ∃ p, Factor.unary w p ∈ fs := by
  induction fs with
  | nil => simp [selectedWires] at h
  | cons f fs ih =>
    cases f with
    | truth | sign | gadget =>
      obtain ⟨p,hp⟩ := ih h
      exact ⟨p,List.mem_cons_of_mem _ hp⟩
    | unary wire tag =>
      rcases List.mem_cons.mp h with e | h
      · exact ⟨tag,e ▸ List.mem_cons_self⟩
      · obtain ⟨p,hp⟩ := ih h
        exact ⟨p,List.mem_cons_of_mem _ hp⟩

/-- The actual selected one-copy wire for the sidecar's named source rank. -/
noncomputable def selectedWire {D : ℕ} {P C : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → C) (v : C) {ns ne np : ℕ} (sites : N.Site ↪ Fin ns) (edges : N.Edge ↪ Fin ne)
    (ports : P ↪ Fin np) (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)
    (i : Fin (count (factors N cell v sites edges ports rules))) : Fin (GridBoxes.stride N cell v) := by
  let fs := factors N cell v sites edges ports rules
  let j : Fin (selectedWires fs).length := ⟨i,by simpa only [selectedWires_length] using i.isLt⟩
  refine ⟨(selectedWires fs)[j.val],?_⟩
  obtain ⟨p,hp⟩ := selected_mem fs _ (List.getElem_mem j.isLt)
  obtain ⟨u,_,hu⟩ := List.mem_map.mp hp
  cases hr : rules u with
  | truth t => simp only [hr,ruleFactor,reduceCtorEq] at hu
  | unary l a =>
    simp only [hr,ruleFactor,Factor.unary.injEq] at hu
    exact hu.1 ▸ (lane N cell v edges ports u l).isLt

private def ordinary (f : Factor) (bank : ℕ → Bool) (off copy : ℕ) : Prop :=
  match f with
  | .unary _ _ => True
  | _ => (f.observe bank off copy).isSome = true

private theorem ordinary_iff (fs : List Factor) (bank : ℕ → Bool) (off copy : ℕ) :
    ordinaryReads bank off copy fs ↔ ∀ f ∈ fs, ordinary f bank off copy := by
  induction fs with
  | nil => simp [ordinaryReads]
  | cons f fs ih => cases f <;> simp [ordinaryReads,ordinary,ih]

/-- For genuine fine-site boxes the ordinary part consists of the source paper's
Boolean gate checks. Weighted vertices impose only the selected-use comparison. -/
theorem ordinary_grid {D : ℕ} {P C : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → C) (c : C) {ne np ns : ℕ} (sites : N.Site ↪ Fin ns)
    (edges : N.Edge ↪ Fin ne) (ports : P ↪ Fin np) (rules : ∀ w : {u : N.Site // cell u = c}, Rule N w.val)
    (bank : ℕ → Bool) (off copy : ℕ) :
    ordinaryReads bank off copy (factors N cell c sites edges ports rules) ↔
      ∀ w, (rules w).base (fun l => bank (off+(lane N cell c edges ports w l).val)) = true := by
  rw [ordinary_iff]
  simp only [factors,List.forall_mem_map,mem_siteList,forall_true_left]
  apply forall_congr'
  intro w
  cases h : rules w with
  | truth t =>
    change ((ruleFactor N cell c edges ports w (Fintype.equivFin _) (.truth t)).observe bank off copy).isSome = true ↔ _
    rw [observe_rule,accepts_passes]
    cases ht : t (fun l => bank (off+(lane N cell c edges ports w l).val)) <;> simp [Rule.base,Rule.passes,ht]
  | unary => simp [ruleFactor,ordinary,Rule.base]

end Packing.BottomReports

end BorderVNP
end Computability
end OAI

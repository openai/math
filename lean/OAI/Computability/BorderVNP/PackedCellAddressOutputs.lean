import OAI.Computability.BorderVNP.PackedCellAddressViews

/-! # Checked canonical outputs of the sparse cell allocation program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressViews

open Crossing CellAddresses CellAddressPhysical ParseBatchSort CellAddressCircuit
open private srcKey dstKey sourceRow destRow from OAI.Computability.BorderVNP.PackedCellAddressPhysical
open scoped Classical

variable {D s m n C d k w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)
variable {x : σ → Bool} (h : Represents N cell aux siteID edgeID portID F x)
variable (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)

include h fit

/-- The site-view column gives the beginning of the private staging slab in its current cell. -/
theorem site_value (v : N.Site) :
    value (fun j => (frame F).eval x (.inr (.inl (siteID v)),j)) =
      siteBase N cell (cell v) siteID aux ⟨v,rfl⟩ := by
  simp only [frame_eval,row]
  exact frame_absolute N cell aux siteID edgeID portID F (cell v) h fit (.inl (.inr ⟨v,rfl⟩))

/-- The port-view column gives the absolute position of its attached supplied word. -/
theorem port_value (p : P) :
    value (fun j => (frame F).eval x (.inl (.inr (portID p)),j)) =
      portBase N cell (cell (N.attach p)) edgeID portID aux ⟨N.attach p,rfl⟩ ⟨p,rfl⟩ := by
  simp only [frame_eval,row]
  apply (frame_absolute N cell aux siteID edgeID portID F (cell (N.attach p)) h fit (.inr (.inr ⟨p,rfl⟩))).trans
  simp only [absolute,Sum.elim_inr,portBase,CellSlabs.start]
  congr 2; exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

/-- The source sees the unique private cable word or its own crossing endpoint. -/
theorem source_value (e : N.Edge) :
    value (fun j => (frame F).eval x (.inl (.inl (.inl (edgeID e))),j)) =
      wireBase N cell (cell (N.src e)) edgeID portID aux ⟨N.src e,rfl⟩ ⟨e,.inl rfl⟩ := by
  have he : (data F x).loc (.inl (.inl (edgeID e))) = (data F x).loc (.inl (.inr (edgeID e))) ↔
      cell (N.src e) = cell (N.dst e) := by
    rw [srcKey N cell aux siteID edgeID portID F h, dstKey N cell aux siteID edgeID portID F h,
      Fin.val_inj, F.cells.injective.eq_iff]
  simp only [frame_eval,row,he]
  by_cases hs : cell (N.src e) = cell (N.dst e)
  · simp only [wireBase,hs,dite_true,ite_true]
    apply (frame_absolute N cell aux siteID edgeID portID F _ h fit (.inl (.inl ⟨e,rfl,hs.symm⟩))).trans
    simp only [absolute,Sum.elim_inl,CellSlabs.start]
    exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)
  · let u : Boundary N cell (cell (N.src e)) := ⟨⟨e,hs⟩,.inl rfl⟩
    have f := frame_absolute N cell aux siteID edgeID portID F _ h fit (.inr (.inl u))
    rw [sourceRow N cell siteID edgeID portID _ u rfl] at f
    simp only [wireBase,hs,dite_false,ite_false]
    apply f.trans
    simp only [absolute,Sum.elim_inr,CellSlabs.start]
    congr 2; exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

/-- The destination sees precisely the same compact private word in the internal case. -/
theorem dest_value (e : N.Edge) :
    value (fun j => (frame F).eval x (.inl (.inl (.inr (edgeID e))),j)) =
      wireBase N cell (cell (N.dst e)) edgeID portID aux ⟨N.dst e,rfl⟩ ⟨e,.inr rfl⟩ := by
  have he : (data F x).loc (.inl (.inl (edgeID e))) = (data F x).loc (.inl (.inr (edgeID e))) ↔
      cell (N.src e) = cell (N.dst e) := by
    rw [srcKey N cell aux siteID edgeID portID F h, dstKey N cell aux siteID edgeID portID F h,
      Fin.val_inj, F.cells.injective.eq_iff]
  simp only [frame_eval,row,he]
  by_cases hs : cell (N.src e) = cell (N.dst e)
  · simp only [wireBase,hs,dite_true,ite_true]
    apply (frame_absolute N cell aux siteID edgeID portID F _ h fit (.inl (.inl ⟨e,hs,rfl⟩))).trans
    simp only [absolute,Sum.elim_inl,CellSlabs.start]
    exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)
  · let u : Boundary N cell (cell (N.dst e)) := ⟨⟨e,hs⟩,.inr rfl⟩
    have f := frame_absolute N cell aux siteID edgeID portID F _ h fit (.inr (.inl u))
    rw [destRow N cell siteID edgeID portID _ u hs] at f
    simp only [wireBase,hs,dite_false,ite_false]
    apply f.trans
    simp only [absolute,Sum.elim_inr,CellSlabs.start]
    congr 2; exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

/-- A returned marker is the exact compact end of its region. -/
theorem marker_value (c : Fin C) (i : Fin 3) :
    value (fun j => (frame F).eval x (.inr (.inr (i,c)),j)) =
      guessedSize N cell c + (if i = 0 then 0 else siteSize N cell c aux) +
        (if i = 2 then suppliedSize N cell c else 0) := by
  simp only [frame_eval,row]
  exact frame_marker N cell aux siteID edgeID portID F c h fit i

end Packing.CellAddressViews

end BorderVNP
end Computability
end OAI

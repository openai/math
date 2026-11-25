import OAI.Computability.BorderVNP.PackedFinalReportFrame
import OAI.Computability.BorderVNP.PackedFinalCellSupplement
import OAI.Computability.BorderVNP.CellPacketGeometryFinalDirectory

/-! # Count and private-wire fields in the actual sorted public packet template -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FinalReports

open Crossing CellAddresses CellAddressViews CellAddressPhysical CellAddressCircuit ParseBatchSort
open VPVNP.VerifierNetwork CellPacketGeometry.LiveWords CellPacketGeometry.SiteWords
open DiagonalTallyCellReports Inherited
open scoped Classical

variable {s m n C g digits w : ℕ} {E I Orig : Type}

/-- Install the fixed operand list in the native emitter template. Existing
site records and one-copy box references retain their physical row ordering. -/
def Template.installReports (T : Template E I Orig s C) (g digits : ℕ) :
    Template (Pin C g digits ⊕ E) I Orig s C where
  boxes := T.boxes
  format := T.format
  privateWires c := .inl (.inl c)
  reports c := (countPins c).map (List.map Sum.inl)

variable {σ : Type*} [Fintype σ] [Fintype E]

/-- Shared gate list exposing the computed report operands and the other
upstream public fields on the emitter's combined input alphabet. -/
noncomputable def joinFields (base : Frame σ (View s m n C × Fin w)) (rest : Frame σ (E × Fin w)) :
    Frame σ ((Pin C g digits ⊕ E) × Fin w) :=
  (Crossing.parallelFrame (frame base) rest).select (fun z => z.1.elim (fun p => .inl (p,z.2)) (fun e => .inr (e,z.2)))

theorem joinFields_size (base : Frame σ (View s m n C × Fin w)) (rest : Frame σ (E × Fin w)) :
    (joinFields (g := g) (digits := digits) base rest).size ≤
      base.size+(C+C*g*digits)*w*(100*(w+1))+rest.size := by
  rw [joinFields,Frame.select_size,Crossing.parallelFrame_size]
  exact Nat.add_le_add_right (frame_size base) _

variable {D d k : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  (cell : N.Site → Fin C) (state : N.Site → Site)

/-- Passing from the physical finite cell IDs to their natural numerals
preserves all three measured bank widths. -/
theorem bank_sizes (c : Fin C) :
    guessedSize N (fun v => (cell v).val) c.val = guessedSize N cell c ∧
    siteSize N (fun v => (cell v).val) c.val (fun v => (state v).size) =
      siteSize N cell c (fun v => (state v).size) ∧
    suppliedSize N (fun v => (cell v).val) c.val = suppliedSize N cell c := by
  refine ⟨?_,?_,?_⟩
  · let a : N.InsideEdge (fun v => (cell v).val) c.val ≃ N.InsideEdge cell c :=
      Equiv.subtypeEquivRight fun i => by simp only [Fin.val_inj]
    unfold guessedSize
    convert! Fintype.sum_equiv a (fun e => N.width e.val) (fun e => N.width e.val) (fun _ => rfl) using 1 <;>
      exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)
  · let a : {v : N.Site // (cell v).val = c.val} ≃ {v : N.Site // cell v=c} :=
      Equiv.subtypeEquivRight fun _ => Fin.val_inj
    unfold siteSize
    convert! Fintype.sum_equiv a (fun v => (state v.val).size) (fun v => (state v.val).size) (fun _ => rfl) using 1 <;>
      exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)
  · let a : Boundary N (fun v => (cell v).val) c.val ≃ Boundary N cell c :=
      { toFun := fun e => ⟨⟨e.val.val,fun he => e.val.property (congrArg Fin.val he)⟩,
          e.property.imp (fun h => Fin.ext h) (fun h => Fin.ext h)⟩
        invFun := fun e => ⟨⟨e.val.val,fun he => e.val.property (Fin.ext he)⟩,
          e.property.imp (congrArg Fin.val) (congrArg Fin.val)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let b := Equiv.subtypeEquivRight (p := fun u => (cell (N.attach u)).val = c.val)
      (q := fun u => cell (N.attach u)=c) (fun _ => Fin.val_inj)
    unfold suppliedSize
    convert! Fintype.sum_equiv (Equiv.sumCongr a b) (suppliedWidth N (fun v => (cell v).val) c.val)
      (suppliedWidth N cell c) (fun i => by cases i <;> rfl) using 1 <;>
      exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)

variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
  (F : Fields s m n C d k w σ) {x : σ → Bool}
  (h : Represents N cell (fun v => (state v).size) siteID edgeID portID F x)
  (fit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c < 2^w)
  (T : Template E I Orig s C) (rest : Frame σ (E × Fin w)) (owner : Fin s → Fin C)
  (localWords : Fin s → I → ℕ) (anchor : Fin s → Fin s)

include h fit

/-- Evaluation and owner sorting deliver the actual private-bank end and the
complete list of gadget count addresses to the cell. The field words come from
the physical marker frame. -/
theorem emitted (c : Fin C)
    (room : guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c+g*digits ≤ 2^w) :
    let f := joinFields (g := g) (digits := digits) (CellAddressViews.frame F) rest
    let args := fun p => value fun j => f.eval x (p,j)
    let G := ((Template.installReports T g digits).directory owner args localWords).regroup anchor
    G.privateWires c = FinalCell.privateBits N (fun v => (cell v).val) state c.val ∧
      G.reports c = countFields (FinalCell.countBase N (fun v => (cell v).val) state c.val) g digits := by
  obtain ⟨hguess,hsite,hsupply⟩ := bank_sizes N cell state c
  have hp := private_value (g := g) (digits := digits) N cell (fun v => (state v).size) siteID edgeID portID F h fit c
  have hc := countPins_value N cell (fun v => (state v).size) siteID edgeID portID F h fit c room
  dsimp only [Directory.regroup,Template.directory,Template.installReports]
  simp only [joinFields,Frame.select_eval,Sum.elim_inl,Crossing.parallelFrame_eval_inl,
    Function.comp_def,List.map_ofFn,countPins] at hc ⊢
  simpa only [FinalCell.privateBits,FinalCell.countBase,hguess,hsite,hsupply] using And.intro hp hc

omit fit in
/-- The terminal tile load and the actual external report length give the
width conditions for every physical marker and for the selected count fields. -/
theorem emitted_of_load (c : Fin C) (M E₀ : ℕ)
    (hin : ∀ v, (state v).incoming = incoming N v)
    (hexp : ∀ u : Fin C, Shortening.localRecords N true (fun v => (state v).staticNodes)
      (fun v => (state v).expandedLoad) (fun v => cell v=u) ≤ M)
    (hext : suppliedSize N cell c + g*digits ≤ E₀) (width : 3*M+E₀ < 2^w) :
    let f := joinFields (g := g) (digits := digits) (CellAddressViews.frame F) rest
    let args := fun p => value fun j => f.eval x (p,j)
    let G := ((Template.installReports T g digits).directory owner args localWords).regroup anchor
    G.privateWires c = FinalCell.privateBits N (fun v => (cell v).val) state c.val ∧
      G.reports c = countFields (FinalCell.countBase N (fun v => (cell v).val) state c.val) g digits := by
  have cap (u : Fin C) := (merged_bank_capacity N state cell u hin).trans (Nat.mul_le_mul_left 3 (hexp u))
  apply emitted N cell state siteID edgeID portID F h (fun u => (cap u).trans_lt (by omega)) T rest owner localWords anchor c
  have hprivate := (Nat.le_add_right _ (suppliedSize N cell c)).trans (cap c)
  omega

end Packing.FinalReports

end BorderVNP
end Computability
end OAI

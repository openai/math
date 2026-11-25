import OAI.Computability.BorderVNP.PackedFrozenMeasuredNode
import OAI.Computability.BorderVNP.PackedTerminalEndpointFields

/-! # The measured old-endpoint fields on occupied and vacant cable rows

The selected pre-stage gives genuine widths at occupied rows. A single
bitwise mask supplies the zero widths on holes required by the incidence
prefix scan. The grouped ports use the fixed attachment and width headers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.OldFields

open Crossing Shortening DirectoryCircuit ParseBatchSort CellAddressCircuit VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit
open scoped Classical

variable {D m rows sites np b w : ℕ} {σ : Type*} [Fintype σ]
    (pop : PublicPopulation.Pins (Fin rows) σ b w) (col : Columns σ rows D w)

/-- Source pins followed by the masked old width fields and the two shared literal values. -/
abbrev Pin (σ : Type*) (rows w : ℕ) := σ ⊕ ((Fin rows × Fin w) ⊕ Bool)

private def expr : ((Fin rows × Fin w) ⊕ Bool) → StatementCircuit.Expr σ
  | .inl (i,j) => .and (.input (col.occupied i)) (.input (pop.width i j))
  | .inr b => .const b

/-- All live old widths and the two shared literal wires on the same original assignment. -/
noncomputable def frame : Frame σ (Pin σ rows w) :=
  ((Frame.initial id).step (expr pop col)).withInput

/-- Each old cable-width bit uses one conjunction and two wire references. -/
theorem frame_size : (frame pop col).size ≤ (rows*w+2)*3 := by
  have h := Frame.step_size_le (Frame.initial (id : σ → σ)) (expr pop col) 3 (fun z => by
    rcases z with ⟨_,_⟩ | b
    · exact le_rfl
    · exact (by decide : 1 ≤ 3))
  simpa only [frame,Frame.withInput_size,Frame.initial_size,zero_add,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool] using h

/-- The original selected fields keep their wire identities. -/
theorem original (x : σ → Bool) (v : σ) : (frame pop col).eval x (.inl v) = x v := by simp [frame]

/-- Both constant values are shared by the old and the new virtual fields. -/
theorem literal (x : σ → Bool) (b : Bool) : (frame pop col).eval x (.inr (.inr b)) = b := by
  simp [frame,expr,StatementCircuit.Expr.eval]

/-- The width of a vacant row is always zero, and an occupied row reads the selected population field. -/
theorem masked (x : σ → Bool) (r : Fin rows) (j : Fin w) :
    (frame pop col).eval x (.inr (.inl (r,j))) = (x (col.occupied r) && x (pop.width r j)) := by
  simp [frame,expr,StatementCircuit.Expr.eval]

variable (fit : sites ≤ 2^w) (host width : Fin np → ℕ)

/-- Endpoint pointers are the actual selected parallel positions. The masked
widths and the grouped external headers use the same common pins. -/
noncomputable def fields : Fields sites rows np 1 w 0 w (Pin σ rows w) where
  sites := Fin.castLEEmb fit
  cells := Fin.castLEEmb (by decide)
  owner _ _ := .inr (.inr false)
  ptr
    | .inl (.inl r),j => .inl (col.endpoint r true j)
    | .inl (.inr r),j => .inl (col.endpoint r false j)
    | .inr r,j => .inr (.inr ((host r).testBit (w-1-j.val)))
  edgeWidth r j := .inr (.inl (r,j))
  auxWidth _ _ := .inr (.inr false)
  portWidth r j := .inr (.inr ((width r).testBit (w-1-j.val)))

variable [NeZero D] {K P A : Type} [Field K] [Fintype P] [Fintype A] {bits : P → ℕ} {n : ℕ}
    (e : PaidIdentity K D m) (p : Pack D P bits K) (bin : p.layout.Edge → Option A)
    (positive : p.layout.Edge → Bool) (code : A ↪ Fin (2^b)) (seed : A ≃ Fin n)
    (site : p.layout.Site ↪ Fin sites) (slot : p.layout.Edge ↪ Fin rows) (port : P ↪ Fin np)
    (dummy : Fin (StaticRows.edgeCapacity e rows n) → StaticRows.SiteShape e (densePack p slot) A)

omit [NeZero D] [Fintype P] [Fintype A] in
/-- Every real endpoint, including every original grouped port, and every
unused physical width are represented in the old virtual incidence frame. -/
theorem represented (x : σ → Bool) (ready : Ready e pop col code seed p bin positive site slot dummy x)
    (attach : ∀ a,host (port a) = (site (p.layout.attach a)).val) (sizes : ∀ a,width (port a) = bits a)
    (fits : ∀ i,width i < 2^w) (holes : ∀ i,i ∉ Set.range port → width i = 0) :
    Views.EndpointData p.layout (fields col fit host width) site slot port ((frame pop col).eval x) := by
  constructor
  · intro z
    simpa only [fields,Function.comp_def,original,Fin.castLEEmb_apply,Fin.val_castLE] using (ready.endpoints z).1
  · intro z
    simpa only [fields,Function.comp_def,original,Fin.castLEEmb_apply,Fin.val_castLE] using (ready.endpoints z).2
  · intro a
    simp only [fields,Function.comp_def,literal,ParseRecords.bigValue_testBit,Fin.castLEEmb_apply,Fin.val_castLE]
    rw [attach,Nat.mod_eq_of_lt ((site (p.layout.attach a)).isLt.trans_le fit)]
  · intro z
    have live := (ready.occupied (slot z)).2 ⟨z,rfl⟩
    simpa only [fields,Function.comp_def,masked,live,Bool.true_and] using ready.widths z
  · intro a
    simp only [fields,Function.comp_def,literal,ParseRecords.bigValue_testBit]
    rw [Nat.mod_eq_of_lt (fits _),sizes]
  · intro i hi
    have gone : x (col.occupied i) = false := Bool.eq_false_iff.mpr fun on => hi ((ready.occupied i).1 on)
    simp only [fields,Function.comp_def,masked,gone,Bool.false_and]
    exact zero_value w
  · intro i hi
    simp only [fields,Function.comp_def,literal,ParseRecords.bigValue_testBit]
    rw [Nat.mod_eq_of_lt (fits _),holes i hi]

end Packing.Inherited.FrozenTape.OldFields

end BorderVNP
end Computability
end OAI

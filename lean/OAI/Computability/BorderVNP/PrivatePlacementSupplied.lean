import OAI.Computability.BorderVNP.TransmissionDataSlabs
import OAI.Computability.BorderVNP.PackedCellAddresses

/-! # The supplied prefix in the actual packed network's cell-bank addresses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.PrivateBank

open Crossing CellAddresses Function
open private endRow from OAI.Computability.BorderVNP.PackedCellAddresses
open scoped Classical

variable {D C m n : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → Fin C)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- All supplied words of all cells, including each oriented crossing incidence and
each actual attached external port. -/
abbrev SuppliedWord := (c : Fin C) × Supplied N cell c

private noncomputable def rowBounded (c : Fin C) : Supplied N cell c ↪ Fin ((m+m)+n) :=
  (((endRow N cell c edgeID).trans finSumFinEquiv.toEmbedding).sumMap
    ((Embedding.subtype _).trans portID)).trans finSumFinEquiv.toEmbedding

/-- Number supplied words first by their cell and then by the native sparse cable and
port row inside that cell. -/
noncomputable def suppliedID : SuppliedWord N cell ↪ Fin (C*((m+m)+n)) where
  toFun x := finProdFinEquiv (x.1,rowBounded N cell edgeID portID x.1 x.2)
  inj' := by
    rintro ⟨c,a⟩ ⟨c',b⟩ eq
    have parts := finProdFinEquiv.injective eq
    obtain rfl : c = c' := congrArg Prod.fst parts
    exact congrArg (Sigma.mk c) ((rowBounded N cell edgeID portID c).injective (congrArg Prod.snd parts))

/-- Width of a supplied network word, on its actual owning cell. -/
def supplyWidth (x : SuppliedWord N cell) := suppliedWidth N cell x.1 x.2

/-- In the original network's physical supplied bank, the cell-keyed total is the
sum of its true crossing and argument widths. -/
theorem dataSlabs_size (c : Fin C) :
    DataSlabs.size (fun x : SuppliedWord N cell => x.1) (supplyWidth N cell) c = suppliedSize N cell c := by
  rw [DataSlabs.size, Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · simp only [supplyWidth,suppliedSize,ite_true]
    apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
    exact fun _ _ => rfl
  · intro c' _ ne; simp [ne]
  · simp

/-- The within-cell prefix in the global supplied-word table agrees exactly with the
cell-local ordinal used by the native packet-scatter and private-cell compiler. -/
theorem dataSlabs_base (c : Fin C) (a : Supplied N cell c) :
    DataSlabs.base (fun x : SuppliedWord N cell => x.1)
      ((suppliedID N cell edgeID portID).trans Fin.valEmbedding) (supplyWidth N cell) ⟨c,a⟩ =
      CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) a := by
  rw [DataSlabs.base, CellSlabs.start, Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · apply Finset.sum_congr rfl
    intro b _
    have ib : (rowBounded N cell edgeID portID c b).val = suppliedRow N cell c edgeID portID b := rfl
    have ia : (rowBounded N cell edgeID portID c a).val = suppliedRow N cell c edgeID portID a := rfl
    change (if (finProdFinEquiv (c,rowBounded N cell edgeID portID c b)).val <
      (finProdFinEquiv (c,rowBounded N cell edgeID portID c a)).val then
      (if c = c then suppliedWidth N cell c b else 0) else 0) = _
    simp only [finProdFinEquiv_apply_val, ib, ia, Nat.add_lt_add_iff_right,ite_true]
  · intro c' _ ne
    apply Finset.sum_eq_zero; intro b _
    change (if _ then (if c' = c then _ else 0) else 0) = 0
    simp [ne]
  · simp

/-- The attached external port is an actual supplied word. Distinct port indices
remain distinct even when their sites are packed into the same cell. -/
def suppliedPort : P ↪ SuppliedWord N cell where
  toFun p := ⟨cell (N.attach p),.inr ⟨p,rfl⟩⟩
  inj' := by
    intro p q h
    let port? : SuppliedWord N cell → Option P := fun x => x.2.elim (fun _ => none) (fun a => some a.val)
    exact Option.some.inj (congrArg port? h)

end Packing.Directory.PrivateBank

end BorderVNP
end Computability
end OAI

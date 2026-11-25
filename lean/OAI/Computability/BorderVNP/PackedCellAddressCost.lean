import OAI.Computability.BorderVNP.PackedCellAddressCircuit

/-! # Gate bounds for batched physical cell address allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressCircuit

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private raw wt key loc same source from OAI.Computability.BorderVNP.PackedCellAddressCircuit
open private eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame

variable {s m n C d k w : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

/-- Gate count for the site-ID lookup in the cell-placement directory. -/
def labelBound (s m n d k : ℕ) :=
  let h := Nat.clog 2 (s+((m+m)+n))
  2^h * ((d+1+k) + ((k+h)+1+d) +
    h^2*(24*((k+h)+1+d)+1) + k*(60*d+16*k+33) + h^2*(24*(k+h)+1))

/-- Including the final address sort, scan, and permutation restoring row order. -/
def gateBound (s m n C d k w : ℕ) :=
  let b := Nat.clog 2 (count s m n C)
  labelBound s m n d k + 1 + 2^b * ((k+w)*(30*k+8) + ((w+b)+1+k) +
    b^2*(24*((w+b)+1+k)+1) + w*(60*k+40*w+63) + b^2*(24*(w+b)+1))

/-- Site lookup is linear in padded row count times a polynomial in the address widths. -/
theorem labels_size : (labels F).size ≤ labelBound s m n d k := by
  have h := queries_size (layout (Fin s) (End m n)) (fun u => fixed (F.sites u))
    (fun u j => .input (F.owner u j)) (fun e j => .input (F.ptr e j)) 1 (by decide)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa only [labels,PackedLookup.lookup,labelBound,End,Fintype.card_sum,Fintype.card_fin,Nat.mul_one] using h

/-- The compiled circuit computes all offsets together within its linear-times-polylog budget. -/
theorem frame_size : (frame F).size ≤ gateBound s m n C d k w := by
  let b := Nat.clog 2 (count s m n C)
  have ke (r : Row s m n C) (j : Fin k) : (key F r j).size ≤ 1 := by
    rcases r with ((e|c)|(v|c))|(e|c) <;> exact le_rfl
  have se (e : Fin m) : (same (σ := σ) (n := n) (k := k) e).size ≤ 30*k+3 :=
    eqWord_size _ _ (fun _ => le_rfl) (fun _ => le_rfl)
  have we (r : Row s m n C) (j : Fin w) : (wt F r j).size ≤ 30*k+8 := by
    rcases r with ((e|c)|(v|c))|(((e|e)|p)|c) <;> simp only [wt,StatementCircuit.Expr.size]
    all_goals first | omega | exact (by have := se e; omega)
  have raw_size (ij : Stable.Input b k w) : (raw F ij).size ≤ 30*k+8 := by
    unfold raw
    split
    · rcases ij with ⟨u,j|j⟩
      · exact (ke _ j).trans (by omega)
      · exact we _ j
    · change 1 ≤ 30*k+8
      omega
  have h := Frame.step_size_le (labels F).withInput (raw F) _ raw_size
  simp only [Stable.Input,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,Frame.withInput_size] at h
  change (source F).size ≤ (labels F).size + 2^b*(k+w)*(30*k+8) at h
  rw [frame,Frame.select_size,Frame.subst_size]
  exact (Nat.add_le_add (h.trans (Nat.add_le_add_right (labels_size F) _)) (Stable.frame_size b k w)).trans
    (by dsimp only [gateBound,b]; ring_nf; rfl)

end Packing.CellAddressCircuit

end BorderVNP
end Computability
end OAI

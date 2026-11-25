import OAI.Computability.BorderVNP.PackedBundleSortSource
import OAI.Computability.BorderVNP.PackedStableOffsets

/-! # Computing the private placement prefix from original site owners

The segmented scan uses the same original order and constant metadata width as the
native placement pass. Unused power-of-two padding has zero width at every key.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open PackedHistogram ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork RoutingISA
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private prefix_univ from OAI.Computability.BorderVNP.PackedStableOffsets

variable {N k w : ℕ}

private abbrev Exponent (N : ℕ) := Nat.clog 2 N
private def lane (i : Fin N) : Fin (2^Exponent N) := Fin.castLE (Nat.le_pow_clog (by decide) N) i
private noncomputable def sourceBit (desc : ℕ) (r : Stable.Input (Exponent N) k w) : Expr (Fin N × Fin k) :=
  if h : r.1.val < N then r.2.elim (fun j => .input (⟨r.1.val,h⟩,j))
    (fun j => (fixed (Fin.ofNat (2^w) desc)) j) else .const false

private noncomputable def beforeScan (N k w desc : ℕ) :
    Frame (Fin N × Fin k) (Stable.Input (Exponent N) k w) :=
  (Frame.initial id).step (sourceBit desc)

/-- One shared exclusive same-owner sum per real metadata row. -/
noncomputable def descriptionPrefix (N k w desc : ℕ) : Frame (Fin N × Fin k) (Fin N × Fin w) :=
  ((Stable.frame (Exponent N) k w).subst (beforeScan N k w desc)).select fun ij => (lane ij.1,ij.2)

private theorem bit_eval (desc : ℕ) (x : Fin N × Fin k → Bool) (r : Stable.Input (Exponent N) k w) :
    (beforeScan N k w desc).eval x r = (sourceBit desc r).eval x := by
  simp only [beforeScan,Frame.step_eval,show (Frame.initial (id : Fin N × Fin k → _)).eval x = x
    from funext (Frame.initial_eval id x)]

private theorem live_key (desc : ℕ) (x : Fin N × Fin k → Bool) (i : Fin N) :
    Stable.key ((beforeScan N k w desc).eval x) (lane i) = value (fun j => x (i,j)) := by
  simp [Stable.key,bit_eval,sourceBit,lane,i.isLt,StatementCircuit.Expr.eval]

private theorem weight (desc : ℕ) (hd : desc < 2^w) (x : Fin N × Fin k → Bool) (r : Fin (2^Exponent N)) :
    Stable.weight ((beforeScan N k w desc).eval x) r = if r.val < N then desc else 0 := by
  by_cases hr : r.val < N
  · simpa only [Stable.weight,bit_eval,sourceBit,dite_eq_left hr,ite_eq_left hr,Sum.elim_inr,wordValue]
      using (fixed_value x (Fin.ofNat (2^w) desc)).trans (Nat.mod_eq_of_lt hd)
  · have zero (n : ℕ) : value (fun _ : Fin n => false) = 0 := by induction n <;> simp_all [value]
    simp [Stable.weight,bit_eval,sourceBit,hr,StatementCircuit.Expr.eval,zero]

/-- The restored scalar at row i is exactly the native prefixCounts on the same owners. -/
theorem descriptionPrefix_value (desc : ℕ) (hd : desc < 2^w) (room : 2^Exponent N*desc < 2^w)
    (x : Fin N × Fin k → Bool) (owner : ℕ → ℕ) (correct : ∀ i : Fin N, value (fun j => x (i,j)) = owner i.val)
    (i : Fin N) :
    value (fun j => (descriptionPrefix N k w desc).eval x (i,j)) =
      PrivatePlacement.prefixCounts owner desc i.val (owner i.val) := by
  let y := (beforeScan N k w desc).eval x
  have key (j : Fin N) : Stable.key y (lane j) = owner j.val := (live_key desc x j).trans (correct j)
  have weights (j) : Stable.weight y j = if j.val < N then desc else 0 := weight desc hd x j
  have fits (a : ℕ) : bucket (Stable.key y) (Stable.weight y) a < 2^w := by
    apply lt_of_le_of_lt _ room
    calc
      _ ≤ ∑ _j : Fin (2^Exponent N), desc := by
        unfold bucket
        exact Finset.sum_le_sum fun j _ => by rw [weights]; split_ifs <;> omega
      _ = _ := by simp
  simp only [descriptionPrefix,Frame.select_eval,Frame.subst_eval]
  rw [Stable.frame_value y fits (lane i),key i,PrivatePlacement.prefixCounts,
    prefix_univ (show i.val < 2^Exponent N from (lane i).isLt) (fun j => if owner j = owner i.val then desc else 0)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j.val < i.val
  · have hi := h.trans i.isLt
    have kj : Stable.key y j = owner j.val := key ⟨j.val,hi⟩
    simp [lane,Fin.lt_def,h,kj,weights,hi]
  · simp [lane,Fin.lt_def,h]

/-- Gates charged for padding, both Batcher sorts, and one segmented exclusive scan. -/
theorem descriptionPrefix_size (N k w desc : ℕ) : let b := Exponent N
    (descriptionPrefix N k w desc).size ≤ 2^b*(k+w) + 1 + 2^b *
      (((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) + w*(60*k+40*w+63) + b^2*(24*(w+b)+1)) := by
  intro b
  have bound (r : Stable.Input b k w) : (sourceBit (N:=N) desc r).size ≤ 1 := by
    rcases r with ⟨r,j|j⟩ <;> unfold sourceBit <;> split <;> rfl
  have h := Frame.step_size_le (Frame.initial (id : Fin N × Fin k → _)) (sourceBit desc) 1 bound
  simp only [Frame.initial_size,zero_add,Stable.Input,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,mul_one] at h
  rw [descriptionPrefix,Frame.select_size,Frame.subst_size]
  change (beforeScan N k w desc).size ≤ 2^b*(k+w) at h
  exact (Nat.add_le_add h (Stable.frame_size b k w)).trans_eq (Nat.add_assoc _ _ _).symm

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI

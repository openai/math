import OAI.Computability.NearSquareRoot.PhysicalWalshChildLanes
import OAI.Computability.NearSquareRoot.PhysicalWalshBank
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.FinRange

/-! # Addresses and encoded volume of recursive Walsh lanes

The parent stream has physical axes `(group, lane, record)`. Splitting keeps
`(group, record)` contiguous in each lane. Both layouts use the usual
quotient and remainder of the least significant rectangular coordinate.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.ChildLanes

open IntegerMultiplication Code

variable {A : Type} {n W R : ℕ}

/-- Group-major concatenation reads the outer and inner indices from quotient and remainder. -/
theorem flatten_rect {Z : Type} {m k : ℕ} (x : Fin m → Fin k → Z) :
    (List.ofFn (fun i => List.ofFn (x i))).flatten =
      List.ofFn (fun t : Fin (m*k) => x t.divNat t.modNat) := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext g
  apply congrArg List.ofFn
  funext j
  have h : (⟨g.val*k+j.val, by
      have ht := (finProdFinEquiv (g,j)).isLt
      change j.val + k*g.val < m*k at ht
      simpa only [Nat.mul_comm k g.val, Nat.add_comm j.val] using ht⟩ : Fin (m*k)) =
        finProdFinEquiv (g,j) := Fin.ext (by change g.val*k+j.val = j.val+k*g.val; ac_rfl)
  rw [h]
  have e := finProdFinEquiv.symm_apply_apply (g,j)
  exact (congrArg (fun p : Fin m × Fin k => x p.1 p.2) e).symm

/-- The data layout before splitting, indexed by its physical ordinal. -/
theorem stream_rect (x : Fin n → Fin W → Fin R → A) :
    stream (List.finRange n) (fun g j => List.ofFn (x g j)) =
      List.ofFn (fun t : Fin (n*W*R) => x t.divNat.divNat t.divNat.modNat t.modNat) := by
  simp only [stream, ← List.ofFn_eq_map, flatten_rect]

/-- The data layout after splitting, indexed by its lane and within-lane ordinal. -/
theorem rows_rect (x : Fin n → Fin W → Fin R → A) :
    rows (List.finRange n) (fun g j => List.ofFn (x g j)) =
      List.ofFn (fun j => List.ofFn (fun t : Fin (n*R) => x t.divNat j t.modNat)) := by
  simp only [rows, MixBankLayout.bank, List.map_ofFn, ← List.ofFn_eq_map, Function.comp_def, flatten_rect]

theorem length_stream_rect (x : Fin n → Fin W → Fin R → A) :
    (stream (List.finRange n) (fun g j => List.ofFn (x g j))).length = n*W*R := by
  rw [stream_rect, List.length_ofFn]

theorem length_rows_rect (x : Fin n → Fin W → Fin R → A) :
    (rows (List.finRange n) (fun g j => List.ofFn (x g j))).length = W := by
  rw [rows_rect, List.length_ofFn]

theorem length_lane_rect (x : Fin n → Fin W → Fin R → A) (j : Fin W) :
    ((rows (List.finRange n) (fun g j => List.ofFn (x g j)))[j.val]?.getD []).length = n*R := by
  simp only [rows_rect, List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some, List.length_ofFn]

private theorem pair_val {m k : ℕ} (i : Fin m) (j : Fin k) :
    (finProdFinEquiv (i,j)).val = i.val*k+j.val := by
  change j.val + k*i.val = _
  ac_rfl

private theorem pair_div {m k : ℕ} (i : Fin m) (j : Fin k) :
    (finProdFinEquiv (i,j)).divNat = i := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i,j))

private theorem pair_mod {m k : ℕ} (i : Fin m) (j : Fin k) :
    (finProdFinEquiv (i,j)).modNat = j := congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i,j))

/-- Splitting sends a parent ordinal to the remainder of its spectator number
and to its group-major ordinal in that lane. -/
def laneEquiv (n W R : ℕ) : Fin (n*W*R) ≃ Fin W × Fin (n*R) where
  toFun t := (t.divNat.modNat,finProdFinEquiv (t.divNat.divNat,t.modNat))
  invFun p := finProdFinEquiv (finProdFinEquiv (p.2.divNat,p.1),p.2.modNat)
  left_inv t := by
    simp only [pair_div,pair_mod]
    change finProdFinEquiv (finProdFinEquiv (finProdFinEquiv.symm t.divNat),t.modNat) = t
    rw [Equiv.apply_symm_apply]
    exact finProdFinEquiv.apply_symm_apply t
  right_inv p := by
    simp only [pair_div,pair_mod]
    change (p.1,finProdFinEquiv (finProdFinEquiv.symm p.2)) = p
    rw [Equiv.apply_symm_apply]

/-- The physical entries agree under the quotient/remainder permutation. -/
theorem get_laneEquiv (x : Fin n → Fin W → Fin R → A) (t : Fin (n*W*R)) :
    ((rows (List.finRange n) (fun g j => List.ofFn (x g j)))[(laneEquiv n W R t).1.val]?).bind
      (fun lane => lane[(laneEquiv n W R t).2.val]?) =
    (stream (List.finRange n) (fun g j => List.ofFn (x g j)))[t.val]? := by
  simp only [rows_rect,stream_rect,laneEquiv,Equiv.coe_fn_mk,List.getElem?_ofFn,
    Fin.isLt,dite_true,Option.bind_some,Fin.eta,pair_div,pair_mod]

/-- Lane `j`, group `g`, local record `b` comes from the parent ordinal
`(g*W+j)*R+b`. -/
theorem get_rect (x : Fin n → Fin W → Fin R → A) (g : Fin n) (j : Fin W) (b : Fin R) :
    ((rows (List.finRange n) (fun g j => List.ofFn (x g j)))[j.val]?).bind
      (fun lane => lane[g.val*R+b.val]?) =
    (stream (List.finRange n) (fun g j => List.ofFn (x g j)))[(g.val*W+j.val)*R+b.val]? := by
  have h := get_laneEquiv x (finProdFinEquiv (finProdFinEquiv (g,j),b))
  simpa only [laneEquiv,Equiv.coe_fn_mk,pair_div,pair_mod,pair_val] using h

/-- Framed storage for the complete rectangular input stream. -/
theorem size_stream_rect [Codec A] (x : Fin n → Fin W → Fin R → A) (w : ℕ)
    (hw : ∀ g j b, size (x g j b) ≤ w) :
    size (stream (List.finRange n) (fun g j => List.ofFn (x g j))) ≤ n*W*R*(w+1)+1 := by
  rw [stream_rect]
  apply PhysicalWalshBank.size_rows_le _ _ (fun k => hw _ _ _)

/-- Framed storage for all child rows, including every row delimiter. -/
theorem size_rows_rect [Codec A] (x : Fin n → Fin W → Fin R → A) (w : ℕ)
    (hw : ∀ g j b, size (x g j b) ≤ w) :
    size (rows (List.finRange n) (fun g j => List.ofFn (x g j))) ≤ W*(n*R*(w+1)+2)+1 := by
  rw [rows_rect]
  apply PhysicalWalshBank.size_cells_le _ _ (fun j c => hw _ _ _)

/-- For fixed `W` the forward and inverse lane shuffles both take linear
steps and live tape volume, including the two address rulers. -/
theorem rectangularTasks {I : Type} [Codec A] (n R w : I → ℕ)
    (x : (i : I) → Fin (n i) → Fin W → Fin (R i) → A)
    (hw : ∀ i g j b, size (x i g j b) ≤ w i) :
    let V i := (n i + 1)*(R i + 1)*(w i + 1)
    let h i := (tally (n i), tally (R i))
    let flat i := stream (List.finRange (n i)) (fun g j => List.ofFn (x i g j))
    let bank i := rows (List.finRange (n i)) (fun g j => List.ofFn (x i g j))
    Space.BoundedTask V V (fun i => send (h i, flat i)) (fun i => send (h i, bank i)) ∧
    Space.BoundedTask V V (fun i => send (h i, bank i)) (fun i => send (h i, flat i)) := by
  intro V h flat bank
  let l (i : I) := List.finRange (n i)
  let block (i : I) (g : Fin (n i)) (j : Fin W) := List.ofFn (x i g j)
  have lengths i (g : Fin (n i)) (_ : g ∈ l i) (j : Fin W) : (block i g j).length = R i :=
    List.length_ofFn
  have split := splitTask l block R lengths
  have merge := mergeTask l block R lengths
  simp only [l,List.length_finRange] at split merge
  have sf i : size (flat i) + (n i+1)*(R i+1) + 1 ≤ (2*W+3)*(V i+1) := by
    have s := size_stream_rect (x i) _ (hw i)
    change size (flat i) ≤ _ at s
    dsimp only [V]
    ring_nf at s ⊢
    omega
  have sb i : size (bank i) + (n i+1)*(R i+1) + 1 ≤ (2*W+3)*(V i+1) := by
    have s := size_rows_rect (x i) _ (hw i)
    change size (bank i) ≤ _ at s
    dsimp only [V]
    ring_nf at s ⊢
    omega
  exact ⟨split.bound (2*W+3) (2*W+3) sf sf, merge.bound (2*W+3) (2*W+3) sb sb⟩

end PhysicalWalsh.ChildLanes

end NearSquareRoot
end Computability
end OAI

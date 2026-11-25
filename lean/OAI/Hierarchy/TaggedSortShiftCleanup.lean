import OAI.Hierarchy.TaggedSortCutPass
import Mathlib.Tactic

namespace OAI
/-! # Leighton's two cleanup passes for a short window of mixed ranks -/

noncomputable section
namespace Hierarchy.Tagged.SortLift
open scoped Classical BigOperators

abbrev ArraySize (q B : ℕ) := q*(B+B)

def alignedKey (q B : ℕ) (pos : 0<B) (i : Fin (ArraySize q B)) : Fin q :=
  ⟨i.val/(B+B),(Nat.div_lt_iff_lt_mul (by omega)).2 i.isLt⟩

def shiftedKey (q B : ℕ) (pos : 0<B) (i : Fin (ArraySize q B)) : Fin (q+1) :=
  ⟨(i.val+B)/(B+B),(Nat.div_lt_iff_lt_mul (by omega)).2 (by
    rw [Nat.succ_mul]; have bound := i.isLt; change i.val<q*(B+B) at bound; omega)⟩

def aligned (q B : ℕ) (pos : 0<B) : Stage (ArraySize q B) := blockPass (alignedKey q B pos)
def shifted (q B : ℕ) (pos : 0<B) : Stage (ArraySize q B) := blockPass (shiftedKey q B pos)

private theorem block_width {n m H : ℕ} (pos : 0<H) (offset : ℕ)
    (g : Fin n→Fin m) (label : ∀ i,(g i).val=(i.val+offset)/H) (b : Fin m) :
    Fintype.card (Fiber g b)≤H := by
  let slot (i : Fiber g b) : Fin H := ⟨(i.val.val+offset)%H,Nat.mod_lt _ pos⟩
  have inj : Function.Injective slot := by
    intro i j same
    have divs : (i.val.val+offset)/H=(j.val.val+offset)/H := by
      rw [←label,←label,i.property,j.property]
    have rems : (i.val.val+offset)%H=(j.val.val+offset)%H := congrArg Fin.val same
    have ai := Nat.mod_add_div (i.val.val+offset) H
    have aj := Nat.mod_add_div (j.val.val+offset) H
    rw [divs,rems] at ai
    exact Subtype.ext (Fin.ext (by omega))
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective slot inj

theorem aligned_width (q B : ℕ) (pos : 0<B) (b : Fin q) : (aligned q B pos).length b≤B+B :=
  block_width (by omega) 0 (alignedKey q B pos) (fun _=>by simp [alignedKey]) b

theorem shifted_width (q B : ℕ) (pos : 0<B) (b : Fin (q+1)) : (shifted q B pos).length b≤B+B :=
  block_width (by omega) B (shiftedKey q B pos) (fun _=>rfl) b

/-- There are q aligned calls and q+1 shifted calls. Allowing both end
half-blocks a padded complete call costs just one additional block in total. -/
theorem cleanup_volume (q B : ℕ) (pos : 0<B) (nonempty : 0<q) :
    blockCount [aligned q B pos,shifted q B pos] = 2*q+1 ∧
    (aligned q B pos).blocks*(B+B)+(shifted q B pos).blocks*(B+B)≤3*ArraySize q B := by
  constructor
  · change q+(q+1+0)=2*q+1
    omega
  · change q*(B+B)+(q+1)*(B+B)≤3*(q*(B+B))
    have extra : B+B≤q*(B+B) := by
      simpa only [one_mul] using (Nat.mul_le_mul_right (B+B) (show 1≤q by omega))
    rw [Nat.succ_mul]
    omega

/-- On a cell of length 2B, a window of width B fits the aligned cell
when its initial remainder is at most B. Otherwise it fits a shifted cell.
This remains true for either clipped final half-block. -/
private theorem contains_window (B : ℕ) (pos : 0<B) (lo hi : ℕ) (small : hi≤lo+B) :
    (∀ i,lo ≤ i → i<hi → i/(B+B)=lo/(B+B)) ∨
    (∀ i,lo ≤ i → i<hi → (i+B)/(B+B)=lo/(B+B)+1) := by
  let H := B+B
  have hp : 0<H := by dsimp [H];omega
  have rem := Nat.mod_lt lo hp
  have eq := Nat.mod_add_div lo H
  rw [Nat.mul_comm H] at eq
  by_cases first : lo%H≤B
  · left;intro i low high
    change i/H=lo/H
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.succ_mul]
      dsimp [H] at eq first rem ⊢
      omega
  · right;intro i low high
    change (i+B)/H=lo/H+1
    apply Nat.div_eq_of_lt_le
    · rw [Nat.succ_mul]
      dsimp [H] at eq first rem ⊢
      omega
    · rw [Nat.succ_mul,Nat.succ_mul]
      dsimp [H] at eq first rem ⊢
      omega

/-- Both stages sort genuine blocks by the supplied key. Below any cut with
a short mixed window, their composition has an initial segment of ones. -/
theorem shifted_cleanup {α κ : Type*} [LinearOrder κ] (q B : ℕ) (pos : 0<B)
    (key : α→κ) (x : Fin (ArraySize q B)→α) (t : κ) (lo hi : ℕ)
    (small : hi≤lo+B) (before : ∀ i : Fin (ArraySize q B),i.val<lo → key (x i)<t)
    (after : ∀ i : Fin (ArraySize q B),hi ≤ i.val → ¬key (x i)<t) :
    CutPrefix ((shifted q B pos).eval key ((aligned q B pos).eval key x)) key t := by
  let g := alignedKey q B pos
  let v := shiftedKey q B pos
  rcases contains_window B pos lo hi small with left|right
  · apply keep_cut v key ((blockPass g).eval key x) t
    exact resolve_cut g key x t before after (fun i j il ih jl jh =>
      Fin.ext ((left i.val il ih).trans (left j.val jl jh).symm))
  · exact resolve_cut v key ((blockPass g).eval key x) t (before_pass g key x t before)
      (after_pass g key x t after) (fun i j il ih jl jh =>
        Fin.ext ((right i.val il ih).trans (right j.val jl jh).symm))

end Hierarchy.Tagged.SortLift

end
end OAI

import OAI.Computability.NearSquareRoot.CRTControlledFlatGate
import OAI.Computability.NearSquareRoot.CRTPositionShort

/-! # Sequential address transpositions on a flat record stream -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Packed
open IntegerMultiplication.Code IntegerMultiplication.Strip

noncomputable section

theorem prefixBit_injective (k : ℕ) : Function.Injective (prefixBit (p := k)) := by
  intro a b e
  have hb : (least a).map title = (least b).map title := by
    rw [← prefixBit_list, ← prefixBit_list, e]
  have hd : Function.Injective title := by decide
  have h := List.map_injective_iff.mpr hd hb
  exact distinct 2 k (by simpa only [least,List.reverse_reverse] using congrArg List.reverse h)

/-- A pair of little-endian positions can arrive in either order. -/
def swapFlat {k : ℕ} (pair : Fin k × Fin k) (y : Block 2 k) : Block 2 k :=
  if h : pair.1 ≠ pair.2 then
    flatGateAt (max pair.1 pair.2) (min pair.1 pair.2) (min_lt_max.mpr h) (digitGate Prod.swap) y
  else y

theorem swapFlat_of_ne {k : ℕ} (p : Fin k × Fin k) (h : p.1 ≠ p.2) (y : Block 2 k) :
    swapFlat p y =
      flatGateAt (max p.1 p.2) (min p.1 p.2) (min_lt_max.mpr h) (digitGate Prod.swap) y := by
  unfold swapFlat
  split <;> simp_all

theorem swapFlat_prefixBit {k : ℕ} (p : Fin k × Fin k) (y : Block 2 k) (j : Fin k) :
    prefixBit (swapFlat p y) j = prefixBit y (Equiv.swap p.1 p.2 j) := by
  rcases p with ⟨a,b⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [swapFlat_of_ne _ (ne_of_lt hab),flatGateAt_swap]
    simp only [max_eq_right hab.le, min_eq_left hab.le, Equiv.swap_comm b a]
  · simp [swapFlat]
  · rw [swapFlat_of_ne _ (ne_of_gt hba),flatGateAt_swap]
    simp only [max_eq_left hba.le,min_eq_right hba.le]

theorem swapFlat_involutive {k : ℕ} (p : Fin k × Fin k) : Function.Involutive (swapFlat p) := by
  intro y
  apply prefixBit_injective k
  funext j
  simp only [swapFlat_prefixBit,Equiv.swap_apply_self]

def swapFlatEquiv {k : ℕ} (p : Fin k × Fin k) : Equiv.Perm (Block 2 k) :=
  (swapFlat_involutive p).toPerm (swapFlat p)

/-- Record address read after processing each pair from head to tail. -/
def swapsFlat {k : ℕ} : List (Fin k × Fin k) → Equiv.Perm (Block 2 k)
  | [] => Equiv.refl _
  | p :: l => (swapsFlat l).trans (swapFlatEquiv p)

theorem foldl_swapFlat {k : ℕ} {A : Type*} (moves : List (Fin k × Fin k)) (f : Block 2 k → A) :
    moves.foldl (fun g p => g ∘ swapFlat p) f = f ∘ (swapsFlat moves) := by
  induction moves generalizing f with
  | nil => rfl
  | cons p l ih => exact ih (f ∘ swapFlat p)

/-- Bit lookups traverse the transpositions in the reverse order of the composed
record lookup. -/
theorem swapsFlat_prefixBit {k : ℕ} (moves : List (Fin k × Fin k)) (y : Block 2 k) (j : Fin k) :
    prefixBit (swapsFlat moves y) j = prefixBit y ((positionExchanges moves).symm j) := by
  induction moves generalizing j with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,b⟩
    change prefixBit (swapFlat (a,b) (swapsFlat l y)) j = _
    rw [swapFlat_prefixBit, ih]
    rfl

theorem swapsFlat_append {k : ℕ} (xs ys : List (Fin k × Fin k)) :
    swapsFlat (xs ++ ys) = (swapsFlat ys).trans (swapsFlat xs) := by
  induction xs with
  | nil => rfl
  | cons p l ih => ext; simp only [List.cons_append,swapsFlat,ih,Equiv.trans_apply]

theorem swapsFlat_reverse {k : ℕ} (xs : List (Fin k × Fin k)) :
    swapsFlat xs.reverse = (swapsFlat xs).symm := by
  induction xs with
  | nil => rfl
  | cons p l ih =>
    rw [List.reverse_cons,swapsFlat_append,ih]
    rfl

theorem swapsFlat_reverse_prefixBit {k : ℕ} (xs : List (Fin k × Fin k)) (y : Block 2 k) (j : Fin k) :
    prefixBit (swapsFlat xs.reverse y) j = prefixBit y (positionExchanges xs j) := by
  have h := swapsFlat_prefixBit xs ((swapsFlat xs).symm y) (positionExchanges xs j)
  simpa only [Equiv.apply_symm_apply,Equiv.symm_apply_apply,swapsFlat_reverse] using h.symm

/-- Moving complete records by an address permutation preserves the encoded tree
size, even when records have different sizes. -/
theorem stripe_count_perm {A : Type} (s : Series A) (e : Equiv.Perm A) (f : A → Tree) :
    (stripe s (f ∘ e)).count = (stripe s f).count := by
  have h : (s.explore.map e).Perm s.explore :=
    List.perm_ext_iff_of_nodup (s.nodup.map e.injective) s.nodup |>.mpr (fun x =>
      ⟨fun _ => s.complete x, fun _ => List.mem_map.mpr ⟨e.symm x,s.complete _,e.apply_symm_apply x⟩⟩)
  rw [stripe_simple,stripe_simple,Task.forest_count,Task.forest_count]
  simp only [costSum]
  have hs := (h.map (fun x => (f x).count)).sum_eq
  rw [List.map_map] at hs
  exact congrArg (fun x => s.explore.length + x + 1) hs

end
end Controlled

end NearSquareRoot
end Computability
end OAI

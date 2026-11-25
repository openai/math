import OAI.Computability.NearSquareRoot.CRTIsomorphism

/-! # Mixed-radix rank of a slowest-axis-first traversal -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxRank

/-- Position of a tuple in lexicographic traversal, with the outermost axis first. -/
def position : List ℕ → List ℕ → ℕ
  | _ :: axes, digit :: digits => digit * axes.prod + position axes digits
  | _, _ => 0

private theorem prefix_last {n : ℕ} (rad : Fin (n + 1) → ℕ) :
    CRT.«prefix» rad (Fin.last n) = ∏ i : Fin n, rad i.castSucc := by
  classical
  have h : (Finset.univ : Finset (Fin n)).map Fin.castSuccEmb = Finset.Iio (Fin.last n) := by
    ext j
    cases j using Fin.lastCases with
    | last => simp [Finset.mem_map]
    | cast i => simp [Finset.mem_map]
  rw [CRT.«prefix», ← h, Finset.prod_map]
  rfl

private theorem prefix_castSucc {n : ℕ} (rad : Fin (n + 1) → ℕ) (i : Fin n) :
    CRT.«prefix» rad i.castSucc = CRT.«prefix» (fun j : Fin n => rad j.castSucc) i := by
  unfold CRT.«prefix»
  rw [← Fin.map_castSuccEmb_Iio, Finset.prod_map]
  rfl

theorem position_ofFn_rev {d : ℕ} (rad t : Fin d → ℕ) :
    position (List.ofFn rad).reverse (List.ofFn t).reverse = CRT.rank rad t := by
  induction d with
  | zero => simp [position, CRT.rank]
  | succ n ih =>
    rw [List.ofFn_succ' rad, List.ofFn_succ' t]
    simp only [List.concat_eq_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append, position, List.prod_reverse, Fin.prod_ofFn, ih]
    conv_rhs => rw [CRT.rank, Fin.sum_univ_castSucc, prefix_last]
    simp only [prefix_castSucc, CRT.rank]
    ring

/-- Reversing the fastest-first axis list gives the scan order, with exactly the
same place values used by the scaled CRT permutation. -/
theorem position_eq_rank {α : Type*} (box : List α) (rad : α → ℕ) (t : Fin box.length → ℕ) :
    position (box.map rad).reverse (List.ofFn t).reverse =
      CRT.rank (fun i => rad (box.get i)) t := by
  simpa only [List.ofFn_comp', List.ofFn_get] using
    position_ofFn_rev (fun i => rad (box.get i)) t

end BoxRank

end NearSquareRoot
end Computability
end OAI

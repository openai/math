import OAI.Computability.BorderVNP.CubeLabelBinOrdinals
import OAI.Computability.BorderVNP.CubeLabelISAPass
import OAI.Computability.BorderVNP.CubeLabelISABins

/-! # The native trial and commit arithmetic from the semantic cache bounds -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open Cube.MeanChoice Finset
open scoped BigOperators

/-- The contiguous cable and delivery caches assign distinct physical addresses to
all visited ordinal positions. -/
theorem Frame.cacheAddr_injective (p : Frame) (separate : p.cables+p.Z^2 ≤ p.data)
    {i j : ℕ} (eq : p.cacheAddr i = p.cacheAddr j) : i = j := by
  unfold cacheAddr at eq
  split at eq <;> split at eq <;> omega

/-- Every bin address follows the immutable incidence and demand directories. -/
theorem Frame.cacheAddr_lower (p : Frame) (separate : p.cables+p.Z^2 ≤ p.data)
    (i : ℕ) : p.cables ≤ p.cacheAddr i := by unfold cacheAddr; split <;> omega

/-- Commit and trial prefixes preserve all memory below the cache. -/
theorem prefix_below (p : Frame) (b : PassBins) (addr : b.addr = p.cacheAddr)
    (separate : p.cables+p.Z^2 ≤ p.data) (commit : Bool) (m : ℕ → ℕ) (i x : ℕ)
    (hx : x < p.cables) : b.memory commit m i x = m x := by
  cases commit
  · rfl
  · exact b.image_off m i x (fun k _ eq => by
      rw [addr] at eq; have := p.cacheAddr_lower separate k; omega)

/-- The unvisited position still contains its old mean on a partially written pass. -/
theorem PassBins.before_image (b : PassBins) (m : ℕ → ℕ) (i : ℕ)
    (distinct : ∀ j < i, b.addr i ≠ b.addr j) : b.image m i (b.addr i) = m (b.addr i) :=
  b.image_off m i _ distinct

/-- Componentwise correspondence with the source traffic tables yields both the
underflow check and the word-size bound for an updated mean. -/
theorem commit_fits {C I : Type*} [DecidableEq C] [Fintype I] {z w : ℕ}
    (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1))
    (b : PassBins) (m : ℕ → ℕ) (means : ∀ j, m (b.addr (binOrdinal z j).val) = cache rows s x j)
    (before : ∀ j, b.before (binOrdinal z j).val = incidentSum rows c s x j)
    (after : ∀ j, b.after (binOrdinal z j).val =
      incidentSum rows c (insert c s) (Function.update x c v) j)
    (cap : totalWidth rows*(z+1)^2 < 2^w) (i score : ℕ) (hi : i < (z+1)^2+(z+1))
    (distinct : ∀ j < i, b.addr i ≠ b.addr j) : b.fits true w m score i := by
  let j := (binOrdinal z).symm ⟨i,hi⟩
  have ord : (binOrdinal z j).val = i := congrArg Fin.val ((binOrdinal z).apply_symm_apply _)
  have cacheEq := means j
  have old := before j
  have new := after j
  rw [ord] at cacheEq old new
  change b.before i ≤ _ ∧ _ < _
  rw [b.before_image m i distinct,cacheEq,old,new]
  constructor
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.zero_le _
  · change commit rows s x c v (cache rows s x) j < _
    rw [commit_cache]
    exact (cache_le ..).trans_lt cap

/-- Every trial prefix is a partial sum of the final nonnegative semantic score.
The final score bound therefore protects every multiply and add of the scan. -/
theorem trial_fits {C I : Type*} [DecidableEq C] [Fintype I] {z w : ℕ}
    (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1))
    (b : PassBins) (m : ℕ → ℕ) (means : ∀ j, m (b.addr (binOrdinal z j).val) = cache rows s x j)
    (after : ∀ j, b.after (binOrdinal z j).val =
      incidentSum rows c (insert c s) (Function.update x c v) j)
    (score : ℕ) (cap : score+2*(z+1)^6*(totalWidth rows)^2 < 2^w)
    (i : ℕ) (hi : i < (z+1)^2+(z+1)) : b.fits false w m score i := by
  change score+b.score m i + m (b.addr i)*b.after i < _
  rw [Nat.add_assoc,← b.score_succ]
  have leq : b.score m (i+1) ≤ b.score m ((z+1)^2+(z+1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hi) fun _ _ _ => Nat.zero_le _
  rw [pass_score_eq rows s x c v b m means after] at leq
  exact (Nat.add_le_add_left (leq.trans (scoreNat_le ..)) score).trans_lt cap

/-- At the end of a commit, each native bin contains exactly the conditional
mean after fixing the chosen label. -/
theorem commit_image_cache {C I : Type*} [DecidableEq C] [Fintype I] {z : ℕ}
    (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1))
    (b : PassBins) (m : ℕ → ℕ) (means : ∀ j, m (b.addr (binOrdinal z j).val) = cache rows s x j)
    (before : ∀ j, b.before (binOrdinal z j).val = incidentSum rows c s x j)
    (after : ∀ j, b.after (binOrdinal z j).val =
      incidentSum rows c (insert c s) (Function.update x c v) j)
    (distinct : Function.Injective b.addr) (j : Bins z) :
    b.image m ((z+1)^2+(z+1)) (b.addr (binOrdinal z j).val) =
      cache rows (insert c s) (Function.update x c v) j := by
  rw [b.image_at _ _ _ (binOrdinal z j).isLt (fun _ _ _ _ he => distinct he),means,before,after]
  exact congrFun (commit_cache rows s x c v) j

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI

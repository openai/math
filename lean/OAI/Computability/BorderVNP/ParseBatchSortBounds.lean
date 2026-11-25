import OAI.Computability.BorderVNP.ParseBatchSort
import OAI.Computability.BorderVNP.TeamSorting

/-!
# Correctness, multiplicity and size of the bit-record sort

The sorting phases retain all records, even duplicates. Padding any positive batch to
the next power of two costs less than a factor of two, so logarithmic-width records have
a Boolean gate bound linear in the batch size times a cubic logarithm.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchSort

open VPVNP VPVNP.VerifierNetwork VPVNP.RAMSort

variable {σ : Type*} [Fintype σ] {b w : ℕ}

/-- The complete bit records are in ascending numeric order after all phases. -/
theorem phases_monotone (f : Frame σ (Pins b w)) (x : σ → Bool) :
    Monotone (fun i : Fin (2 ^ b) => value (fun k => (phases b le_rfl f).eval x (i,k))) := by
  rw [phases_correct]
  exact sort_monotone ..

/-- All sorted bit records form a permutation of the original records, including
the full payload fields, padding rows, and all multiplicities. -/
theorem phases_perm (f : Frame σ (Pins b w)) (x : σ → Bool) :
    (List.ofFn (fun i : Fin (2 ^ b) => fun k => (phases b le_rfl f).eval x (i,k))).Perm
      (List.ofFn (fun i : Fin (2 ^ b) => fun k => f.eval x (i,k))) := by
  let raw := fun i : Fin (2 ^ b) => fun k => f.eval x (i,k)
  have h := sort_perm b true (fun i => value (raw i))
  change (List.ofFn (sort b true (fun i => value (fun k => f.eval x (i,k))))).Perm _ at h
  rw [← phases_correct] at h
  have hbits := h.map (Function.invFun (@value w))
  have hinv (v : Fin w → Bool) : Function.invFun value (value v) = v :=
    Function.leftInverse_invFun (value_injective w) v
  simpa only [List.map_ofFn, Function.comp_def, hinv, raw] using hbits

/-- Explicit gate overhead for an arbitrary positive number of rows, including
power-of-two padding. -/
theorem padded_size (k : ℕ) (hk : 0 < k) (f : Frame σ (Pins (Nat.clog 2 k) w)) :
    (phases (Nat.clog 2 k) le_rfl f).size ≤
      f.size + 50 * k * (Nat.clog 2 k) ^ 2 * (w + 1) := by
  apply (phases_size _ le_rfl f).trans
  apply Nat.add_le_add_left
  calc
    _ ≤ (Nat.clog 2 k) ^ 2 * (2 * k * (25 * (w + 1))) := by
      gcongr
      · exact (TeamSorting.padding_lt_twice hk).le
      · omega
    _ = _ := by ring

/-- For a sort of at most `A*n*r` rows with `B(1+⌈log₂(2nr)⌉)` bits per row, the
absolute overhead is bounded by `C*n*r*(1+⌈log₂(2nr)⌉)^3` with the displayed constant. -/
theorem batch_size (n r A B k w : ℕ) (hk : 0 < k) (hm : k ≤ A * (n*r))
    (hw : w ≤ B * (Nat.clog 2 (2*n*r) + 1)) (f : Frame σ (Pins (Nat.clog 2 k) w)) :
    (phases (Nat.clog 2 k) le_rfl f).size ≤ f.size +
      (50*A*(Nat.clog 2 A+1)^2*(B+1)) * (n*r) * (Nat.clog 2 (2*n*r)+1)^3 := by
  apply (padded_size k hk f).trans
  apply Nat.add_le_add_left
  let L := Nat.clog 2 (2*n*r)
  have hn : n*r ≤ 2*n*r := by nlinarith
  have hlog : Nat.clog 2 k ≤ Nat.clog 2 A + L := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    rw [pow_add]
    exact hm.trans (Nat.mul_le_mul (Nat.le_pow_clog (by decide) A)
      (hn.trans (Nat.le_pow_clog (by decide) _)))
  have hlog' : Nat.clog 2 k ≤ (Nat.clog 2 A + 1) * (L + 1) := hlog.trans (by nlinarith)
  have hw' : w + 1 ≤ (B + 1) * (L + 1) := by change w ≤ B * (L + 1) at hw; nlinarith
  calc
    _ ≤ 50 * (A * (n*r)) * ((Nat.clog 2 A + 1) * (L+1)) ^ 2 * ((B+1) * (L+1)) := by gcongr
    _ = _ := by dsimp [L]; ring

end ParseBatchSort

end BorderVNP
end Computability
end OAI

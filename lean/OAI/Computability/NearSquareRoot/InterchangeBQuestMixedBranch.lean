import OAI.Computability.NearSquareRoot.InterchangeBQuestMixed
import OAI.Computability.NearSquareRoot.InterchangeBQuestBranch

/-! # Width dispatch for mixed-volume recursive interchanges

The header scan and the bounded-width leaf fit the ordinary parent volume.
A wide request enters its recursive program with the original data and
return-depth caps, including the logarithmic allowance on full-volume calls.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  NearSquareRoot.Space NearSquareRoot.InterchangeSpace

variable {I Y : Type} {b : ℕ} {childJob : Job Y}

/-- Physically choose between the finite leaf and the mixed-volume recursive
command by reading the width in the request's header. -/
theorem branch_mixed (xs : I → Request b) (n : ℕ) (hb : 2 ≤ b)
    (valid : ∀ i, Admissible (xs i))
    (records : Manifest _ (fun i => (xs i).recordWidth) (fun i => (xs i).contents))
    (small full : {i // n < (xs i).width} → List Y)
    (step : InterchangeSpace.Mixed childJob small full (fun q => (xs q.val).recordVolume)
      (fun q => (job b).issue (xs q)) (fun q => (job b).reply (xs q))) :
    InterchangeSpace.Mixed childJob (branch_ledger xs n small) (branch_ledger xs n full)
      (fun i => (xs i).recordVolume) ((job b).issue ∘ xs) ((job b).reply ∘ xs) := by
  let V (i : I) := (xs i).recordVolume
  have ripe := ripe_volume xs hb valid (w:=fun i => (V i : ℝ)) (fun i => by
    exact_mod_cast (xs i).rows_le_recordVolume)
  have stored := issue_volume xs hb valid records
  have solid (i : I) : solidShape (xs i) :=
    ⟨fun d hd => (valid i d (List.mem_append_left _ (List.mem_append_left _ hd))).1,
     fun d hd => (valid i d (List.mem_append_left _ (List.mem_append_right _ hd))).1,
     fun d hd => (valid i d (List.mem_append_right _ hd)).1⟩
  obtain ⟨tag,A,start⟩ := prepare_width_dispatch xs n (w:=V) ripe stored
  obtain ⟨leaf,B,stop⟩ := leaf_of_issue_volume xs n (w:=V) (by omega) solid stored
  obtain ⟨wide,C,H,body⟩ := step.build
  let K := (2*A+2*B+C+10)
  refine ⟨Space.dispatch tag leaf wide,K,H,?_⟩
  intro i parent env time data depth calls deck base hd
  let S := branch_ledger xs n small i
  let F := branch_ledger xs n full i
  let total := ((S++F).map time).sum
  let cap := base + max (K*V i + childPeak data S) (H*(Nat.log 2 (V i)+1)+childPeak data F)
  let ret := max (K*V i + childPeak depth S) (H*(Nat.log 2 (V i)+1)+childPeak depth F)
  have hp : 1 ≤ V i := by
    have pos : (1 : ℝ) ≤ (V i : ℝ) := ripe.1 i
    exact_mod_cast pos
  have a := Nat.le_mul_of_pos_right A (by omega : 0 < V i)
  have b' := Nat.le_mul_of_pos_right B (by omega : 0 < V i)
  have major : A*(V i+1)+B*(V i+1)+C*V i+10 ≤ K*V i := by
    simp only [K,Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.mul_assoc] at *
    omega
  have dc : base + K*V i + childPeak data S ≤ cap := by
    dsimp only [cap]
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left (le_max_left ..) base
  have rc : K*V i + childPeak depth S ≤ ret := le_max_left ..
  have target := start leaf wide i (parent::env) deck base (B*(V i+1)+C*V i+total) cap ret
    hd (by omega) (by omega) (fun h => by
      have ok := stop ⟨i,h⟩ (parent::env) deck base hd
      exact ok.mono (by dsimp only at *; omega) (by dsimp only at *; omega)
        (by dsimp only at *; omega)) (fun h => by
      have sc : S = small ⟨i,h⟩ := by simp only [S,branch_ledger,h,↓reduceDIte]
      have fc : F = full ⟨i,h⟩ := by simp only [F,branch_ledger,h,↓reduceDIte]
      have callWide := calls
      change ∀ y ∈ S ++ F, _ at callWide
      rw [sc,fc] at callWide
      have ok := body ⟨i,h⟩ parent env time data depth callWide deck base hd
      change BoundedFits _ _ _ _ (C*V i + ((small ⟨i,h⟩ ++ full ⟨i,h⟩).map time).sum)
        (base + max (C*V i + childPeak data (small ⟨i,h⟩))
          (H*(Nat.log 2 (V i)+1)+childPeak data (full ⟨i,h⟩)))
        (max (C*V i + childPeak depth (small ⟨i,h⟩))
          (H*(Nat.log 2 (V i)+1)+childPeak depth (full ⟨i,h⟩))) at ok
      rw [← sc,← fc] at ok
      apply ok.mono
      · dsimp only [total]; omega
      · exact Nat.add_le_add_left (max_le_max_right _ (by omega)) base
      · exact max_le_max_right _ (by omega))
  change BoundedFits _ _ _ _ (K*V i+total) cap ret
  exact target.mono (by omega) le_rfl le_rfl

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI

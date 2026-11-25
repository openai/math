import OAI.Computability.BorderVNP.RoutingISAPaddingCommon
import OAI.Computability.BorderVNP.RoutingISAPaddingOffsets
import OAI.Computability.BorderVNP.RoutingISABlockAppend

/-! # Checking the padding on one physical incident block

The non-self branch uses the two leg-total addresses in the initialized frame.
After both reads it scans the remaining interval through the native memory-load opcode.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- The literal non-self branch of the partner loop in `checkPadding`. -/
def paddingPartner : Code := .block (paddingStartSteps ++ [zeroScan])

private theorem paddingPartner_iff {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s m es t mt} : Runs pub macros paddingPartner s m es t mt ↔
      Runs pub macros (.seq paddingStartBlock zeroScan) s m es t mt :=
  Runs.block_append_iff (a := paddingStartSteps) (b := [zeroScan])
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

private theorem scan_keeps {w : ℕ} {s t : Bank w} {f : BroadcastFrame} {base : ℕ}
    (inv : partnerInv f base s) (result : ZeroScanResult s t) :
    partnerInv f base t ∧ t 11 = s 11 := by
  refine ⟨partnerInv_of_preserves inv fun j hj => congrArg Fin.val (result.2 j ?_ ?_ ?_),
    result.2 11 (by decide) (by decide) (by decide)⟩
  · rcases hj with low | rfl | rfl
    · omega
    · decide
    · decide
  all_goals rintro rfl; revert hj; decide

/-- A normal native return of the padding branch is equivalent to all words in
the unoccupied suffix being zero. The time bound charges every probe and loop test. -/
theorem paddingPartner_check {w : ℕ} (f : BroadcastFrame) (base : ℕ)
    (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (pairs : ∀ i < f.teams, i ≠ f.team →
      pairIndex base f.teams f.team i < 2^w ∧ pairIndex base f.teams i f.team < 2^w)
    (space : ∀ i < f.teams, i ≠ f.team → f.paddingFrom (readings m) base i ≤ f.capacity) :
    PartnerCheck pub macros m f.teams f.team
      (paddingStartBlock.slots + f.capacity * (zeroScanBody.slots + 1) + 1) paddingPartner
      (partnerInv f base) (fun i => f.ZeroFrom (readings m) (f.paddingFrom (readings m) base i) i) := by
  let ok := fun i => f.ZeroFrom (readings m) (f.paddingFrom (readings m) base i) i
  let cost := paddingStartBlock.slots + f.capacity * (zeroScanBody.slots + 1) + 1
  have both (i : ℕ) (hi : i < f.teams) (hn : i ≠ f.team) (s : Bank w)
      (inv : partnerInv f base s) (partner : (s 11).val = i) :
      (ok i → ∃ es t, Runs pub macros paddingPartner s m es t m ∧ traceCost es ≤ cost ∧
        partnerInv f base t ∧ t 11 = s 11) ∧
      (∀ {es t mt}, Runs pub macros paddingPartner s m es t mt →
        mt = m ∧ partnerInv f base t ∧ t 11 = s 11 ∧ ok i) := by
    have fields := inv
    obtain ⟨⟨_,_,team,teams,_,_,head,cap,_,_,_⟩,baseReg⟩ := fields
    have tableBase : readings s 19 = base := baseReg
    have partner' : readings s 11 = i := partner
    have offset : paddingOffset (readings m) (readings s) = f.paddingFrom (readings m) base i := by
      simp only [paddingOffset, BroadcastFrame.paddingFrom, head, tableBase, teams, team, partner']
    obtain ⟨forward,reverse⟩ := pairs i hi hn
    have safe := paddingStart_safe (readings pub) (readings m) (readings s)
      (by simpa only [tableBase,teams,team,partner'] using forward)
      (by simpa only [tableBase,teams,team,partner'] using reverse)
      (by simpa only [offset,cap] using space i hi hn) (s 7).isLt
    obtain ⟨fs,u,first,cost₁,value⟩ := paddingStartBlock.runReadOnly pub macros m s safe
    have preserve (j : Reg) (h₁ : j ≠ 10) (h₂ : j ≠ 13) (h₃ : j ≠ 16)
        (h₄ : j ≠ 17) (h₅ : j ≠ 18) : u j = s j :=
      Fin.ext ((congrFun value j).trans (paddingStart_preserves _ _ _ j h₁ h₂ h₃ h₄ h₅))
    have mid : partnerInv f base u := by
      apply partnerInv_of_preserves inv
      intro j hj
      apply congrArg Fin.val (preserve j ?_ ?_ ?_ ?_ ?_)
      all_goals rintro rfl; revert hj; decide
    have p₁₁ := preserve 11 (by decide) (by decide) (by decide) (by decide) (by decide)
    have u₁₁ : (u 11).val = i := p₁₁ ▸ partner
    have u₇ : (u 7).val = f.capacity :=
      (congrArg Fin.val (preserve 7 (by decide) (by decide) (by decide) (by decide) (by decide))).trans cap
    have u₁₀ : (u 10).val = f.paddingFrom (readings m) base i :=
      (congrFun value 10).trans ((paddingStart_cursor _ _ _).trans offset)
    have bounds : (u 10).val ≤ (u 7).val := by simpa only [u₁₀,u₇] using space i hi hn
    have room : ZeroScanRoom w (readings pub) (readings m) (u 11).val (u 10).val (u 7).val := by
      rw [u₁₁,u₇]
      exact scanRoom image fit hi hn _
    have zeros : ok i ↔ ∀ j, (u 10).val ≤ j → j < (u 7).val →
        (m (zeroScanAddr (readings pub) (readings m) (u 11).val j)).val = 0 := by
      simp only [ok, BroadcastFrame.ZeroFrom, readings, u₁₁, u₁₀, u₇, scanAddr_eq image]
    constructor
    · intro good
      obtain ⟨gs,t,second,cost₂,result⟩ := zeroScan_run pub macros m u mid.1.1 mid.1.2.1
        bounds room (zeros.mp good)
      obtain ⟨post,p₁₁'⟩ := scan_keeps mid result
      refine ⟨_,t,paddingPartner_iff.mpr (first.seq second),?_,post,p₁₁'.trans p₁₁⟩
      rw [u₇] at cost₂
      have bound := Nat.mul_le_mul_right (zeroScanBody.slots + 1) (Nat.sub_le f.capacity (u 10).val)
      change traceCost (fs ++ gs) ≤ paddingStartBlock.slots + f.capacity * (zeroScanBody.slots + 1) + 1
      rw [traceCost, VPVNP.RAMBuckets.cost_append]
      change traceCost fs + traceCost gs ≤ _
      omega
    · intro es t mt run
      obtain ⟨v,mv,_,_,_,init,tail⟩ := Runs.seq_iff.mp (paddingPartner_iff.mp run)
      obtain ⟨_,hu,hm⟩ := first.unique_of_deterministic (by decide) init
      rw [← hu, ← hm] at tail
      obtain ⟨memory,result,good⟩ := zeroScan_sound pub macros m u mid.1.1 mid.1.2.1 bounds room tail
      obtain ⟨post,p₁₁'⟩ := scan_keeps mid result
      exact ⟨memory,post,p₁₁'.trans p₁₁,zeros.mpr good⟩
  exact ⟨fun i hi hn s inv h => (both i hi hn s inv h).1,
    fun i hi hn s inv h => (both i hi hn s inv h).2⟩

end RoutingISA

end BorderVNP
end Computability
end OAI

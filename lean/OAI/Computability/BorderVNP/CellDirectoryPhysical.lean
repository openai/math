import OAI.Computability.BorderVNP.CellDirectoryRuntime
import OAI.Computability.BorderVNP.CellPrivateBudget
import OAI.Computability.BorderVNP.RoutingISACompactPacket

/-! # Physical input and tape allowances for a sparse cell contraction -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open Filter TeamScales CellMacro CellMacro.Generator RoutingISA

private theorem width_le_input {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : a ≤ 1) :
    width n a ≤ n := by
  have h := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n) ha)
  simpa only [width,Real.rpow_one,Nat.floor_natCast] using h

/-- Space and time at the actual word interface for a cell with the given local load.
Any additional private translation uses its own measured clock in this statement. -/
theorem eventually_compiled_load_log (A B j : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r M E w p : ℕ, 1 ≤ r →
      (r:ℝ) ≤ 2^((n:ℝ)^ω) → M ≤ width n (1/5) → E ≤ width n (1/4) → 0 < w → w ≤ n →
      ∀ D : Directory, D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
      D.records.length ≤ 4*(M+E+1)^3 → D.reportedCounts.length ≤ 4*(M+E+1)^3 →
      ∀ (payload : List Bool) (extra : ℕ),
      payload.length ≤ B*((M+1)^2+E+1)*(logWidth r n+1)^j →
      extra ≤ B*(M+E+1)^96*(logWidth r n+1)^j →
      (CompactFrame.pack w payload).length ≤ width n (1/2) ∧
      2*(3*((CompactFrame.pack w payload).length*w) + generatedWork (D.program p)+extra) ≤ n^25 := by
  obtain ⟨C,k,_,runtime⟩ := directory_runtime_polynomial A
  obtain ⟨ω,hω,room⟩ := eventually_private_budget (max k j)
  refine ⟨ω,hω,?_⟩
  filter_upwards [room (B+C),eventually_ge_atTop 1] with n budget hn
  intro r M E w p hr hrω hM hE hw hwn D st hf hc hg payload extra hlen he
  have hmn := hM.trans (width_le_input hn (by norm_num))
  have hen := hE.trans (width_le_input hn (by norm_num))
  have run := runtime n M E p hmn hen D st hf hc hg
  let L := (logWidth r n+1)^(max k j)
  have hp (d : ℕ) (hd : d ≤ max k j) : (n.size+1)^d ≤ L :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ (size_le_logWidth n r hr)) d).trans
      (Nat.pow_le_pow_right (by omega) hd)
  have hsmall : (logWidth r n+1)^j ≤ L := Nat.pow_le_pow_right (by omega) (le_max_right ..)
  have hbig := hp k (le_max_left ..)
  have hpre := hlen.trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_add_right B C)) hsmall)
  let T := (M+E+1)^96*L
  have hclock : generatedWork (D.program p) ≤ C*T := by
    rw [show C*T = C*(M+E+1)^96*L from (Nat.mul_assoc ..).symm]
    exact run.trans (Nat.mul_le_mul (Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) (by decide))) hbig)
  have hmore : extra ≤ B*T := by
    rw [show B*T = B*(M+E+1)^96*L from (Nat.mul_assoc ..).symm]
    exact he.trans (Nat.mul_le_mul_left _ hsmall)
  have hwork : generatedWork (D.program p)+extra ≤ (B+C)*(M+E+1)^96*L := by
    rw [Nat.mul_assoc,Nat.add_mul]
    change _ ≤ B*T+C*T; omega
  obtain ⟨hq,ht⟩ := budget r M E w hr hrω hM hE hw hwn payload _ hpre hwork
  exact ⟨hq,by simpa only [Nat.add_assoc] using ht⟩

/-- Specialize the input and translation costs to a polynomial in the binary input length. -/
theorem eventually_compiled_load (A B j : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r M E w p : ℕ, 1 ≤ r →
      (r:ℝ) ≤ 2^((n:ℝ)^ω) → M ≤ width n (1/5) → E ≤ width n (1/4) → 0 < w → w ≤ n →
      ∀ D : Directory, D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
      D.records.length ≤ 4*(M+E+1)^3 → D.reportedCounts.length ≤ 4*(M+E+1)^3 →
      ∀ (payload : List Bool) (extra : ℕ),
      payload.length ≤ B*((M+1)^2+E+1)*(n.size+1)^j →
      extra ≤ B*(M+E+1)^96*(n.size+1)^j →
      (CompactFrame.pack w payload).length ≤ width n (1/2) ∧
      2*(3*((CompactFrame.pack w payload).length*w) + generatedWork (D.program p)+extra) ≤ n^25 := by
  obtain ⟨ω,hω,hp⟩ := eventually_compiled_load_log A B j
  refine ⟨ω,hω,?_⟩
  filter_upwards [hp] with n hn
  intro r M E w p hr hrω hM hE hw hwn D st hf hc hg payload extra hlen he
  have h := Nat.pow_le_pow_left (Nat.succ_le_succ (size_le_logWidth n r hr)) j
  exact hn r M E w p hr hrω hM hE hw hwn D st hf hc hg payload extra
    (hlen.trans (Nat.mul_le_mul_left _ h)) (he.trans (Nat.mul_le_mul_left _ h))

end CellSparse

namespace RoutingISA.CompactMachine

open Filter TeamScales CellSparse CellMacro CellMacro.Generator

/-- The concrete serialized call with its initial boundary literals meets both machine limits. -/
theorem eventually_serialized_clock (A : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r M E w : ℕ, 1 ≤ r →
      (r:ℝ) ≤ 2^((n:ℝ)^ω) → M ≤ width n (1/5) → E ≤ width n (1/4) → 0 < w → w ≤ n →
      ∀ c : CellInput, c.external.length ≤ E → c.directory.StaticBounds A M →
      c.directory.CompactFields c.privateWires (4*(M+E+1)^3) →
      c.directory.records.length ≤ 4*(M+E+1)^3 → c.directory.reportedCounts.length ≤ 4*(M+E+1)^3 →
      (CompactFrame.pack w (serialized 8 c.stmt)).length ≤ width n (1/2) ∧ 2*c.allowance w 8 ≤ n^25 := by
  obtain ⟨P,_,syntaxBound⟩ := uniform_program_input_size A
  obtain ⟨ω,hω,hp⟩ := eventually_compiled_load A (P+111) 1
  refine ⟨ω,hω,?_⟩
  filter_upwards [hp,eventually_ge_atTop 1] with n hn hn1
  intro r M E w hr hrω hM hE hw hwn c he st hf hc hg
  let s := c.directory.program c.privateWires
  have hmn := hM.trans (width_le_input hn1 (by norm_num))
  have hen := hE.trans (width_le_input hn1 (by norm_num))
  have hs := (syntaxBound n M E c.privateWires c.directory hmn hen st hf).2
  let Y := (M+1)^2+E+1
  let L := n.size+1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hY : (M+1)^2 ≤ Y := by dsimp [Y]; omega
  have hEY : E ≤ Y := by dsimp [Y]; omega
  have hEL : c.external.length ≤ Y*L := (he.trans hEY).trans (Nat.le_mul_of_pos_right _ hL)
  have hsize : (serialized 8 c.stmt).length ≤ (P+111)*Y*L^1 := by
    rw [CellInput.stmt,serialized_withExternal,List.length_append,length_externalRecords,pow_one,Nat.mul_assoc,Nat.add_mul]
    have hb := hs.trans (Nat.mul_le_mul_right L (Nat.mul_le_mul_left P hY))
    rw [Nat.mul_assoc] at hb
    omega
  have hX : 1 ≤ M+E+1 := by omega
  have hX' : M+E+1 ≤ (M+E+1)^96 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ 96 by decide)
  have he' : c.external.length ≤ (M+E+1)^96*L := (he.trans (show E ≤ M+E+1 by omega)).trans
    (hX'.trans (Nat.le_mul_of_pos_right _ hL))
  have hm : 111*c.external.length ≤ (P+111)*(M+E+1)^96*L^1 := by
    rw [pow_one,Nat.mul_assoc]; exact Nat.mul_le_mul (Nat.le_add_left ..) he'
  obtain ⟨hq,ht⟩ := hn r M E w c.privateWires hr hrω hM hE hw hwn c.directory st hf hc hg _ _ hsize hm
  refine ⟨hq,?_⟩
  have hgen := scanCost_withExternal c.external s (clocks 8) 8 []
  obtain ⟨hslen,hbudget⟩ := byteCosts_withExternal c.external s []
  change scanCost (jobs (clocks 8) 8 c.stmt []) = 104*c.external.length + scanCost _ at hgen
  change (stream (c.stmt.expand [])).length = 2*c.external.length + work s [] at hslen
  change budget (c.stmt.expand []) = 3*c.external.length + budget (s.expand []) at hbudget
  unfold CellInput.allowance
  rw [hgen,hslen,hbudget]
  change 2*(3*((CompactFrame.pack w (serialized 8 c.stmt)).length*w)+generatedWork s+111*c.external.length) ≤ n^25 at ht
  unfold generatedWork at ht
  omega

end RoutingISA.CompactMachine

end BorderVNP
end Computability
end OAI

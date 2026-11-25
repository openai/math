import OAI.Hierarchy.DescentResetRateNumbers
import OAI.Hierarchy.DescentRoundQuota
import OAI.Hierarchy.DescentCapacityCalendar
import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentRotorFamily
import OAI.Hierarchy.DescentResetGroupingBounds
import OAI.Hierarchy.DescentResetSplicePrice
import OAI.Hierarchy.DescentHostDegree

namespace OAI
/-! # Fixed ordinary and reset parameters in the order required by the compiler -/

namespace Hierarchy.DescentCompiler
open DescentHostDegree DescentRotor DescentMixedRouter DescentResetInvoice DescentBaseProfile DescentColonies
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open scoped Classical BigOperators

theorem reset_recipe_allocations (h C f B hist : ℕ) (old : hist≤B) :
    let g:=reserveGain h C f
    f≤g ∧
    6*(2+rotorRate h C)*((2:ℝ)^f*B)+hist≤(2:ℝ)^g*B ∧
    18*((2:ℝ)^f*B)+hist≤(2:ℝ)^g*B ∧
    3*((2:ℝ)^g*B)/256+hist≤(2:ℝ)^g*B := by
  let A:=max 19 (6*(2+21*((2*h+4)*(2*h*C+2)))+1)
  let g:=reserveGain h C f
  have nineteen : 19≤A := le_max_left ..
  have rot : 6*(2+21*((2*h+4)*(2*h*C+2)))+1≤A := le_max_right ..
  have exp : (2:ℕ)^f*A≤2^g := by
    change 2^f*A≤2^(f+Nat.clog 2 A)
    rw [pow_add]
    exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
  have e : (2:ℝ)^f*A≤(2:ℝ)^g := by exact_mod_cast exp
  have boundNonneg : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
  have pay := mul_le_mul_of_nonneg_right e boundNonneg
  have one : (1:ℝ)≤2^f := one_le_pow₀ (by norm_num)
  have source : (B:ℝ)≤2^f*B := by simpa using mul_le_mul_of_nonneg_right one boundNonneg
  have stored : (hist:ℝ)≤2^f*B := (Nat.cast_le.mpr old).trans source
  have t : (19:ℝ)≤A := by exact_mod_cast nineteen
  have hRate : 6*(2+rotorRate h C)+1≤(A:ℝ) := by
    unfold rotorRate; exact_mod_cast rot
  have bill (s : ℝ) (hs : s+1≤(A:ℝ)) : s*(2^f*B)+hist≤(2:ℝ)^g*B := calc
    _ ≤ (s+1)*(2^f*B) := by nlinarith only [stored]
    _ ≤ A*(2^f*B) := mul_le_mul_of_nonneg_right hs (mul_nonneg (zero_le_one.trans one) boundNonneg)
    _ ≤ _ := by simpa only [mul_comm,mul_assoc,mul_left_comm] using pay
  have high := bill 18 (by linarith only [t])
  refine ⟨Nat.le_add_right ..,bill _ hRate,high,?_⟩
  have b : (hist:ℝ)≤2^g*B/2 := by nlinarith only [high,stored]
  have totalNonneg : 0 ≤ (2 : ℝ)^g*B := mul_nonneg (pow_nonneg (by norm_num) g) boundNonneg
  linarith only [b,totalNonneg]

theorem reset_allocations (h C f B hist : ℕ) (old : hist≤B) :
    let g:=reserveGain h C f
    f≤g ∧
    3*(2+rotorRate h C)*((2:ℝ)^f*B)+hist≤(2:ℝ)^g*B ∧
    9*((2:ℝ)^f*B)+hist≤(2:ℝ)^g*B ∧
    3*((2:ℝ)^g*B)/256+hist≤(2:ℝ)^g*B := by
  obtain ⟨depth,rotor,rows,hub⟩:=reset_recipe_allocations h C f B hist old
  have base : 0≤(2:ℝ)^f*B := by positivity
  have cost : 0≤(2+rotorRate h C)*((2:ℝ)^f*B) := by unfold rotorRate;positivity
  exact ⟨depth,by nlinarith only [rotor,cost],by linarith only [rows,base],hub⟩

/-- The fixed host degree and rotor multiplicity are obtained *before* the
number of subrounds. The required order of the rotor is selected afterwards
at the actual degree at the end of those subrounds. -/
theorem common_menu {F : Type} [Field F] (family : SpectralFamily F)
    {ρ : ℝ} (nonneg : 0≤ρ) (shrink : ρ<1) :
    ∃ (h C t n : ℕ) (board : Graph n h) (bits f g : ℕ), 0<t ∧
      reentryRate h C*ρ^t≤1/2 ∧ 4*quota t≤2^n ∧ 0<bits ∧
      (∀π : Equiv.Perm (Fin (2^n)), Configures F board.arcs C bits π) ∧
      (2^n)^2*bits≤2^f ∧
      128*resetTail f+4*(quota t:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops (atRound t) (2^n):ℝ) ∧
      f≤g ∧ g=reserveGain h C f := by
  obtain ⟨h,C,hh,boards⟩ := rotors_of_family family
  obtain ⟨t,ht,paid,n₀,enough⟩ := choose_reentry_phases h C nonneg shrink quota
  obtain ⟨n,hn,board,m,conf⟩ := boards n₀
  obtain ⟨f,power,tail⟩ := grouping_for_nonhub (quota t) (atRound t) (2^n) (m+1)
  exact ⟨h,C,t,n,board,m+1,f,reserveGain h C f,ht,paid,enough n hn,Nat.succ_pos _,
    conf _ (Nat.le_succ _),power,tail,Nat.le_add_right ..,rfl⟩

end Hierarchy.DescentCompiler

end OAI

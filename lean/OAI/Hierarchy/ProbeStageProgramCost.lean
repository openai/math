import OAI.Hierarchy.ProbeStageProgramRun
import OAI.Hierarchy.ProbeStageHistoryCost

namespace OAI
/-! # Separating the actual native scan and saturation costs -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM
open Finset
open scoped BigOperators

def rowScans (h d j i : ℕ) (m : Memory (wordBits h d copies)) :=
  Record.scans (recordAdvice h d j) (recordScratch h d j) (recordRow h d j i) m

def rowClears (h d j i : ℕ) (m : Memory (wordBits h d copies)) :=
  Record.clears (recordAdvice h d j) (recordScratch h d j) (recordRow h d j i) m

def prior (h d j : ℕ) (m : Memory (wordBits h d copies)) (i : ℕ) :=
  records h d j (result (prepareRows h d j) m) i

def levelScans (h d j : ℕ) (m : Memory (wordBits h d copies)) :=
  ∑ i ∈ range (2^h),rowScans h d j i (prior h d j m i)

def levelClears (h d j : ℕ) (m : Memory (wordBits h d copies)) :=
  ∑ i ∈ range (2^h),rowClears h d j i (prior h d j m i)

theorem level_clock (h d j : ℕ) (m : Memory (wordBits h d copies)) :
    levelTicks h d j m≤5808*2^h+100*levelScans h d j m+18*levelClears h d j m := by
  let n := 2^h
  have constant := Nat.mul_le_mul_left n (show 1000+82*fieldChunks h≤4936 by
    have lim := (chunks_cover h).2.2
    omega)
  have external := control_clock h d j
  have nr : 1≤n := Nat.two_pow_pos _
  change clock (prepareRows h d j)+(∑ i ∈ range n,
    (1000+82*fieldChunks h+100*rowScans h d j i (prior h d j m i)+
      18*rowClears h d j i (prior h d j m i)))+clock (writeRows h d j)≤_
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,Nat.cast_id,← mul_sum]
  rw [← Nat.mul_add n 1000 (82*fieldChunks h)]
  change clock (prepareRows h d j)+(n*(1000+82*fieldChunks h)+100*levelScans h d j m+
    18*levelClears h d j m)+clock (writeRows h d j) ≤ _
  change clock (prepareRows h d j)+clock (writeRows h d j)≤56+816*n at external
  change _≤5808*n+_+_
  omega

def allScans (h d : ℕ) (m : Memory (wordBits h d copies)) :=
  ∑ j∈range (rounds d),levelScans h d j (images h d m j)

def allClears (h d : ℕ) (m : Memory (wordBits h d copies)) :=
  ∑ j∈range (rounds d),levelClears h d j (images h d m j)

/-- Only actual slow-path probes and actual visited occurrences are charged
in addition to the fixed linear cost of all rounds. -/
theorem total_clock (h d : ℕ) (m : Memory (wordBits h d copies)) :
    ticks h d m ≤ (28+5808*rounds d)*2^h+100*allScans h d m+18*allClears h d m := by
  have nr : 1≤2^h := Nat.two_pow_pos _
  have root := columns_clock (2^h) (2^h) 2 ([.lit 0,.row] : List Expr) (by simp [Expr.work])
  have root_ : clock (rootPasses h)≤28*2^h := by
    change clock (rootPasses h)≤4+2*(4+2^h*(2*2+4)) at root
    omega
  have rest := Finset.sum_le_sum (s:=range (rounds d))
    (fun j _ => level_clock h d j (images h d m j))
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,Nat.cast_id,← mul_sum] at rest
  exact (add_le_add root_ rest).trans_eq (by unfold allScans allClears;ring)

def subdivisionConstant (d : ℕ) := 28+5808*rounds d+
  100*(rounds d*(2*4^rounds d))+18*(rounds d*(2*(288*d+17)*4^rounds d))

theorem linear_clock {h d : ℕ} (m : Memory (wordBits h d copies))
    (scans : allScans h d m≤rounds d*(2*4^rounds d*2^h))
    (clears : allClears h d m≤rounds d*(2*(288*d+17)*4^rounds d*2^h)) :
    ticks h d m ≤ subdivisionConstant d*2^h := by
  calc
    _ ≤ (28+5808*rounds d)*2^h+100*allScans h d m+18*allClears h d m := total_clock h d m
    _ ≤ (28+5808*rounds d)*2^h+100*(rounds d*(2*4^rounds d*2^h))+
        18*(rounds d*(2*(288*d+17)*4^rounds d*2^h)) := by gcongr
    _ = _ := by unfold subdivisionConstant;ring

/-- A readback of the actual slow-path and saturation words at each record
gives the linear bound of the linked native program on the same memory. -/
theorem linear_of_readback {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h)))
    (m : Memory (wordBits h d copies))
    (scans : ∀ (j : Fin (rounds d)) (r : Fin (2^h)),
      rowScans h d j.val r.val (prior h d j.val (images h d m j.val) r.val)≤expectedScans h d π j.val r)
    (clears : ∀ (j : Fin (rounds d)) (r : Fin (2^h)),
      rowClears h d j.val r.val (prior h d j.val (images h d m j.val) r.val)≤expectedClears h d π j.val r) :
    ticks h d m ≤ subdivisionConstant d*2^h := by
  apply linear_clock
  · apply le_trans _ (scans_history h d hd π)
    apply Finset.sum_le_sum
    intro j hj
    unfold levelScans
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum (fun r _ => scans ⟨j,mem_range.mp hj⟩ r)
  · apply le_trans _ (clears_history h d hd π)
    apply Finset.sum_le_sum
    intro j hj
    unfold levelClears
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum (fun r _ => clears ⟨j,mem_range.mp hj⟩ r)

end Hierarchy.ProbeStage.Native

end OAI

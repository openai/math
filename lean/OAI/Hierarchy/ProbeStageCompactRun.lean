import OAI.Hierarchy.ProbeStageCompactLevel

namespace OAI
/-! # A fixed-text, linear-clock native implementation of permutation subdivision

At heights at least four, two cells of the initial zero group control a true
counted loop. Its six staging cells are cleared after every physical visit.
The full reference memory image feeds the remaining controller unchanged.
-/

namespace Hierarchy.ProbeStage.Native.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators
noncomputable section

private theorem root_program (h d : ℕ) (m : Memory (ramWidth h d)) :
    (program _ (rootPasses h)).Exec m (images h d m 0) (clock (rootPasses h)) := by
  apply program_exec
  apply columns_safe (src:=2^h) _ le_rfl
  · simp [Expr.Fits]
  · have end_ : 3*extent h d≤ heapEnd h d copies := by
      simpa only [phase,Nat.zero_mul,Nat.add_zero] using (phase_in_heap (h:=h) (copies:=copies) (Nat.zero_le (rounds d)))
    have room := (Nat.mul_le_mul_left 3 (height_extent h d)).trans_lt (end_.trans_lt (heap_room h d copies))
    change 2^h+2*2^h<2^wordBits h d copies
    omega

theorem execute_subdivision {h d : ℕ} (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h))) (raw : Memory (ramWidth h d))
    (read : ∀r : Fin (2^h),raw r.val=((π r).val : Word (ramWidth h d))) :
    let m:=inputTape h d _ raw
    (subdivision h d).Exec m (images h d m (rounds d)) (ticks h d m) := by
  let m:=inputTape h d _ raw
  change (subdivision h d).Exec m (images h d m (rounds d)) (ticks h d m)
  by_cases hh : 4≤ h
  · rw [subdivision,ite_eq_left hh]
    let bill:=fun j=>levelTicks h d j (images h d m j)+overhead h
    have period : ∀j,j<rounds d→(level h d j).Exec (images h d m j) (images h d m (j+1)) (bill j) := by
      intro k hk
      let j : Fin (rounds d):=⟨k,hk⟩
      have prior:=after_levels hd π raw read (physical_ordinal hd π) k hk.le
      obtain ⟨geom,arrays⟩:=prior.future j le_rfl
      intro P regs K M
      exact level_exec hh hd π j (images h d m k) geom prior.parent arrays (images_zero hd hh π raw read k hk.le) M
    have run : (chronological (program _ (rootPasses h)) (level h d) (rounds d)).Exec m (images h d m (rounds d))
        (clock (rootPasses h)+∑ j∈Finset.range (rounds d),bill j) :=
      chronological_exec (program _ (rootPasses h)) (level h d) m (images h d m)
      (clock (rootPasses h)) bill (root_program h d m) period
    simpa only [bill,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,
      ticks,Native.ticks,Nat.add_assoc] using @run
  · rw [subdivision,ite_eq_right hh]
    intro machine
    exact Procedure.Spec.mono (subdivision_exec h d m) (fun _ h=>h) (fun _ _ h=>h)
      (Nat.le_add_right (Native.ticks h d m) (rounds d*overhead h)) machine

theorem ticks_linear {h d : ℕ} (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h))) (raw : Memory (ramWidth h d))
    (read : ∀r : Fin (2^h),raw r.val=((π r).val : Word (ramWidth h d))) :
    ticks h d (inputTape h d _ raw)≤ constant d*2^h := by
  let m:=inputTape h d _ raw
  have end_:=after_levels hd π raw read (physical_ordinal hd π) (rounds d) le_rfl
  have old:=linear_of_readback hd π m (fun j=>end_.scans j j.isLt) (fun j=>end_.clears j j.isLt)
  have overhead_le : overhead h≤(48+stageClock+unstageClock)*2^h := by
    have n:=Nat.two_pow_pos h
    dsimp [overhead,stageClock,unstageClock]
    omega
  calc
    _ ≤ subdivisionConstant d*2^h+rounds d*((48+stageClock+unstageClock)*2^h) :=
      add_le_add old (Nat.mul_le_mul_left _ overhead_le)
    _ = _ := by unfold constant;ring

/-- Uniform physical clock independent of the permutation and arbitrary raw
private words. All permanent stage columns use the original numbered layout. -/
theorem linear_run {h d : ℕ} (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h))) (raw : Memory (ramWidth h d))
    (read : ∀r : Fin (2^h),raw r.val=((π r).val : Word (ramWidth h d))) :
    let m:=inputTape h d _ raw
    (subdivision h d).Exec m (images h d m (rounds d)) (constant d*2^h) := by
  intro m P regs K machine
  exact Procedure.Spec.mono (execute_subdivision hd π raw read) (fun _ h=>h) (fun _ _ h=>h)
    (ticks_linear hd π raw read) machine

end
end Hierarchy.ProbeStage.Native.Compact

end OAI

import OAI.Hierarchy.ProbeStageCompactLevelCode
import OAI.Hierarchy.ProbeStageCompactVisit
import OAI.Hierarchy.ProbeStageCompactZeros

namespace OAI
/-! # The counted three-column allocator level realizes the original memory image -/

namespace Hierarchy.ProbeStage.Native.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators
noncomputable section

open private endpoint_frame from OAI.Hierarchy.ProbeStagePhase

theorem level_exec {h d : ℕ} (hh : 4≤ h) (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h)))
    (j : Fin (rounds d)) (m : Memory (ramWidth h d)) (geom : GeometryStored (h:=h) j m)
    (parent : ParentStored d π j.val m) (arrays : allArrays h d _ j m)
    (clear : ∀q : Fin 8,m (base h+q.val)=0) :
    (level h d j).Exec m (levelImage h d j m) (levelTicks h d j m+overhead h) := by
  let w:=ramWidth h d
  let pre:=result (prepareRows h d j.val) m
  have preArr : allArrays h d _ j pre := by
    intro k i hi
    have next:=allocator_end h d copies j.val
    have later : bankBase h d copies j.val 14≤ region h d j.val k+i := by unfold region bankBase;omega
    exact (endpoint_frame m (Or.inr (next.trans later))).trans (arrays k i hi)
  have ids:=prepare_endpoint_words hd π j m geom parent
  have atStep:=visit_records hd π j pre (initial_prefix hd π j pre preArr) preArr.immutable ids (physical_ordinal hd π j)
  let mem:=records h d j.val pre
  let price:=fun k=>stageClock+rowTicks h d j.val k (mem k)+unstageClock
  have rootZero:=prepared_zero (d:=d) hh j.val m clear
  have allZero (k : ℕ) (le : k≤2^h) := visit_zero hh (atStep k le) rootZero
  have bounds:=window_before (d:=d) hh j
  have upper:=cell_low (h:=h) j (.temp 0)
  change _≤ scratch h d j 0 at upper
  have room : scratch h d j 0<2^w := scratch_fits j 0
  have ticksum : (∑ k∈Finset.range (2^h),price k)=
      (∑k∈Finset.range (2^h),rowTicks h d j.val k (mem k))+(stageClock+unstageClock)*(2^h) := by
    simp only [price,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
    ring
  have loop : (CompactLoop.program h (body h d j)).Exec (mem 0) (mem (2^h)) (CompactLoop.cost h price) :=
    (CompactLoop.run h (body h d j) mem price
    (show CompactLoop.limit h+1<2^w by change base h+7+1<_;omega)
    (allZero _ le_rfl 6) (allZero _ le_rfl 7) (by
       intro k hk
       let i : Fin (2^h):=⟨k,hk⟩
       let state:=atStep k hk.le
       intro P regs K M
       exact body_exec j i hh hd π (mem k) (state.rom preArr.immutable) (state.ids ids i) state.counts
         (fun q=>allZero (k+1) hk ⟨q.val,by omega⟩) M))
  let child := (program w (prepareRows h d j)).seq (CompactLoop.program h (body h d j))
  have made : (child.seq (program w (writeRows h d j))).Exec m (levelImage h d j m)
      (clock (prepareRows h d j)+CompactLoop.cost h price+clock (writeRows h d j)) := by
    intro P regs K M
    exact Procedure.Exec.then (Procedure.Exec.then (program_exec (prepareRows h d j) m (prepare_fits j.isLt)) loop)
      (program_exec (writeRows h d j) (mem (2^h)) (write_fits j.isLt)) M
  have amount : clock (prepareRows h d j)+CompactLoop.cost h price+clock (writeRows h d j) =
      levelTicks h d j m+overhead h := by
    unfold CompactLoop.cost
    rw [ticksum]
    unfold levelTicks overhead
    dsimp only [mem,pre]
    ring
  rw [level,dite_eq_left j.isLt,←amount]
  exact @made

end
end Hierarchy.ProbeStage.Native.Compact

end OAI

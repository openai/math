import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorRoute
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Supplying a generated local header to an ordered Walsh pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileSwapStage

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshCompile
open KernelEffectiveFamily (leftCmd)
open CommonRegisters GeneratorSyntax Filter

private def retain (z : Tree × Tree) := (z,z.1)

structure Frame where
  keep : Cmd
  swap : Cmd

structure Legal (F : Frame) (R : ℕ) : Prop where
  positive : 0 < R
  keepReg : Within R F.keep
  swapReg : Within R F.swap
  save : Scans F.keep retain
  exchange : Scans F.swap (Prod.swap : Tree × Tree → Tree × Tree)

theorem exists_frame : ∃ (F : Frame) (R : ℕ), Legal F R := by
  obtain ⟨p,h⟩ := exists_scanner (show Easy retain from Easy.identity.pair Easy.fst)
  obtain ⟨q,g⟩ := exists_scanner (Easy.exchange (X:=Tree) (Y:=Tree))
  obtain ⟨R,pos,rp,rq⟩ := ((eventually_gt_atTop 0).and ((RegisterSelect.within_eventually p).and (RegisterSelect.within_eventually q))).exists
  exact ⟨⟨p,q⟩,R,pos,rp,rq,h,g⟩

def Frame.supply (F : Frame) (key body : Cmd) : Cmd :=
  (F.keep.join (leftCmd ((leftCmd key).join body))).join F.swap

theorem Frame.effective_supply {I : Type} [Primcodable I] (F : Frame) {k c : I → Cmd}
    (ek : Effective ltr k) (ec : Effective ltr c) : Effective ltr (fun i => F.supply (k i) (c i)) :=
  ((effective_const ltr F.keep).join (KernelEffectiveFamily.effective_left
    ((KernelEffectiveFamily.effective_left ek).join ec))).join (effective_const ltr F.swap)

theorem Legal.within_supply {R M : ℕ} {F : Frame} (hf : Legal F R) (le : R≤M) {k c : Cmd}
    (hk : Within M k) (hc : Within M c) : Within M (F.supply k c) :=
  ⟨⟨RegisterSelect.within_mono le _ hf.keepReg,KernelEffectiveFamily.within_left (hf.positive.trans_le le)
    ⟨KernelEffectiveFamily.within_left (hf.positive.trans_le le) hk,hc⟩⟩,RegisterSelect.within_mono le _ hf.swapReg⟩

open private Scans.atInput from OAI.Computability.NearSquareRoot.PhysicalWalshCompileSound

/-- Both the key emitter and the stage see their original inputs. Only the
outer header remains parked while the stage runs. -/
theorem Legal.supply_runs {I : Type} {R : ℕ} {F : Frame} (hf : Legal F R)
    {T S : I → ℕ} (cost : ∀ i,S i ≤ T i) {h k x y : I → Tree} {key body : Cmd}
    (keyRun : ClosedRuns key S S h k) (bodyRun : ClosedRuns body T S (fun i => .fork (k i) (x i)) y) :
    ClosedRuns (F.supply key body) T S (fun i => .fork (h i) (x i)) (fun i => .fork (h i) (y i)) := by
  let m : Meter I := ⟨T,S,cost,fun _ _ _ _ => True⟩
  obtain ⟨C,ch⟩ := (show BoundedTask S S h k from ⟨key,keyRun⟩).endpointSize
  obtain ⟨D,dr⟩ := (show BoundedTask T S (fun i => .fork (k i) (x i)) y from ⟨body,bodyRun⟩).endpointSize
  have head (i) : (h i).count ≤ C*(S i+1) := (Nat.le_max_left ..).trans (ch i)
  have row (i) : (x i).count ≤ D*(S i+1) := by
    have inBound := (Nat.le_max_left ..).trans (dr i); change (k i).count+(x i).count+1 ≤ _ at inBound; omega
  have out (i) : (y i).count ≤ D*(S i+1) := (Nat.le_max_right ..).trans (dr i)
  have prep := Scans.atInput (m:=m) (u:=id) hf.save (fun i => (h i,x i)) (C+D+1) (fun i => by
    change (h i).count+(x i).count+1 ≤ (C+D+1)*(S i+1)
    have := head i; have := row i; simp only [Nat.add_mul,Nat.one_mul]; omega)
  have runK : PhysicalWalsh.Runs key m 0 id h k := PhysicalWalsh.Runs.closed (keyRun.mono cost (fun _ => le_rfl))
  have runB : PhysicalWalsh.Runs body m 0 id (fun i => .fork (k i) (x i)) y := PhysicalWalsh.Runs.closed bodyRun
  have inside := (runK.left x D row).seq runB
  have swap := Scans.atInput (m:=m) (u:=id) hf.exchange (fun i => (y i,h i)) (C+D+1) (fun i => by
    change (y i).count+(h i).count+1 ≤ (C+D+1)*(S i+1)
    have := head i; have := out i; simp only [Nat.add_mul,Nat.one_mul]; omega)
  have whole := (prep.seq (inside.left h C head)).seq swap
  obtain ⟨K,run⟩ := whole
  refine ⟨K,?_⟩
  intro i env park b hb
  change BoundedFits env _ (pile 0 (send (h i,x i)) park) (pile 0 (send (y i,h i).swap) park) _ _ _
  simpa only [m,Nat.zero_mul,Nat.add_zero,id_eq,Frame.supply,KernelEffectiveFamily.leftCmd] using run i env 0 0 trivial park b hb

end PhysicalWalshCompileSwapStage

end NearSquareRoot
end Computability
end OAI

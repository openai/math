import OAI.Computability.BorderVNP.CubeISAOwnedRawSingleFrame

/-! # Two addressed singleton orientations on unvalidated crossing words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Physical.Owned Cube.Scatter VPVNP.BurstRAM Owned CellDispatch
open private Reversed Reversed.keep swapTrace reverseEntry reverse_twice from OAI.Computability.BorderVNP.CubeISAOwnedDoubleStage

variable {w n : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- An actual addressed singleton stage has the row's write confinement, preserves the
outer control bank, and does not move the routed selector cursor. -/
theorem singleStage_raw_frame (l : OwnedRowSetup.Layout) (D : SingleRowData n l.d (l.blocks*l.bc))
    (src : Set ℕ) {r : Bank w} {m : Memory w} {es t mt} (entry : Entry D.axis D.left D.right r)
    (loaded : l.Loaded n (readings pub) (readings m)) (fits : l.Fits w n (readings pub 0))
    (frameZ : (pub 0).val+56 ∈ src) (frameB : (pub 0).val+88 ∈ src)
    (zAt : readings m ((pub 0).val+56) = l.d^(n+1)) (bankAt : readings m ((pub 0).val+88) = D.bank)
    (room : SingleRoom w n l.d (l.blocks*l.bc) (pub 0).val D.bank)
    (protect : ∀ k : Fin (singlePairTrials n l.d), D.selected k → ∀ x ∈ src,
      x < D.address k ∨ D.address k+l.blocks*l.bc ≤ x)
    (path : Runs pub mac (singleStage n) r m es t mt) :
    Keeps r t ∧ t 36 = r 36 ∧ ∀ x ∈ src, mt x = m x := by
  obtain ⟨_,u,mu,_,_,setup,loop⟩ := seq_split path
  obtain ⟨ready,_,width,held,im⟩ := ((OwnedRowSetup.single_run pub mac r m l D.axis D.left D.right loaded fits
    entry.zero entry.one entry.axis entry.left entry.right).asTest (by decide) |>.sound setup).2
  have hm : mu = m := funext fun a => Fin.ext (congrFun im a)
  subst mu
  obtain ⟨low,old,sel⟩ := singleLoop_raw_frame D src u m ready width frameZ frameB zAt bankAt room protect loop
  exact ⟨keeps_setup_loop held low,sel.trans (Fin.ext (held _ (by decide))),old⟩

private theorem swap_return {r : Bank w} {m : Memory w} {es t mt} (path : Runs pub mac OwnedRowSetup.swap r m es t mt) :
    Reversed r t ∧ mt = m := by
  obtain ⟨_,_,_,canonical,_,_,post⟩ := swapTrace pub mac r m
  obtain ⟨_,rfl,rfl⟩ := canonical.unique_of_deterministic (by decide) path
  exact post

/-- Both singleton orientations and the two real swaps keep every separated selector or
source cell intact. This statement allows arbitrary values throughout the crossing stream. -/
theorem doubleStage_raw_frame (l : OwnedRowSetup.Layout) (A B : SingleRowData n l.d (l.blocks*l.bc))
    (src : Set ℕ) {r : Bank w} {m : Memory w} {es t mt} (entry : Entry A.axis A.left A.right r)
    (axis : B.axis = A.axis) (left : B.left = A.right) (right : B.right = A.left) (sameBank : B.bank = A.bank)
    (loaded : l.Loaded n (readings pub) (readings m)) (fits : l.Fits w n (readings pub 0))
    (pframe : Protected l n (pub 0).val src) (frameZ : (pub 0).val+56 ∈ src) (frameB : (pub 0).val+88 ∈ src)
    (zAt : readings m ((pub 0).val+56) = l.d^(n+1)) (bankAt : readings m ((pub 0).val+88) = A.bank)
    (room : SingleRoom w n l.d (l.blocks*l.bc) (pub 0).val A.bank)
    (protectA : ∀ k : Fin (singlePairTrials n l.d), A.selected k → ∀ x ∈ src,
      x < A.address k ∨ A.address k+l.blocks*l.bc ≤ x)
    (protectB : ∀ k : Fin (singlePairTrials n l.d), B.selected k → ∀ x ∈ src,
      x < B.address k ∨ B.address k+l.blocks*l.bc ≤ x)
    (path : Runs pub mac (doubleStage n) r m es t mt) : Keeps r t ∧ t 36 = r 36 ∧ ∀ x ∈ src, mt x = m x := by
  obtain ⟨_,a,ma,_,_,runA,afterA⟩ := seq_split path
  obtain ⟨_,c,mc,_,_,flipA,afterFlip⟩ := seq_split afterA
  obtain ⟨_,z,mz,_,_,runB,flipB⟩ := seq_split afterFlip
  obtain ⟨keepA,selA,oldA⟩ := singleStage_raw_frame l A src entry loaded fits frameZ frameB zAt bankAt room protectA runA
  obtain ⟨swapA,memA⟩ := swap_return flipA
  subst mc
  have eb : Entry B.axis B.left B.right c := axis ▸ left ▸ right ▸ reverseEntry (entry.keep keepA) swapA
  have zA := (congrArg Fin.val (oldA _ frameZ)).trans zAt
  have bA := (congrArg Fin.val (oldA _ frameB)).trans (bankAt.trans sameBank.symm)
  obtain ⟨keepB,selB,oldB⟩ := singleStage_raw_frame l B src eb (pframe.loaded loaded oldA) fits
    frameZ frameB zA bA (sameBank ▸ room) protectB runB
  obtain ⟨swapB,memB⟩ := swap_return flipB
  have controls := reverse_twice keepA swapA keepB swapB
  obtain ⟨_,_,stableA⟩ := swapA
  obtain ⟨_,_,stableB⟩ := swapB
  exact ⟨controls,
    (stableB 36 (by decide) (by decide) (by decide)).trans
      (selB.trans ((stableA 36 (by decide) (by decide) (by decide)).trans selA)),
    fun x hx => (congrFun memB x).trans ((oldB x hx).trans (oldA x hx))⟩

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI

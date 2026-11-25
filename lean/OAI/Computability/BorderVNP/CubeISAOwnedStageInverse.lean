import OAI.Computability.BorderVNP.CubeISAOwnedDoubleStage
import OAI.Computability.BorderVNP.CubeISAOwnedSingleRowInverse

/-! # Converse and trace uniqueness for the complete oriented singleton stages -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open VPVNP.BurstRAM DiagonalResidueRAM Cube.Scatter Owned Cube.Physical.Owned

/-- The entire addressed setup and singleton row have native tags. -/
theorem singleStage_nativeOnly (n : ℕ) : (singleStage n).nativeOnly = true := by
  have setup : OwnedRowSetup.single.nativeOnly = true := by decide
  have candidate := (singleCandidate n).nativeOnly_of_unsigned (singleCandidate_frame n).1
  have body : scatterSingle.nativeOnly = true := by decide
  simp only [singleStage,rowLoop,Code.nativeOnly,setup,candidate,body,Bool.and_self]

/-- All PCs of the two successive setup and scatter stages, including both label swaps, are native. -/
theorem doubleStage_native (n : ℕ) : ∀ pc, (doubleStage n).program.tag pc = .native := by
  apply Code.program_tag_native
  have swap : OwnedRowSetup.swap.nativeOnly = true := by decide
  simp only [doubleStage,Code.nativeOnly,singleStage_nativeOnly,swap,Bool.and_self]

/-- Every return from the complete addressed singleton stage, including its frame reads, is
the physical scatter of the reconstructed diagonal values on that exact chronological tape. -/
theorem singleStage_recover {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : OwnedRowSetup.Layout) (D : SingleRowData n l.d (l.blocks*l.bc)) (src : Set ℕ)
    (r : Bank w) (m : Memory w) (entry : Entry D.axis D.left D.right r)
    (sel : r 36 = word w D.selector) (cross : r 37 = word w D.crossing)
    (loaded : l.Loaded n (readings pub) (readings m)) (fit : l.Fits w n (readings pub 0))
    (prepared : D.PreparedRow src m) (frameZ : (pub 0).val+56 ∈ src) (frameBank : (pub 0).val+88 ∈ src)
    (zAt : readings m ((pub 0).val+56) = l.d^(n+1)) (bankAt : readings m ((pub 0).val+88) = D.bank)
    (frameFit : (pub 0).val+88 < 2^w) (keys : l.d^(n+1)*l.d^(n+1) ≤ 2^w)
    (allocation : D.bank+l.d^(n+1)*l.d^(n+1)*(l.blocks*l.bc) < 2^w)
    {es t mt} (run : Runs pub mac (singleStage n) r m es t mt) :
    let E := D.withTape (ChoiceTape.extend (es.flatMap TeamRAM.Event.choices))
    let out := E.before m (singlePairTrials n l.d)
    TraceOK es (rowChoices E.selected E.localBits) es.length ∧ traceCost es ≤ singleStageCost D ∧
      Keeps r t ∧ t 36 = word w D.selector ∧ t 37 = word w out.1 ∧ mt = out.2 := by
  intro E out
  let bs := es.flatMap TeamRAM.Event.choices
  let tape := ChoiceTape.extend bs
  obtain ⟨fs,y,my,canon,tr,cost,state⟩ := singleStage_run pub mac l E src r m entry sel cross loaded fit
    (D.prepared_withTape tape m prepared) frameZ frameBank zAt bankAt frameFit keys allocation
  obtain ⟨a,a',compat⟩ := ChoiceTape.compatible bs (ChoiceTape.offset D.privateWidth (singlePairTrials n l.d))
  have agree := (congrArg (· ++ a) (tr.2.1.trans (D.withTape_choices tape))).trans compat
  obtain ⟨rfl,rfl,rfl⟩ := unique_returns ((singleStage n).program_tag_native (singleStage_nativeOnly n)) canon run agree
  exact ⟨tr,cost,state⟩

/-- Between distinct groups all singleton words are loaded from the shared crossing list. -/
theorem strictChoices {n d len : ℕ} (D : SingleRowData n d len) (strict : D.left ≠ D.right) :
    rowChoices D.selected D.localBits = [] := by
  have empty (t) : D.localBits t = [] := by rw [D.localBits_eq,ite_eq_right strict]
  simp [rowChoices,empty]

/-- If the two addressed passes run at opposite orientations of a strict row, the forward
image also characterizes every returning path. All loads, stores, old words and the restored
control bank agree with the prescribed, choice-free execution. -/
theorem strict_double_return {w n : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {r : Bank w} {m : Memory w} {l : OwnedRowSetup.Layout}
    (first second : SingleRowData n l.d (l.blocks*l.bc))
    (strictA : first.left ≠ first.right) (strictB : second.left ≠ second.right)
    {cost : ℕ} {Q : Bank w → Memory w → Prop}
    (forward : TraceRun pub mac (doubleStage n) r m
      (rowChoices first.selected first.localBits ++ rowChoices second.selected second.localBits) cost Q)
    {es t mt} (run : Runs pub mac (doubleStage n) r m es t mt) :
    TraceOK es [] es.length ∧ traceCost es ≤ cost ∧ Q t mt := by
  rw [strictChoices first strictA,strictChoices second strictB] at forward
  obtain ⟨fs,y,my,canon,tr,budget,post⟩ := forward
  have empty : fs.flatMap TeamRAM.Event.choices = [] := tr.2.1
  have agree : fs.flatMap TeamRAM.Event.choices ++ es.flatMap TeamRAM.Event.choices =
      es.flatMap TeamRAM.Event.choices ++ [] := by rw [empty]; simp
  obtain ⟨rfl,rfl,rfl⟩ := unique_returns (doubleStage_native n) canon run agree
  exact ⟨tr,budget,post⟩

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI

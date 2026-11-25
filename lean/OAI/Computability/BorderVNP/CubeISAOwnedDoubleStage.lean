import OAI.Computability.BorderVNP.CubeISAOwnedSingleStage

/-! # Both oriented singleton scatters on an unordered group row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open VPVNP.BurstRAM DiagonalResidueRAM Cube.Scatter Owned Cube.Physical.Owned

/-- Reverse the symbol registers for the second pass and restore them before returning to the
outer pair loop. -/
def doubleStage (n : ℕ) : Code := .seq (singleStage n) (.seq OwnedRowSetup.swap (.seq (singleStage n) OwnedRowSetup.swap))

/-- Tick allowance of one fully addressed singleton scatter stage. -/
def singleStageCost {n d len : ℕ} (D : SingleRowData n d len) :=
  OwnedRowSetup.single.slots +
    ((∑ t : Fin (singlePairTrials n d), (6*n+20+if D.selected t then startSingle.slots+5*len+2 else 1))+1)

private structure Reversed {w : ℕ} (r t : Bank w) : Prop where
  left : t 14 = r 15
  right : t 15 = r 14
  keep : ∀ j : Reg, j ≠ 14 → j ≠ 15 → j ≠ 54 → t j = r j

private theorem swapTrace {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w) :
    TraceRun pub mac OwnedRowSetup.swap r m [] 3 (fun t mt => Reversed r t ∧ mt = m) := by
  apply (traceRun_unsigned (OwnedRowSetup.swap_run pub mac r m) (by decide)).mono le_rfl
  rintro t mt ⟨a,b,kept,mem⟩
  exact ⟨⟨Fin.ext a,Fin.ext b,fun j h1 h2 h3 => Fin.ext (kept j h1 h2 h3)⟩,
    funext fun j => Fin.ext (congrFun mem j)⟩

private theorem reverseEntry {w n d : ℕ} {i : Fin (n+1)} {a b : Fin d} {r t : Bank w}
    (entry : Entry i a b r) (rev : Reversed r t) : Entry i b a t :=
  ⟨(congrArg Fin.val (rev.keep 0 (by decide) (by decide) (by decide))).trans entry.zero,
    (congrArg Fin.val (rev.keep 1 (by decide) (by decide) (by decide))).trans entry.one,
    (congrArg Fin.val (rev.keep 4 (by decide) (by decide) (by decide))).trans entry.axis,
    (congrArg Fin.val rev.left).trans entry.right,(congrArg Fin.val rev.right).trans entry.left⟩

private theorem reverse_twice {w : ℕ} {r a b c t : Bank w}
    (first : Keeps r a) (swapA : Reversed a b) (second : Keeps b c) (swapB : Reversed c t) : Keeps r t := by
  intro j hj
  by_cases left : j = 14
  · subst j
    exact swapB.left.trans ((second 15 (by decide)).trans (swapA.right.trans (first 14 (by decide))))
  by_cases right : j = 15
  · subst j
    exact swapB.right.trans ((second 14 (by decide)).trans (swapA.left.trans (first 15 (by decide))))
  have scratch : j ≠ 54 := (by decide : ∀ j : Reg, Control j → j ≠ 54) j hj
  exact (swapB.keep j left right scratch).trans
    ((second j hj).trans ((swapA.keep j left right scratch).trans (first j hj)))

/-- Both orientations of one group-pair row, starting from its real frame and current physical
memory. The shared cursors pass directly from one stage to the next, all caller control words
are restored, and the ending memory is the two successive native scatter images. -/
theorem doubleStage_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : OwnedRowSetup.Layout) (first second : SingleRowData n l.d (l.blocks*l.bc)) (src : Set ℕ)
    (r : Bank w) (m : Memory w) (entry : Entry first.axis first.left first.right r)
    (axis : second.axis = first.axis) (left : second.left = first.right) (right : second.right = first.left)
    (sameBank : second.bank = first.bank) (sameSel : second.selector = first.selector)
    (nextCross : second.crossing = (first.before m (singlePairTrials n l.d)).1)
    (sel : r 36 = word w first.selector) (cross : r 37 = word w first.crossing)
    (loaded : l.Loaded n (readings pub) (readings m)) (fit : l.Fits w n (readings pub 0))
    (protect : Protected l n (pub 0).val src)
    (preparedA : first.PreparedRow src m) (preparedB : second.PreparedRow src (first.before m (singlePairTrials n l.d)).2)
    (frameZ : (pub 0).val+56 ∈ src) (frameBank : (pub 0).val+88 ∈ src)
    (zAt : readings m ((pub 0).val+56) = l.d^(n+1)) (bankAt : readings m ((pub 0).val+88) = first.bank)
    (frameFit : (pub 0).val+88 < 2^w) (keys : l.d^(n+1)*l.d^(n+1) ≤ 2^w)
    (allocation : first.bank+l.d^(n+1)*l.d^(n+1)*(l.blocks*l.bc) < 2^w) :
    let endA := first.before m (singlePairTrials n l.d)
    let endB := second.before endA.2 (singlePairTrials n l.d)
    TraceRun pub mac (doubleStage n) r m
      (rowChoices first.selected first.localBits ++ rowChoices second.selected second.localBits)
      (singleStageCost first + (3 + (singleStageCost second + 3)))
      (fun t mt => Keeps r t ∧ t 36 = word w first.selector ∧ t 37 = word w endB.1 ∧ mt = endB.2) := by
  intro endA endB
  let Q (t : Bank w) (mt : Memory w) := Keeps r t ∧ t 36 = word w first.selector ∧ t 37 = word w endB.1 ∧ mt = endB.2
  have source (j : ℕ) (hj : j ∈ src) : endA.2 j = m j := first.before_source m preparedA _ j hj
  have loadB := protect.loaded loaded source
  have zB := (congrArg Fin.val (source _ frameZ)).trans zAt
  have bankB := (congrArg Fin.val (source _ frameBank)).trans (bankAt.trans sameBank.symm)
  have allocB : second.bank+l.d^(n+1)*l.d^(n+1)*(l.blocks*l.bc) < 2^w := sameBank ▸ allocation
  have initial := singleStage_run pub mac l first src r m entry sel cross loaded fit preparedA frameZ frameBank
    zAt bankAt frameFit keys allocation
  have all := initial.seq (Q := Q) (cs := rowChoices second.selected second.localBits)
    (k := 3+(singleStageCost second+3)) (fun a ma ha => by
      obtain ⟨keepA,asel,across,memA⟩ := ha
      subst ma
      apply (swapTrace pub mac a endA.2).seq (cs := rowChoices second.selected second.localBits)
        (k := singleStageCost second+3)
      rintro b mb ⟨swA,rfl⟩
      have en : Entry second.axis second.left second.right b := by
        rw [axis,left,right]
        exact reverseEntry (entry.keep keepA) swA
      have bsel := (swA.keep 36 (by decide) (by decide) (by decide)).trans (asel.trans (congrArg (word w) sameSel.symm))
      have bcross := (swA.keep 37 (by decide) (by decide) (by decide)).trans (across.trans (congrArg (word w) nextCross.symm))
      have visitB := singleStage_run pub mac l second src b endA.2 en bsel bcross loadB fit preparedB frameZ frameBank
        zB bankB frameFit keys allocB
      have finish := visitB.seq (Q := Q) (cs := []) (k := 3) (fun c mc hc => by
        obtain ⟨keepB,csel,ccross,memB⟩ := hc
        apply (swapTrace pub mac c mc).mono le_rfl
        rintro t mt ⟨swB,rfl⟩
        exact ⟨reverse_twice keepA swA keepB swB,
          (swB.keep 36 (by decide) (by decide) (by decide)).trans (csel.trans (congrArg (word w) sameSel)),
          (swB.keep 37 (by decide) (by decide) (by decide)).trans ccross,memB⟩)
      simpa only [singleStageCost,List.append_nil] using finish)
  exact all

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI

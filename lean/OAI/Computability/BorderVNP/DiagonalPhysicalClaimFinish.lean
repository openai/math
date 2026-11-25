import OAI.Computability.BorderVNP.DiagonalTallyReturningOperands
import OAI.Computability.BorderVNP.DiagonalReturnedClaimClock

/-! # The genuine local finish receipt on an arbitrary returning team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader.PositiveFields

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation DiagonalTallyRAM
open DiagonalTallyMaterialize DiagonalResidueRAM

/-- Build the signed native finish receipt without a passing path on any
other team. The rows here are the actual words in the proposed header.
The native guards force this team's raw operands to have valid coordinates
and unwrapped local sums. Its own row comparison then proves that its
decoded header words are exactly those local sums. -/
theorem localFinishOfReturn {w dim teams width raw : ℕ} (team : Fin teams) (post : AfterTasks)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (state start : Bank w) (mem selected : Memory w)
    (events : List (TeamRAM.Event w)) (os : List Operand) (xs : List (List Bool))
    (prepare : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      state mem events start selected)
    (seed : SelectedSeed post pub mem raw dim teams team.val width)
    (keep : ∀ k,k<post.start → k≠(pub 0).val+35 → selected k=mem k)
    (frame : (pub 0).val+101<post.start) (rawLo : (pub 0).val+45 ≤ raw)
    (rawHi : raw+(teams*dim)*width ≤ post.start)
    (room : post.localBase+dim+teams*dim+dim+dim+1+dim*w<2^w)
    (teamsFit : teams<2^w) (widthFit : width ≤ w) (wpos : 0<w)
    (operands : supplied selected post.fresh post.descriptors os)
    (count : (selected ((pub 0).val+35)).val=os.length) (capacity : os.length ≤ post.bound.operands)
    (apart : ∀ k, operandReads post.descriptors os k → outsidePointers (pub 0).val k ∧ k≠(pub 0).val+34)
    (data : DiagonalTallyBits.WordsAt mem raw xs) (length : xs.length=teams*dim) (sizes : ∀ b∈xs,b.length=width)
    (z : Returns (finishExpansion signedOccurrences) pub mac state mem) :
    let a := post.arenaFor os.length raw dim teams team.val width
    let rows := fun (i : Fin teams) (c : Fin dim) => (claimWord (w := w) a.frame xs i.val c.val).val
    ∃ h : FinishInput team rows width pub mac state mem xs,
      h.post=post ∧ h.raw=raw ∧ h.operands=os ∧ h.earlier=events ∧ h.selected=selected := by
  intro a rows
  obtain ⟨u,mu,_,_,_,first,aligned⟩ := Runs.seq_iff.mp (signedFinish_split.mp z.property)
  obtain ⟨_,us,mus⟩ := first.unique_of_deterministic (by decide) prepare
  subst u
  subst mu
  have read (i : ℕ) (hi : i ≤ 101) (hne : i≠35) :
      selected ((pub 0).val+i)=mem ((pub 0).val+i) := keep _ (by omega) (by omega)
  have before : post.start ≤ post.fresh := by rw [post.footprint]; omega
  have low : post.fresh ≤ post.localBase := Nat.le_add_right ..
  have fit : a.Fits w (pub 0).val :=
    post.arena_fits capacity (by omega) (by omega) room team.isLt teamsFit widthFit wpos
  have initial : a.alignedSeed pub selected post.descriptors := by
    refine post.aligned_seed pub selected raw dim teams team.val width os.length capacity ?_ ?_ count ?_ ?_ ?_ ?_ ?_ ?_
    · rw [read 33 (by decide) (by decide)]; exact seed.dimensions.1
    · rw [read 34 (by decide) (by decide)]; exact seed.dimensions.2
    · rw [read 36 (by decide) (by decide)]; exact seed.common.1
    · rw [read 38 (by decide) (by decide)]; exact seed.common.2.1
    · rw [read 39 (by decide) (by decide)]; exact seed.common.2.2.1
    · rw [read 40 (by decide) (by decide)]; exact seed.common.2.2.2
    · rw [read 44 (by decide) (by decide)]; exact seed.words.1
    · rw [read 101 (by decide) (by decide)]; exact seed.words.2
  obtain ⟨coords,sums⟩ := a.guards_of_aligned pub mac start selected os post.descriptors initial fit
    (by omega) (supplied_mono _ (post.arena_lower capacity raw dim teams team.val width) _ _ operands) apart rfl aligned
  have input := seed.alignedInput post pub mem selected raw dim teams team.val width os xs keep frame rawLo rawHi room
    team.isLt teamsFit widthFit wpos operands count capacity apart coords sums data length sizes
  have matching := alignedAllocateAndEvaluate_sound a pub mac start selected os xs post.descriptors input aligned
  have total (c : Fin dim) : a.localRow os c.val=rows team c := by
    exact (word_val w _ (sums c.val c.isLt)).symm.trans (congrArg Fin.val (matching c.val c.isLt))
  exact ⟨⟨post,raw,os,events,start,selected,prepare,input,total,capacity⟩,rfl,rfl,rfl,rfl,rfl⟩

end TeamContraction.JointHeader.PositiveFields

end BorderVNP
end Computability
end OAI

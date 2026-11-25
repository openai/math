import OAI.Computability.BorderVNP.DiagonalTallySelectedOperands
import OAI.Computability.BorderVNP.CubePhysicalAlignedClaims
import OAI.Computability.BorderVNP.RoutingISASignedAssembly

/-! # The linked signed evaluator's actual post-cell execution and subtotal check -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyAllocation DiagonalTallyMaterialize
open DiagonalTallyCellReports
open private seq_assoc from OAI.Computability.BorderVNP.RoutingISABlockAppend

/-- The linked evaluator finishes the exact cube selection and operand program, then
runs the aligned subtotal calculation, with the same trace and final RAM state. -/
theorem signedFinish_split {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m es t mt} :
    Runs pub mac (Evaluator.finishExpansion Evaluator.signedOccurrences) s m es t mt ↔
      Runs pub mac (.seq (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
        alignedAllocateAndEvaluate) s m es t mt := by
  let sel := [DiagonalTallyPacketEmit.producePacketIDs,DiagonalTallyCubeSuffix.appendCubeOperands]
  let work := [alignTallies,allocateTallies,prepareTallies]
  have split {x mx ys y my} :
      Runs pub mac Evaluator.signedOccurrences x mx ys y my ↔
        Runs pub mac (.seq (.block sel) (.block work)) x mx ys y my :=
    Runs.block_append_iff (a:=sel) (b:=work) (by decide) (by decide)
  change Runs pub mac (.seq Evaluator.signedOccurrences complete) s m es t mt ↔
    Runs pub mac (.seq (.block sel) alignedAllocateAndEvaluate) s m es t mt
  conv_lhs => rw [Runs.seq_iff]; simp only [split,← Runs.seq_iff]
  rw [← seq_assoc]
  simp only [Runs.seq_iff,alignedAllocateAndEvaluate_iff_finish,Evaluator.finishExpansion,work,Code.block]

/-- Length-only scalar seed prior to the lookup and suffix program. Their native
frame-35 update supplies the remaining realized count. -/
structure SelectedSeed {w : ℕ} (post : AfterTasks) (pub : Arg → Word w) (m : Memory w)
    (raw dim teams team width : ℕ) : Prop where
  /-- Physical dimension and static local-bank endpoint. -/
  dimensions : (m ((pub 0).val+33)).val=dim ∧ (m ((pub 0).val+34)).val=post.localBase
  /-- The common raw fields and native team word. -/
  common : (m ((pub 0).val+36)).val=raw ∧ (m ((pub 0).val+38)).val=teams ∧
    (m ((pub 0).val+39)).val=team ∧ (m ((pub 0).val+40)).val=width
  /-- Physical descriptor pointer and the uniform machine word width. -/
  words : (m ((pub 0).val+44)).val=post.descriptors ∧ (m ((pub 0).val+101)).val=w

/-- Build the actual allocator inputs at the end of selected cube ID generation and
operand writing, with every common bit retained from the physically supplied old
tape and every fresh-bank inequality derived from the fixed reservation. -/
theorem SelectedSeed.alignedInput {w : ℕ} (post : AfterTasks) (pub : Arg → Word w) (m mt : Memory w)
    (raw dim teams team width : ℕ) (os : List Operand) (xs : List (List Bool))
    (seed : SelectedSeed post pub m raw dim teams team width)
    (preserved : ∀ k,k<post.start → k≠(pub 0).val+35 → mt k=m k)
    (frame : (pub 0).val+101<post.start) (rawLo : (pub 0).val+45 ≤ raw)
    (rawHi : raw+(teams*dim)*width ≤ post.start)
    (room : post.localBase+dim+teams*dim+dim+dim+1+dim*w<2^w)
    (validTeam : team<teams) (fitTeams : teams<2^w) (widthFit : width ≤ w) (wpos : 0<w)
    (operands : supplied mt post.fresh post.descriptors os) (count : (mt ((pub 0).val+35)).val=os.length)
    (capacity : os.length ≤ post.bound.operands)
    (separated : ∀ k, operandReads post.descriptors os k → outsidePointers (pub 0).val k ∧ k≠(pub 0).val+34)
    (coords : ∀ o∈os,o.pair.1<dim)
    (sums : ∀ c<dim,(post.arenaFor os.length raw dim teams team width).localRow os c<2^w)
    (rawData : DiagonalTallyBits.WordsAt m raw xs) (length : xs.length=teams*dim) (sizes : ∀ b∈xs,b.length=width) :
    AlignedAllocationInput (post.arenaFor os.length raw dim teams team width) pub mt os xs post.descriptors := by
  have read (i : ℕ) (lo : i ≤ 101) (ne : i≠35) : mt ((pub 0).val+i)=m ((pub 0).val+i) :=
    preserved _ (by omega) (by omega)
  have before : post.start ≤ post.fresh := by
    rw [post.footprint]; omega
  have localBefore : post.fresh ≤ post.localBase := Nat.le_add_right ..
  have fit := post.arena_fits (frame:=(pub 0).val) (raw:=raw) (dim:=dim) (teams:=teams) (team:=team) (width:=width) (w:=w) capacity (by omega) (by omega) room validTeam fitTeams widthFit wpos
  refine ⟨post.aligned_seed pub mt raw dim teams team width os.length capacity ?_ ?_ count ?_ ?_ ?_ ?_ ?_ ?_,
    fit,by omega,supplied_mono _ (post.arena_lower capacity raw dim teams team width) _ _ operands,
    separated,?_,rfl,coords,sums,?_,length,sizes⟩
  · rw [read 33 (by decide) (by decide)]; exact seed.dimensions.1
  · rw [read 34 (by decide) (by decide)]; exact seed.dimensions.2
  · rw [read 36 (by decide) (by decide)]; exact seed.common.1
  · rw [read 38 (by decide) (by decide)]; exact seed.common.2.1
  · rw [read 39 (by decide) (by decide)]; exact seed.common.2.2.1
  · rw [read 40 (by decide) (by decide)]; exact seed.common.2.2.2
  · rw [read 44 (by decide) (by decide)]; exact seed.words.1
  · rw [read 101 (by decide) (by decide)]; exact seed.words.2
  · intro k lo _
    change raw ≤ k at lo
    unfold outsidePointers
    omega
  · apply DiagonalTallyBits.words_congr _ _ raw width _ rawData sizes
    intro k lo hi
    rw [length] at hi
    exact preserved k (by omega) (by omega)

/-- Every accepting linked native suffix verifies the actual row, even if the
common-claim tape was chosen arbitrarily. The initial selected-operand run is
unique on its original physical memory and contains no private guesses. -/
theorem signedFinish_sound {w : ℕ} (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s u : Bank w) (m mu : Memory w) (earlier : List (TeamRAM.Event w)) (os : List Operand) (xs : List (List Bool))
    (p : ℕ) (prepared : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      s m earlier u mu) (input : AlignedAllocationInput a pub mu os xs p)
    {es t mt} (run : Runs pub mac (Evaluator.finishExpansion Evaluator.signedOccurrences) s m es t mt) :
    ∀ c<a.dim,word w (a.localRow os c)=claimWord a.frame xs a.team c := by
  obtain ⟨v,mv,_,_,_,ids,tail⟩ := Runs.seq_iff.mp (signedFinish_split.mp run)
  obtain ⟨_,rfl,rfl⟩ := ids.unique_of_deterministic (by decide) prepared
  exact alignedAllocateAndEvaluate_sound a pub mac _ _ os xs p input tail

/-- Conversely, the true broadcast produces every bit of the summed natural row at
the fixed physical query location in the evaluator's linked program. -/
theorem signedFinish_runs {w : ℕ} (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s u : Bank w) (m mu : Memory w) (earlier : List (TeamRAM.Event w)) (os : List Operand) (p budget : ℕ)
    (rows : Fin a.teams → Fin a.dim → ℕ)
    (prepared : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      s m earlier u mu) (cost : traceCost earlier ≤ budget) (input : AlignedAllocationInput a pub mu os (broadcast a.width rows) p)
    (localCounts : ∀ c, a.localRow os c.val=rows ⟨a.team,input.fit.team⟩ c)
    (rowFit : ∀ i c,rows i c<2^a.width) (sumFit : ∀ c, ∑ i, rows i c<2^w) :
    ∃ es t mt,Runs pub mac (Evaluator.finishExpansion Evaluator.signedOccurrences) s m es t mt ∧
      traceCost es ≤ budget+(alignTallies.slots+allocateTallies.slots+a.work w os) ∧
      (∀ e∈es,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c : Fin a.dim,∀ j<w,mt ((a.bitFrame w).dst+(c.val*w+j))=word w (((∑ i,rows i c).testBit j).toNat) := by
  obtain ⟨last,t,mt,run,clock,_,output⟩ := alignedAllocateAndEvaluate_natural_runs a pub mac u mu os p rows
    input.seed input.fit input.frameFit input.operands input.operandsDisjoint input.broadcastDisjoint input.count input.coords
    input.raw localCounts rowFit sumFit
  have full := signedFinish_split.mpr (prepared.seq run)
  refine ⟨_,t,mt,full,?_,ordinary_run (by decide) full,output⟩
  rw [show traceCost (earlier++last)=traceCost earlier+traceCost last from VPVNP.RAMBuckets.cost_append ..]
  exact Nat.add_le_add cost clock

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI

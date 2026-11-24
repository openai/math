import OAI.Computability.VPVNP.CompressorShrinkSelectedTailGroup
import OAI.Computability.VPVNP.CompressorShrinkScoreGroup
import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch

/-! # Fourteen selected-geometry visits on each admitted shrinking branch -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SelectedTailPackets

open BurstRAM Compression ShrinkBlockInputs BlockPlanner DescriptorSpace Schedule SourceTransport
open scoped Fin.CommRing Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (base : Word w) (positions blocks t : ℕ)
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (BlockPlanner.Script.catalog (BlockProgram.script B))) base
local notation "pub" => Schedule.Ports.data pt
local notation "first₀" => BlockPlanner.Script.levelsPerBlock (BlockProgram.script B)*t
local notation "H" => levelStart L 0
local notation "head" => levelStart L (first₀+i.val)
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "p₀" => ShrinkInput.placementBank X T start
local notation "tab" => SelectedArena.scoreTables X term (10 : Word w) (B.shrink.selectorBits : Word w)

/-- Total source calls for the selected geometry, including two one-shot score calls, eight
score calls per motif, and the four scans for placement, roles, and the child directory. -/
def selectedCalls {a g : ℕ} (X : State a (packingLaneBits a g)) :=
  (8*SelectedArena.motifs X+2)+(SelectedArena.positions X+(DemandRAM.oldCount X+
    (ShrinkPreimages.newCount X+ShrinkPreimages.oldCount X)))


private theorem preliminaryFloor {mem : Memory w} (r : ShrinkInput.Run X T start mem)
    (lo : ℕ) (before : lo ≤ start) (inc : ∀ j, lo≤(T.column j).val) :
    lo ≤ ShrinkHistoryTrace.inputFloor p₀ := by
  have h := GreedyArena.bounds start (Fintype.card X.Base) (a i)
  have room := r.greedy.room
  have v₁ : GreedyArena.colorBase start < 2^w := by omega
  have v₂ : GreedyArena.offsetBase start (Fintype.card X.Base) (a i) < 2^w := by omega
  apply le_min
  · apply le_min
    · change lo≤GreedyArena.colorBase start%(2^w); rw [Nat.mod_eq_of_lt v₁]; exact before
    · change lo≤GreedyArena.offsetBase start _ _%(2^w); rw [Nat.mod_eq_of_lt v₂]
      exact before.trans (by unfold GreedyArena.offsetBase; omega)
  · exact le_min (inc 0) (inc 2)

set_option maxHeartbeats 2000000 in
/-- The fixed ten-score and four-directory groups join at the score post-memory.
The branch supplies all native proofs. The returned memory is the entry for
the next resident-directory group. -/
theorem selected_group (s : SelectedScore.Selection B X) (m : Memory w) (fuel cap : ℕ)
    (p : ShrinkBranch.Prefix X T start fuel m)
    (v : ShrinkBranch.Selected B X T start (10 : Word w) (B.shrink.selectorBits : Word w) fuel m p s)
    (fits : ShrinkBranch.PrefixFits B X T start (10 : Word w) fuel) (room : SelectedFinish.stop X term 10 ≤ 2^w)
    (header : ShrinkHeaderReads.Header i X T start L (first₀) p.beforeTerm) (before : head+60 < start)
    (inc : ∀ j, H≤(T.column j).val) (rows : p.beforeTerm (pt).rows.val = (directoryRows L : Word w))
    (pitch : p.beforeTerm (pub 1-1).val = (levelWords L : Word w))
    (within : t<blocks) (fit : endAddress L<2^w) (clock : SourceOnline.scanCap prog 65≤cap) :
    let mem := after p.beforeTerm (eventLog v.terms)
    let ordinal := (prog).initial.length+t*(prog).block.length+(BlockIndex.earlier B i).length+22
    ∃ ps : List (SourceOnline.Packet prog w), SourceOnline.Group prog L base cap ordinal (directoryRows L) mem ps ∧
      ps.length=14 ∧ eventLog (ps.flatMap SourceWalk.Packet.reports)=eventLog v.geometry.reports ∧
      SourceOnline.post mem ps=v.beforeOutput ∧
      ps.flatMap (fun q => q.stage.choices)=List.replicate (selectedCalls X) [] := by
  intro mem ordinal
  let r := v.geometry.placed
  let c := v.geometry.children
  have exec := v.postTerm.placed
  have selected := v.postTerm.selected
  have finish := v.postTerm.geometry
  have ten : 10<2^w := by have := header.room; omega
  have small : (10 : Word w).val=10 := Nat.mod_eq_of_lt ten
  have terms := fits.termRoom
  rw [small] at terms
  have lo := ScorePackets.start_le_term i X start terms
  have h0 : H≤head := levelStart_mono L (Nat.zero_le _)
  have startLo : H≤start := by omega
  have baseFit : H<2^w := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  have hctrl := Window.lowCells (A:=prog) L base rfl rfl baseFit
  have beforeTerm (j : ℕ) (hj : j<start) : mem j=p.beforeTerm j := v.termRun.frame j (.inl (hj.trans_le lo))
  have entryHeader := header.keep_below before beforeTerm
  have rowLo : (pt).rows.val<start := hctrl.1.trans_le startLo
  have pitchLo : (pub 1-1).val<start := hctrl.2.trans_le startLo
  have entryRows := (beforeTerm _ rowLo).trans rows
  have entryPitch := (beforeTerm _ pitchLo).trans pitch
  have selFit : SelectedArena.Fits X term (10 : Word w) := by
    have hn : 0<ShrinkPreimages.oldCount X := Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos _)
    change SelectedArena.endAddr X term 10+ShrinkPreimages.newCount X+ShrinkPreimages.oldCount X ≤ _ at room
    change SelectedArena.endAddr X term 10 < _; omega
  have clock27 : SourceOnline.scanCap prog 27 ≤ cap := (show SourceOnline.scanCap prog 27≤SourceOnline.scanCap prog 65 by
    unfold SourceOnline.scanCap; omega).trans clock
  obtain ⟨ps,gp,ids,ev,cs⟩ := ScorePackets.group B i X T start base positions blocks t cap mem r.scores exec.scores
    within terms before selFit entryHeader entryRows entryPitch clock27
  have reg := ScorePackets.Region.selected X term (10 : Word w) (B.shrink.selectorBits : Word w) (small ▸ le_rfl) selFit
  have keep (j : ℕ) (hj : j<start) : r.afterScores mem j=mem j :=
    ScorePackets.score_frame tab (SelectedArena.motifs X) mem r.scores exec.scores reg j (hj.trans_le lo)
  have init := entryHeader.keep_below before keep
  have inputFit : ShrinkInput.stop X start<2^w := by unfold ShrinkInput.termEnd at terms; omega
  have old := (p.input.termInputs (10 : Word w) fits.termRoom).1
  have low := preliminaryFloor i X T start p.input H startLo inc
  obtain ⟨qs,gq,tailIds,tailReports,tailPost⟩ := group B i X T start base positions blocks t s mem r c
    exec selected finish (p.input.bankParams inputFit) old terms room init before low (inc 3)
    ((keep _ rowLo).trans entryRows) ((keep _ pitchLo).trans entryPitch) within fit cap clock
  have len : ps.length=10 := by
    have := congrArg List.length ids
    simpa only [Window.indices,List.length_map,List.length_ofFn,ScorePackets.visits,ScorePackets.length] using this
  have len' : qs.length=4 := by simpa only [Window.indices,List.length_map,List.length_ofFn,tail,List.length_cons,List.length_nil] using congrArg List.length tailIds
  have mid : SourceOnline.post mem ps = r.afterScores mem := congrArg (after mem) ev
  have indexEq : ordinal+ps.length = (prog).initial.length+t*(prog).block.length+(BlockIndex.earlier B i).length+32 := by
    dsimp only [ordinal]; omega
  have join := gp.append (show SourceOnline.Group prog L base cap (ordinal+ps.length) (directoryRows L) (SourceOnline.post mem ps) qs by rwa [mid,indexEq])
  refine ⟨ps++qs,join,by rw [List.length_append,len,len'],?_,?_,?_⟩
  · simp only [List.flatMap_append,eventLog] at ev ⊢
    rw [ev,tailReports]
    simp only [ChosenGeometry.Construction.reports,SelectedStage.Passes.all,reports,List.flatMap_append,List.append_assoc,r,c]
  · rw [SourceOnline.post_append,mid,tailPost]; rfl
  · rw [List.flatMap_append,cs,PublishedHeads.chronological_tapes _ qs gq.chronological,tailReports]
    have paths {Q : Type} {P : BurstRAM.Program w Q} {f : ℕ} {state : Option (Word w)} {mem : Memory w} {n : ℕ} {rs : List (Report w)}
        (run : runSegment P f state mem (List.replicate n [])=some rs) : branchPaths rs=List.replicate n [] :=
      ((runSegment_iff ..).mp run).2.2
    simp only [reports,branchPaths,List.map_append]
    rw [show r.positions.map (fun z => choiceBits z.events)=_ from paths (n:=SelectedArena.positions X) exec.positions,
      show r.roles.map (fun z => choiceBits z.events)=_ from paths (n:=DemandRAM.oldCount X) exec.roles,
      show c.clear.map (fun z => choiceBits z.events)=_ from paths (n:=ShrinkPreimages.newCount X) finish.raw.clear,
      show c.collect.map (fun z => choiceBits z.events)=_ from paths (n:=ShrinkPreimages.oldCount X) finish.raw.collect]
    simp only [← List.replicate_add,selectedCalls]

end CompressorRecords.SelectedTailPackets

end

end VPVNP
end Computability
end OAI

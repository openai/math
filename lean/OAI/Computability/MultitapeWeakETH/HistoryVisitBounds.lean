import OAI.Computability.MultitapeWeakETH.HistoryVisitChildren
import OAI.Computability.MultitapeWeakETH.ResidentHistory
import OAI.Computability.MultitapeWeakETH.WitnessReplyBound
import OAI.Computability.VPVNP.PairSimulationNodeFieldSpace
import OAI.Computability.VPVNP.PairTraversalBuildExecution

/-! # Uniform branching and packet bounds on the chronological visitor -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords PairSimulation NetworkKernel
open LocalHistory NodeArguments TraversalRows WitnessWalk DyadicBudget
open private earlier leaf from OAI.Computability.MultitapeWeakETH.HistoryVisit
open private selected_order from OAI.Computability.MultitapeWeakETH.HistoryVisitChildren
open private size_list_le from OAI.Computability.MultitapeWeakETH.WitnessWalkSpace
open scoped Classical
noncomputable section

theorem visitor_lower {stages : ℕ} (K : ℕ) (children : HistorySite × Bits.Word → Option ChildResult)
    (sh : Fin stages → Kernel) (refresh : RefreshQuery → Option (List Tally)) (ctx : VisitContext)
    (j : Job) (bits : Bits.Word) (ans : Answer) (h : visitor K children sh refresh ((ctx,j),bits) = some ans) :
    ∀ child ∈ ans.1.1, child.1.1.length < j.1.1.length := by
  obtain ⟨⟨lvl,site⟩,packet⟩ := j
  obtain ⟨⟨jobs,tail⟩,ls⟩ := ans
  cases lvl with
  | nil =>
    simp only [visitor,List.isEmpty_nil,Bool.cond_true,leaf] at h
    cases e : CNFNetwork.SwitchFactor.sourceCheck K (ctx.1,site,packet) <;> simp_all
  | cons a lvl =>
    change passVisit _ _ _ = some ((jobs,tail),ls) at h
    obtain ⟨ids,bank,rest,_,_,rfl⟩ := (passVisit_iff ..).mp h
    intro child mem
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp mem
    exact Nat.lt_succ_self _

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
  {f : B.Entry → R} {hf : B.IsSolution f}

def packetLimit (N : ℕ) :=
  let n := (2^(4*stepSize B)*N)^4
  2*((S.steps+1)*n + n + 2*n*n)+5

def jobRoom (N : ℕ) := (packetLimit B N + 1)*(B.recordLimit+1)+5

private theorem input_size {a g : ℕ} (X : State a g) (i N : ℕ) (v : X.network.Site) (h : X.network.Half v)
    (lev : i ≤ (S.steps+1)*((2^(4*stepSize B)*N)^4)) (pos : X.positions ≤ (2^(4*stepSize B)*N)^4)
    (degree : 2^a ≤ (2^(4*stepSize B)*N)^4) (width : X.maxWireWidth ≤ (2^(4*stepSize B)*N)^4) :
    size (inputJob X i v h) ≤ packetLimit B N := by
  let n := (2^(4*stepSize B)*N)^4
  have ord : (siteOrder X).length = X.positions := by
    change (siteOrder X).length = Fintype.card X.network.Site
    simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder X).entries
  have site := ((siteOrder X).entries.symm v).isLt.le.trans (ord.le.trans pos)
  have pkt : (packed X v h).length ≤ 2*n*n := (packed_length_le X v h).trans (by gcongr)
  simp only [inputJob,size_prod,size_tally,tally_length,Bits.size_word,packetLimit]
  dsimp only [n] at pkt
  omega

variable {B} (H : ResidentHistory B f hf)
private theorem passes_bound : H.passes.length ≤ (S.steps+1)*gridIndex B H.volume :=
  executeLevels_length B f hf _ _ _ H.path

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels

set_option maxHeartbeats 1200000 in
theorem history_job_size (big : 1 < H.volume.length) (fits : max 1 (slotDegree S) ≤ gridIndex B H.volume)
    (j : Fin H.passes.length) (u : H.passes[j.val].input.network.Site) (h : H.passes[j.val].input.network.Half u) :
    size (inputJob H.passes[j.val].input j.val u h) ≤ packetLimit B H.volume.length := by
  let V := H.passes[j.val]
  let s := gridIndex B H.volume
  have cap := scale_polynomial B big
  have sSmall := (scale_ge B s).trans cap
  have room : 1 ≤ s := (le_max_left ..).trans fits
  have ⟨p,w⟩ := history_size room H.path V (List.getElem_mem (l:=H.passes) j.isLt)
  exact input_size B V.input j.val _ u h
    (j.isLt.le.trans ((passes_bound H).trans (Nat.mul_le_mul_left _ sSmall)))
    (p.trans ((source_positions B room).trans cap)) (V.oldDegree_le.trans (((le_max_right ..).trans fits).trans sSmall)) (w.trans cap)

set_option maxHeartbeats 1200000 in
theorem history_child_bounds (big : 1 < H.volume.length) (fits : max 1 (slotDegree S) ≤ gridIndex B H.volume)
    (j : Fin H.passes.length) :
    let V := H.passes[j.val]
    let r := originReader B f hf V.origin V.term
    ∀ v a, let jobs := WitnessWalk.children r (inputJob V.input j.val) v a
      jobs.length ≤ B.recordLimit ∧ replySize jobs ≤ jobRoom B H.volume.length := by
  intro V r v a jobs
  let id := (outputOrder V).entries.symm v
  have ord := (selected_order V).1 v
  have sizeEq : jobs.length = ((levelLayer B f hf V).ids id).length := by
    change (List.ofFn _).length = (List.ofFn _).length
    simp only [List.length_ofFn]
    rw [ord]
    change _ = ((siteOrder V.input).restrict (fun u => (outputOrder V).entries id = (V.pass.step.term V.term).place u)).length
    rw [show (outputOrder V).entries id = v from (outputOrder V).entries.apply_symm_apply v]
  have cap := TraversalRows.selected_capacity B f hf _ (lanes_fit B _) (source B _) H.path
  rw [selectedLayers_eq_levels] at cap
  have count := sizeEq.le.trans (cap _ (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨V,List.getElem_mem (l:=H.passes) j.isLt,rfl⟩)) id)
  refine ⟨count,?_⟩
  have allSmall (c) (mem : c ∈ jobs) : size c ≤ packetLimit B H.volume.length := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact history_job_size H big fits j _ _
  have bound := size_list_le jobs _ allSmall
  have total := bound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ count) 1)
  simp only [replySize,size_prod,size_nil,jobRoom,Nat.mul_succ]
  omega

end
end OAI.Computability.MultitapeWeakETH.NativeGrid

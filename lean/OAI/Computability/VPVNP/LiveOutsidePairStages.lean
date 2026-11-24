import OAI.Computability.VPVNP.LiveProgramNominationPaths
import OAI.Computability.VPVNP.LiveOutsideTraces
import OAI.Computability.VPVNP.LiveAuxiliaryGuardedCopy
import OAI.Computability.VPVNP.LiveProgramPairExponent
import OAI.Computability.VPVNP.LiveProgramPairAuxiliary
import OAI.Computability.VPVNP.LiveAuxiliaryHeaderPreparation

/-!
# Physical costs outside the compressed first-half pair

These estimates count the actual linked reports, including the dispatch read
and the transfer write on a nonterminal closing call. The auxiliary header
copy visits its populated entries only. Its two reserved exterior capacities
give a uniform upper bound independent of the incident group index.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideBudget

open BurstRAM BurstRAM.PrivateRAM LiveStageLink LiveExponent LiveAuxiliaryHeaders PrimedInputRAM

open scoped Fin.CommRing

variable {w : ℕ}

private theorem linked_terminal_cost {n : ℕ} (next : Fin n → Option (Fin n)) (addr : Word w)
    (s : Fin n) (stop : next s = none) (rs : List (Report w)) :
    RAMBuckets.cost Report.probes (rs.map (linkedReport next addr s)) =
      RAMBuckets.cost Report.probes rs + rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,RAMBuckets.cost,linkedReport_probes,stop,Option.isSome_none,
      Bool.false_eq_true,and_false,ite_false,Nat.add_zero,ih,List.length_cons]
    omega

/-- Exact terminal exponent cost in the actual pair chronology. A digit
call reads three words, writes one counter, and reads the outer tag. -/
theorem exponent_cost (G : PairStages.Group) (t Z : ℕ) (m : Memory G.w) :
    let out := (stageReports G.exponentPub t Z m).map (linkedReport G.nextStage G.addr Stage.exponents)
    RAMBuckets.cost Report.probes out = 6*(t*Z)+2 ∧
      RAMBuckets.cost Report.probes out ≤ 7*(t*Z+1) ∧
      ∀ r ∈ out, r.probes ≤ 5 ∧ r.events.length ≤ 77 := by
  let rs := stageReports G.exponentPub t Z m
  obtain ⟨raw,len,each⟩ := stageResources G.exponentPub t Z m
  have stop : G.nextStage Stage.exponents = none := rfl
  have cost : RAMBuckets.cost Report.probes (rs.map (linkedReport G.nextStage G.addr Stage.exponents)) =
      6*(t*Z)+2 := by
    rw [linked_terminal_cost _ _ _ stop,show RAMBuckets.cost Report.probes rs = _ from raw,
      show rs.length = _ from len]
    omega
  refine ⟨cost,cost.trans_le (by omega),?_⟩
  intro r hr
  obtain ⟨source,hs,rfl⟩ := List.mem_map.mp hr
  obtain ⟨hp,ht⟩ := each source hs
  constructor
  · rw [linkedReport_probes,stop]
    simp; omega
  · exact (linkedReport_length_le G.nextStage G.addr Stage.exponents source).trans (by omega)

/-- The physical pair's packed source interval is bounded by the prescribed
two exterior capacities and the total label count. -/
theorem auxiliary_word_bound (s : LiveHeaderSchedule.Sizes) (i : Fin (2^s.h)) (N t : ℕ) (labels : N ≤ t) :
    populated (PairedChain.lengths s.h s.delta s.advice i) N ≤ auxWords s t := by
  let L := PairedChain.lengths s.h s.delta s.advice i
  have left : L.leftCut ≤ (s.h+1)*s.delta := L.leftFit
  have right : L.rightCut ≤ (s.h+1)*s.delta := L.rightFit
  change 3+2*(s.h+2)+s.advice+L.leftCut+L.rightCut+N ≤ _
  unfold auxWords
  omega

/-- A successful initializer burst is the native 78-event trace publishing
all seven descriptors. It has exactly 23 source probes and then transfers
to the auxiliary copy stage. This holds for arbitrary successful fuel. -/
theorem initializer_cost (G : PairStages.Group) (L : PrimedInputRAM.Lengths) (N : ℕ) (shadow table : Word G.w)
    (src : Fin 7 → Word G.w) (m : Memory G.w) (tableFit : table.val+21 ≤ 2^G.w)
    (left : m (src 0).val = (L.leftCut : Word G.w)) (right : m (src 0+2).val = (L.rightCut : Word G.w))
    (fuel : ℕ) (bits : List Bool) (r : Report G.w)
    (run : let P := (initTable.instantiate G.w (initData L N shadow table src)).program
      execute P fuel (P.start 0) m bits = some r) :
    let linked := linkedReport G.nextStage G.addr Stage.auxiliaryInit r
    bits = [] ∧ r.result = none ∧ linked.probes = 25 ∧ RAMBuckets.cost Report.probes [linked] = 26 ∧
      RAMBuckets.cost Report.probes [linked] ≤ 100 ∧ linked.events.length = 91 := by
  obtain ⟨es,hs,_,_,hlen,hp,_⟩ := LiveAuxiliaryDescriptorInit.init_native L N shadow table (src 0) src 0 m tableFit left right
  let P := (initTable.instantiate G.w (initData L N shadow table src)).program
  have hr : execute P 79 (P.start 0) m [] = some ⟨es,none⟩ := by
    change execute ((LiveOneShot.oneShot (PrimedStackRAM.template LiveAuxiliaryDescriptorInit.ops 27)).instantiate G.w
      (initData L N shadow table src)).program 79 _ _ _ = _
    rw [LiveOneShot.execute_oneShot]
    change (execute (LiveAuxiliaryDescriptorInit.program L N shadow table (src 0) src) 79
      ((LiveAuxiliaryDescriptorInit.program L N shadow table (src 0) src).start 0) m []).map _ = _
    rw [hs]
    rfl
  obtain ⟨hb,rfl⟩ := execute_prefix_unique hr (suffix := bits) (by simpa only [List.nil_append] using run)
  let raw : Report G.w := ⟨es,none⟩
  have pr : (linkedReport G.nextStage G.addr Stage.auxiliaryInit raw).probes = 25 := by
    rw [linkedReport_probes]
    change countProbes es+1+1 = 25
    omega
  refine ⟨hb,rfl,pr,?_,?_,?_⟩
  · change 1+(linkedReport G.nextStage G.addr Stage.auxiliaryInit raw).probes+0 = 26
    rw [pr]
  · change 1+(linkedReport G.nextStage G.addr Stage.auxiliaryInit raw).probes+0 ≤ 100
    rw [pr]; decide
  · change ((dispatchEvents G.addr Stage.auxiliaryInit) ++ es ++ transferEvents G.addr Stage.auxiliaryCopy).length = 91
    simp only [List.length_append,hlen]
    rfl

/-- Every actually nominated histogram has one linked burst per production
label and one closing burst, each costing three units. -/
theorem nomination_resources (G : PairStages.Group) (fit : PairStages.Group.Nominations.Fits G)
    (m : Memory G.w) (tag : G.tagged Stage.nominations m) (μ : PairStages.Group.Nominations.Nom G) :
    let logs := (PairStages.Group.Nominations.indexed G fit m tag).logs μ
    OutsideTraces.Resources logs (4*(G.constants.labels.eval G.g+1)) 3 (5*(2*G.g.d)+23) := by
  dsimp only
  constructor
  · rw [PairStages.Group.Nominations.logs_cost]
    change (G.constants.grammarLabels.eval G.g+1)*3 ≤ 4*(G.constants.grammarLabels.eval G.g+G.constants.motifLabels+1)
    omega
  · intro r hr
    rw [PairStages.Group.Nominations.logs_probes G fit m tag μ r hr]
  · intro r hr
    have ht : r.events.length ∈ ((PairStages.Group.Nominations.indexed G fit m tag).logs μ).map (fun u => u.events.length) := List.mem_map.mpr ⟨r,hr,rfl⟩
    rw [PairStages.Group.Nominations.logs_lengths G fit m tag μ] at ht
    rcases List.mem_append.mp ht with ha | hc
    · rw [(List.mem_replicate.mp ha).2]
    · rw [List.mem_singleton.mp hc]
      omega

theorem exponent_resources (G : PairStages.Group) (t Z : ℕ) (m : Memory G.w) :
    OutsideTraces.Resources ((stageReports G.exponentPub t Z m).map (linkedReport G.nextStage G.addr Stage.exponents))
      (7*(t*Z+1)) 6 78 := by
  obtain ⟨_,hc,each⟩ := exponent_cost G t Z m
  exact ⟨hc, fun r hr => by have hp := (each r hr).1; omega,
    fun r hr => by have ht := (each r hr).2; omega⟩

theorem initializer_resources (G : PairStages.Group) (L : PrimedInputRAM.Lengths) (N : ℕ) (shadow table : Word G.w)
    (src : Fin 7 → Word G.w) (m : Memory G.w) (tableFit : table.val+21 ≤ 2^G.w)
    (left : m (src 0).val = (L.leftCut : Word G.w)) (right : m (src 0+2).val = (L.rightCut : Word G.w))
    (fuel : ℕ) (bits : List Bool) (r : Report G.w)
    (run : let P := (initTable.instantiate G.w (initData L N shadow table src)).program
      execute P fuel (P.start 0) m bits = some r) :
    OutsideTraces.Resources [linkedReport G.nextStage G.addr Stage.auxiliaryInit r] 100 26 92 := by
  obtain ⟨_,_,hp,_,cost,clock⟩ := initializer_cost G L N shadow table src m tableFit left right fuel bits r run
  refine ⟨cost,?_,?_⟩
  · intro a ha
    obtain rfl := List.mem_singleton.mp ha
    rw [hp]
  · intro a ha
    obtain rfl := List.mem_singleton.mp ha
    rw [clock]

private theorem cost_length {α : Type*} (p : α → ℕ) (xs : List α) (b : ℕ)
    (each : ∀ x ∈ xs, 1+p x ≤ b) : RAMBuckets.cost p xs ≤ b*xs.length := by
  induction xs with
  | nil => simp [RAMBuckets.cost]
  | cons x xs ih =>
    have hx := each x (by simp)
    have ht := ih fun a ha => each a (List.mem_cons_of_mem _ ha)
    simp only [RAMBuckets.cost,List.length_cons,Nat.mul_succ]
    omega

/-- Every accepting run through the runtime-guarded copy component has
precisely the native sparse-copy reports. Dispatch and handoff are included
in all three bounds, and arbitrary choices cannot shorten the required copy. -/
theorem copy_resources (G : PairStages.Group) (s : LiveHeaderSchedule.Sizes) (i : Fin (2^s.h)) (t : ℕ)
    {base : ℕ} {desc : Word G.w} {src : Fin 7 → Word G.w} {hist : List (Word G.w)} (labels : hist.length ≤ t)
    {hdr : Header (PairedChain.lengths s.h s.delta s.advice i) → Bool} {m : Memory G.w}
    (fit : base+span (PairedChain.lengths s.h s.delta s.advice i) hist.length ≤ 2^G.w)
    (width : populated (PairedChain.lengths s.h s.delta s.advice i) hist.length < 2^G.w)
    (sep : Separated desc base (PairedChain.lengths s.h s.delta s.advice i) hist.length src fit)
    (ready : Prepared desc base (PairedChain.lengths s.h s.delta s.advice i) hdr hist src m)
    (fuel : ℕ) (room : 68 ≤ fuel)
    (outside : G.addr.val < base ∨ base+span (PairedChain.lengths s.h s.delta s.advice i) hist.length ≤ G.addr.val)
    {bs rs} (run : let P := (LiveAuxiliaryStages.copy.instantiate G.w (LiveAuxiliaryStages.copyData desc)).program
      runSegment P fuel (some 0) m bs = some rs) (halt : endState (some (0 : Word G.w)) rs = none) :
    OutsideTraces.Resources (rs.map (linkedReport G.nextStage G.addr Stage.auxiliaryCopy)) (16*(auxWords s t+1)) 15 115 := by
  obtain ⟨active,closed,hraw,hh,_,hlen,each,hclosed,pclosed,_,_⟩ :=
    LiveAuxiliaryStages.guarded_copy_native fit width sep fuel room G.addr outside ready
  obtain ⟨_,rfl⟩ := accepted_empty_unique hraw hh run halt
  let out := (active++[closed]).map (linkedReport G.nextStage G.addr Stage.auxiliaryCopy)
  have per (r : Report G.w) (hr : r ∈ out) : 1+r.probes ≤ 15 ∧ r.events.length+1 ≤ 115 := by
    obtain ⟨raw,hraw,rfl⟩ := List.mem_map.mp hr
    have bounds : raw.probes ≤ 12 ∧ raw.events.length < 68 := by
      rcases List.mem_append.mp hraw with live | done
      · exact ⟨(each raw live).2.1,(each raw live).1⟩
      · obtain rfl := List.mem_singleton.mp done
        omega
    have hlen := linkedReport_length_le G.nextStage G.addr Stage.auxiliaryCopy raw
    change _ ≤ raw.events.length + 2*21+5 at hlen
    rw [linkedReport_probes]
    split <;> omega
  refine ⟨?_,fun r h => (per r h).1, fun r h => (per r h).2⟩
  have hc := cost_length Report.probes out 15 (fun r h => (per r h).1)
  have n : out.length = active.length+1 := by simp [out]
  have small := auxiliary_word_bound s i hist.length t labels
  change RAMBuckets.cost Report.probes out ≤ _
  omega

open PairStages.Group.Auxiliary

/-- Resource bound on the actual initializer logs of an indexed chronology.
Its single source report follows from native execution on the seven producer
arrays, so this applies to any indexing of the same component paths. -/
theorem initializer_logs_resources (G : PairStages.Group) (i : Fin (2^(sizes G).h)) {m : Memory G.w}
    {hist : List (Word G.w)} {hdr : Header (pairLengths G i) → Bool}
    (hlen : hist.length = G.constants.grammarLabels.eval G.g)
    (areas : Areas (desc G) (shadow G) (pairLengths G i) hist.length (source G))
    (inputs : InputArrays (pairLengths G i) hdr hist (source G) m) {ι : Type*}
    (A : PairStages.Group.Indexed G Stage.auxiliaryInit m ι) (u : ι) :
    OutsideTraces.Resources (A.logs u) 100 26 92 := by
  let L := pairLengths G i
  let path := A.traces u
  let rs := ordinaryReports path
  let f := G.clockAt Stage.auxiliaryInit
  let P := (initTable.instantiate G.w (initData L hist.length (shadow G) (desc G) (source G))).program
  have hr : runSegment P f (some 0) m path.val = some rs := by
    have h := (PairStages.Group.component_segment G Stage.auxiliaryInit f (some 0) m path.val).symm.trans (ordinaryRun path)
    change runSegment (initTable.instantiate G.w
      (Pieces.word G.g G.lit ∘ InputOperand.geometry ∘ StageOperands.auxiliary G.constants)).program _ _ _ _ = _ at h
    rwa [init_data G i hist hlen] at h
  have hh : endState (some 0) rs = none := path.property.choose_spec.2.1
  have left : m (source G 0).val = (L.leftCut : Word G.w) := by simpa [cutLength] using inputs.lengths 0
  have right : m (source G 0+2).val = (L.rightCut : Word G.w) := by simpa [cutLength] using inputs.lengths 2
  change OutsideTraces.Resources (rs.map (linkedReport G.nextStage G.addr Stage.auxiliaryInit)) 100 26 92
  cases stream : path.val with
  | nil =>
    rw [stream,runSegment,Option.some.injEq] at hr
    rw [← hr] at hh
    contradiction
  | cons b bs =>
    rw [stream,runSegment] at hr
    cases he : execute P f (P.start 0) m b with
    | none => simp [he] at hr
    | some rep =>
      rw [he,Option.map_eq_some_iff] at hr
      obtain ⟨tail,ht,same⟩ := hr
      have cost := initializer_cost G L hist.length (shadow G) (desc G) (source G) m areas.tableFit left right f b rep he
      rw [cost.2.1] at ht
      cases bs with
      | cons _ _ => contradiction
      | nil =>
        change some [] = some tail at ht
        obtain rfl : tail = [] := (Option.some.inj ht).symm
        rw [← same]
        exact initializer_resources G L hist.length (shadow G) (desc G) (source G) m areas.tableFit left right f b rep he

/-- Resource bound on the actual copy logs of any indexed chronology.
The public-bank equality recovers the guarded copy component at this stage. -/
theorem copy_logs_resources (G : PairStages.Group) (i : Fin (2^(sizes G).h)) {m : Memory G.w}
    {hist : List (Word G.w)} {hdr : Header (pairLengths G i) → Bool}
    (labels : hist.length ≤ G.constants.labels.eval G.g)
    (areas : Areas (desc G) (shadow G) (pairLengths G i) hist.length (source G))
    (ready : Prepared (desc G) (shadow G).val (pairLengths G i) hdr hist (source G) m)
    (clock : 68 ≤ G.clockAt Stage.auxiliaryCopy) (before : G.addr.val < (shadow G).val)
    {ι : Type*} (A : PairStages.Group.Indexed G Stage.auxiliaryCopy m ι) (u : ι) :
    OutsideTraces.Resources (A.logs u) (16*(auxWords (sizes G) (G.constants.labels.eval G.g)+1)) 15 115 := by
  let path := A.traces u
  let f := G.clockAt Stage.auxiliaryCopy
  have hr := (PairStages.Group.component_segment G Stage.auxiliaryCopy f (some 0) m path.val).symm.trans (ordinaryRun path)
  change runSegment (LiveAuxiliaryStages.copy.instantiate G.w
    (Pieces.word G.g G.lit ∘ InputOperand.geometry ∘ StageOperands.auxiliaryCopy G.constants)).program _ _ _ _ = _ at hr
  rw [copy_data] at hr
  exact copy_resources G (sizes G) i _ labels areas.shadowFit areas.countFit areas.separated ready f clock
    (Or.inl before) hr path.property.choose_spec.2.1

end LiveProgram.OutsideBudget

end VPVNP
end Computability
end OAI

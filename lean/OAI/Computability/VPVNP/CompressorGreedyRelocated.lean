import OAI.Computability.VPVNP.CompressorRecordGreedyDirectory
import OAI.Computability.VPVNP.CompressorRecordsSchedule
import OAI.Computability.VPVNP.PrimedCounterRename

/-!
# Greedy preparation from an active scheduler frame

The worker receives the slot numbers followed by eight current-level controls.
It loads those controls into registers and runs the shared native record writer.
Both color and tag directories use the same placement of public operands.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy.Relocated

open BurstRAM BurstRAM.PrivateRAM Compression PrimedStackRAM

variable {w N width d : ℕ} {V : Type*}

/-- Control indices are those of the original greedy preparation block. -/
def controls (L : WalkLayout w N width) (T : PortTables w) (j : Fin 8) : Word w :=
  (controlWords L T).get j

/-- Public operand bank consisting of the slot numbers followed by the eight relocated walk
controls. -/
def publicWords (d : ℕ) (L : WalkLayout w N width) (T : PortTables w) :
    Fin ((d+1)+8) → Word w :=
  Fin.addCases (slotNumbers w d) (controls L T)

private def loadControls (d : ℕ) : List (Op 13 ((d+1)+8)) :=
  [.stateWord 0, .constant 11 1,
   .publicWord 2 ((0 : Fin 8).natAdd (d+1)), .publicWord 3 ((1 : Fin 8).natAdd (d+1)),
   .publicWord 4 ((2 : Fin 8).natAdd (d+1)), .publicWord 5 ((3 : Fin 8).natAdd (d+1)),
   .publicWord 6 ((4 : Fin 8).natAdd (d+1)), .publicWord 7 ((5 : Fin 8).natAdd (d+1)),
   .publicWord 8 ((6 : Fin 8).natAdd (d+1)), .publicWord 9 ((7 : Fin 8).natAdd (d+1))]

/-- Preparation instructions that load the relocated controls before running the greedy record
builder. -/
def prepareCode (rows : OperandRows d) : List (Op 13 ((d+1)+8)) :=
  loadControls d ++ (prepareBody rows).map (PrimedCounter.renameOp id (Fin.castAdd 8))

/-- Schedulable pass that builds the relocated greedy records and returns its cursor in
register zero. -/
abbrev preparePass (rows : OperandRows d) : Schedule.Pass := ⟨_,_,_,template (prepareCode rows) 0⟩

private theorem loaded (L : WalkLayout w N width) (T : PortTables w) (m : Memory w)
    (s : Word w) (d : ℕ) :
    ∃ es rs, trace (publicWords d L T) s (loadControls d) (fun _ ↦ 0) m = some (es,rs,m) ∧
      es.length = 10 ∧ countProbes es = 0 ∧ RowInput T s 0 rs ∧ rs 11 = 1 ∧
      rs 8 = L.base 0 ∧ rs 9 = Fin.ofNat _ (2+width) := by
  simp (config := {decide := true}) [loadControls,trace,Op.effect,countProbes,Function.update,
    publicWords,Fin.addCases_right]
  exact ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩

private theorem trace_slots {r : ℕ} (L : WalkLayout w N width) (T : PortTables w)
    (s : Word w) (ops : List (Op r (d+1))) (rs : Regs w r) (m : Memory w) :
    trace (publicWords d L T) s (ops.map (PrimedCounter.renameOp id (Fin.castAdd 8))) rs m =
      trace (slotNumbers w d) s ops rs m := by
  induction ops generalizing rs m with
  | nil => rfl
  | cons op ops ih =>
    have effect : (PrimedCounter.renameOp id (Fin.castAdd 8) op).effect (publicWords d L T) s rs m =
        op.effect (slotNumbers w d) s rs m := by
      cases op <;> first | rfl | simp [PrimedCounter.renameOp,Op.effect,publicWords]
    simp only [List.map_cons,trace,effect,ih]

/-- A frame-based preparation call writes the same label and record as the
original greedy initializer, including the pointer to the next record. -/
theorem prepare_one (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows : OperandRows d) (m : Memory w) (i : Fin N)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (space : L.limit < 2^w) (outside : GraphOutside (d := d) L T order)
    (size : (rowWords T G order (order.symm i) rows).length = width) :
    let P := ((preparePass rows).table.instantiate w (publicWords d L T)).program
    let ptrs := fun k : Fin N ↦ rowWords T G order (order.symm k) rows
    ∃ es, execute P (1+(prepareCode rows).length) (P.start (Fin.ofNat _ i.val)) m [] =
        some ⟨es,some (Fin.ofNat _ (i.val+1))⟩ ∧
      after m es = writeRow (writeMemory m (L.label i) 0) (L.base i.val) (L.record ptrs i) ∧
      es.length ≤ 22+8*rows.length+6*width ∧ countProbes es = 3+rows.length+width := by
  let s : Word w := Fin.ofNat _ i.val
  obtain ⟨a,r,ha,hla,hpa,hr,hu,hfirst,hstride⟩ := loaded L T m s d
  obtain ⟨b,last,hb,hresult,hlen,hprobes⟩ :=
    prepareBody_trace L T G order rows m i labels rep space outside size r hr hu hfirst hstride
  have he : trace (publicWords d L T) s (prepareCode rows) (fun _ ↦ 0) m =
      some (a++b,last,writeRow (writeMemory m (L.label i) 0) (L.base i.val)
        (L.record (fun k ↦ rowWords T G order (order.symm k) rows) i)) := by
    rw [prepareCode,trace_append,ha]
    simp only [Option.bind_some,trace_slots]
    rw [hb]; rfl
  refine ⟨a++b,?_,trace_after he,?_,?_⟩
  · let M := (template (prepareCode rows) 0).instantiate w (publicWords d L T)
    change execute M.program (1+(prepareCode rows).length) ⟨M.entry,s,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
    dsimp only [M]
    rw [execute_template,run_eq_trace,he]
    simp [hresult]
  · rw [List.length_append,hla]; omega
  · rw [probes_append,hpa,hprobes,Nat.zero_add]

/-- The completed native scan installs the directory from arbitrary initial
memory. All external probes go to the mate arrays, labels and records. -/
theorem prepare_directory (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows : OperandRows d) (m : Memory w)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (space : L.limit < 2^w) (outside : GraphOutside (d := d) L T order)
    (size : ∀ i : Fin N, (rowWords T G order (order.symm i) rows).length = width) :
    let P := ((preparePass rows).table.instantiate w (publicWords d L T)).program
    let ptrs := fun i : Fin N ↦ rowWords T G order (order.symm i) rows
    ∃ rs, runSegment P (1+(prepareCode rows).length) (some 0) m (List.replicate N []) = some rs ∧
      endState (some 0) rs = some (Fin.ofNat _ N) ∧ after m (eventLog rs) = L.initialMemory ptrs m ∧
      rs.length = N ∧ RAMBuckets.cost Report.probes rs = N*(4+rows.length+width) ∧
      ∀ r ∈ rs, r.events.length ≤ 22+8*rows.length+6*width ∧ r.probes = 3+rows.length+width := by
  let ptrs := fun i : Fin N ↦ rowWords T G order (order.symm i) rows
  let P := ((preparePass rows).table.instantiate w (publicWords d L T)).program
  have call (i : Fin N) := prepare_one L T G order rows (L.prefixMemory ptrs m i.val) i labels
    (L.prefixMemory_tables ptrs m i.isLt.le rep outside) space outside (size i)
  have whole := WalkLayout.prepare_segment (N := N) P (1+(prepareCode rows).length)
    (3+rows.length+width) (22+8*rows.length+6*width) (L.prefixMemory ptrs m) (fun i ↦ by
      obtain ⟨es,he,hm,hs,hp⟩ := call i
      exact ⟨es,he,hm.trans (L.write_prefixMemory ptrs m size i),hs,hp⟩) 0 N (by omega)
  have zero : Fin.ofNat _ 0 = (0 : Word w) := Fin.ext (Nat.zero_mod _)
  have cost : 1+(3+rows.length+width) = 4+rows.length+width := by omega
  have charge : (fun r : Report w ↦ countProbes r.events) = Report.probes := rfl
  rw [charge] at whole
  simp only [WalkLayout.prefixMemory_zero,Nat.zero_add,WalkLayout.prefixMemory_full,zero,cost] at whole
  obtain ⟨rs,hr,hs,hm,hn,hp,hw⟩ := whole
  exact ⟨rs,hr,hs,hm,hn,hp,hw⟩

open scoped Fin.CommRing

private theorem valid_segment {q : ℕ} {A : Type*} (C : Schedule.Catalog q) (worker : Fin q)
    (ports : Schedule.Ports w) (pub : Fin (C worker).params → Word w)
    (P : Program w A) (fuel N : ℕ) (mem : ℕ → Memory w) (fit : N < 2^w)
    (ready : ∀ k, k ≤ N → Schedule.Ready C worker ports pub (N : Word w) (mem k))
    (step : ∀ i : Fin N, ∃ es, execute P fuel (P.start (Fin.ofNat _ i.val)) (mem i.val) [] =
        some ⟨es,some (Fin.ofNat _ (i.val+1))⟩ ∧ after (mem i.val) es = mem (i.val+1))
    (k n : ℕ) (stop : k+n=N) (rs : List (Report w))
    (run : runSegment P fuel (some (Fin.ofNat _ k)) (mem k) (List.replicate n []) = some rs) :
    Schedule.ValidTrace C worker ports pub (N : Word w) (Fin.ofNat _ k) (mem k) rs := by
  induction n generalizing k rs with
  | zero =>
    have h : rs = [] := (Option.some.inj run).symm
    subst rs
    simp only [Nat.add_zero] at stop
    subst k
    exact ⟨ready N le_rfl,le_rfl⟩
  | succ n ih =>
    have hk : k < N := by omega
    obtain ⟨es,he,hm⟩ := step ⟨k,hk⟩
    rw [List.replicate_succ,runSegment,he] at run
    change (runSegment P fuel (some (Fin.ofNat _ (k+1))) (after (mem k) es)
      (List.replicate n [])).map _ = some rs at run
    rw [hm] at run
    obtain ⟨tail,ht,rfl⟩ := Option.map_eq_some_iff.mp run
    refine ⟨ready k hk.le,?_,Fin.ofNat _ (k+1),rfl,?_⟩
    · change k % (2^w) < N % (2^w)
      rwa [Nat.mod_eq_of_lt (hk.trans fit),Nat.mod_eq_of_lt fit]
    · change Schedule.ValidTrace C worker ports pub _ _ (after (mem k) es) tail
      rw [hm]
      exact ih _ (by omega) _ ht

/-- The preparation reports meet the linked worker's exclusive guard. Each
prefix writes only the walk allocation, so the stop, parameters and tag can
be read from the same external frame at every call. -/
theorem prepare_valid {q : ℕ} (C : Schedule.Catalog q) (worker : Fin q) (ports : Schedule.Ports w)
    (pub : Fin (C worker).params → Word w) (L : WalkLayout w N width) (T : PortTables w)
    (G : SlotGraph V d) (order : V ≃ Fin N) (rows : OperandRows d) (m : Memory w)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (space : L.limit < 2^w) (outside : GraphOutside (d := d) L T order)
    (size : ∀ i : Fin N, (rowWords T G order (order.symm i) rows).length = width)
    (ready : Schedule.Ready C worker ports pub (N : Word w) m)
    (tag : ports.tag.val < L.origin ∨ L.limit ≤ ports.tag.val)
    (frame : ∀ j : Fin ((C worker).params+1), (ports.activeFrame+(j.val : Word w)).val < L.origin ∨
      L.limit ≤ (ports.activeFrame+(j.val : Word w)).val)
    (rs : List (Report w))
    (native : let P := ((preparePass rows).table.instantiate w (publicWords d L T)).program
      runSegment P (1+(prepareCode rows).length) (some 0) m (List.replicate N []) = some rs) :
    Schedule.ValidTrace C worker ports pub (N : Word w) 0 m rs := by
  let ptrs := fun i : Fin N ↦ rowWords T G order (order.symm i) rows
  let mem := L.prefixMemory ptrs m
  let P := ((preparePass rows).table.instantiate w (publicWords d L T)).program
  have fresh (k : ℕ) (hk : k ≤ N) : Schedule.Ready C worker ports pub (N : Word w) (mem k) := by
    have keep {z : ℕ} (hz : z < L.origin ∨ L.limit ≤ z) : mem k z = m z :=
      L.prefixMemory_outside ptrs m hk hz
    refine ⟨(keep tag).trans ready.1,?_,?_⟩
    · exact (keep (by simpa using frame 0)).trans ready.2.1
    · funext i
      exact (keep (frame i.succ)).trans (congrFun ready.2.2 i)
  have one (i : Fin N) := prepare_one L T G order rows (mem i.val) i labels
    (L.prefixMemory_tables ptrs m i.isLt.le rep outside) space outside (size i)
  have zero : Fin.ofNat _ 0 = (0 : Word w) := Fin.ext (Nat.zero_mod _)
  have start : mem 0 = m := L.prefixMemory_zero ptrs m
  rw [← start,← zero]
  refine valid_segment C worker ports pub P (1+(prepareCode rows).length) N mem
    (by unfold WalkLayout.limit at space; omega) fresh ?_ 0 N (Nat.zero_add N) rs ?_
  · intro i
    obtain ⟨es,he,hm,_,_⟩ := one i
    exact ⟨es,he,hm.trans (L.write_prefixMemory ptrs m size i)⟩
  · rwa [start,zero]

end CompressorRecords.Greedy.Relocated

end VPVNP
end Computability
end OAI

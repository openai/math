import OAI.Computability.VPVNP.CompressorSlotState
import OAI.Computability.VPVNP.CompressorRecordsOrdinalFootprint
import OAI.Computability.VPVNP.RAMChoicePrefix

/-!
# Probe addresses in the shrinking slot array passes

The append pass reads the owner and count columns and writes the count and row
columns. Scattering the resulting real rows, or the base-mate permutation, reads
the forward column and writes the inverse column. These bounds apply to the
actual chronological event log, so a scheduler can change unrelated control cells
and replay the same native calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotFillFootprint

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport
open private collectPreimage_reject from OAI.Computability.VPVNP.CompressorSlotFrames
open private countAt_val rowAt_val from OAI.Computability.VPVNP.CompressorRecordPreimageScan
open private parameter_values from OAI.Computability.VPVNP.CompressorSlotSchedule
open private address_val word_succ from OAI.Computability.VPVNP.CompressorSlotScatter

variable {w : ℕ}

/-- The half-open physical range of a contiguous column. -/
def InColumn (base count addr : ℕ) : Prop := base ≤ addr ∧ addr < base + count

/-- An address in the owner column or count column that the field append pass may read. -/
def AppendReads (p : Fin 6 → Word w) (addr : ℕ) : Prop :=
  InColumn (p 1).val (p 0).val addr ∨ InColumn (p 3).val (p 2).val addr

/-- An address in the count column or the rectangular row table that the field append pass may
write. -/
def AppendWrites (p : Fin 6 → Word w) (addr : ℕ) : Prop :=
  InColumn (p 3).val (p 2).val addr ∨ InColumn (p 5).val ((p 2).val * (p 4).val) addr

private theorem append_visit {p : Fin 6 → Word w} (regions : RowRegions p) (m : Memory w) (i : Word w)
    (hi : i < p 0) (ho : ownerAt p m i < p 2) (hcap : m (countAt p (ownerAt p m i)).val < p 4) :
    Reads (AppendReads p) (collectEvents p m i) ∧ Writes (AppendWrites p) (collectEvents p m i) := by
  let u := ownerAt p m i
  let len := m (countAt p u).val
  have hb := regions.ownersBeforeCounts
  have hw := (p 3).isLt
  have hfit := regions.rowsFit
  change i.val < (p 0).val at hi
  change u.val < (p 2).val at ho
  change len.val < (p 4).val at hcap
  have oaddr : InColumn (p 1).val (p 0).val (p 1 + i).val := by
    rw [InColumn, Fin.val_add, Nat.mod_eq_of_lt (by omega)]; omega
  have caddr : InColumn (p 3).val (p 2).val (countAt p u).val := by
    rw [InColumn, countAt_val regions ho]; omega
  have mul := Nat.mul_le_mul_right (p 4).val (Nat.succ_le_of_lt ho)
  rw [Nat.succ_mul] at mul
  have daddr : InColumn (p 5).val ((p 2).val*(p 4).val) (rowAt p u + len).val := by
    rw [InColumn, Fin.val_add, rowAt_val regions ho, Nat.mod_eq_of_lt (by omega)]; omega
  constructor <;> intro a v h
  · simp only [collectEvents, List.mem_cons, List.not_mem_nil, or_false, false_or, reduceCtorEq,
      Event.read.injEq] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact .inl oaddr
    · exact .inr caddr
  · simp only [collectEvents, List.mem_cons, List.not_mem_nil, or_false, false_or, reduceCtorEq,
      Event.write.injEq] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact .inr daddr
    · exact .inl caddr

/-- Native append bounds for a successful partial or complete scan. The guards
on each call suffice for these bounds even with arbitrary starting memory. -/
theorem append_run {p : Fin 6 → Word w} (regions : RowRegions p) {m : Memory w} {i : Word w}
    {steps : ℕ} {rs : List (Report w)}
    (run : runSegment ((template collectPreimage 3).instantiate w p).program 23 (some i) m
      (List.replicate steps []) = some rs) :
    Reads (AppendReads p) (eventLog rs) ∧ Writes (AppendWrites p) (eventLog rs) := by
  induction steps generalizing m i rs with
  | zero =>
    change some [] = some rs at run
    cases run
    simp [eventLog, Reads, Writes]
  | succ steps ih =>
    rw [List.replicate_succ, runSegment] at run
    by_cases ok : i < p 0 ∧ ownerAt p m i < p 2 ∧ m (countAt p (ownerAt p m i)).val < p 4
    · rw [collectPreimage_native p m i ok.1 ok.2.1 ok.2.2] at run
      obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp run
      obtain ⟨tr, tw⟩ := ih ht
      obtain ⟨hr, hw⟩ := append_visit regions m i ok.1 ok.2.1 ok.2.2
      exact ⟨fun a v h => (List.mem_append.mp h).elim (hr a v) (tr a v),
        fun a v h => (List.mem_append.mp h).elim (hw a v) (tw a v)⟩
    · rw [collectPreimage_reject p m i ok] at run
      cases run

/-- Bounds for the native inverse pass with a bounded forward column. The values
may repeat. Each write lies in the disjoint inverse interval, so all remaining
source reads see their initial values. -/
theorem scatter_run_bounded {n cap : ℕ} {p : Fin 2 → Word w} (regions : SlotScatter.Regions p n cap)
    {m : Memory w} (bounded : ∀ i : Fin n, (m ((p 0).val+i.val)).val < cap)
    {k steps : ℕ} (size : k + steps ≤ n) {rs : List (Report w)}
    (run : runSegment ((template SlotScatter.visit 0).instantiate w p).program 10
      (some (Fin.ofNat (2^w) k)) m (List.replicate steps []) = some rs) :
    Reads (InColumn (p 0).val n) (eventLog rs) ∧ Writes (InColumn (p 1).val cap) (eventLog rs) := by
  let M := (template SlotScatter.visit 0).instantiate w p
  let I := fun (_ : ℕ) (mem : Memory w) => ∀ i : Fin n, (mem ((p 0).val+i.val)).val < cap
  apply OrdinalRun.footprint M.program 10 (Fin.ofNat (2^w)) n I _ _ _ k (List.replicate steps [])
    m rs (by simpa only [List.length_replicate] using size) bounded run
  intro j hj mem hmem bits rep he
  let idx := Fin.ofNat (2^w) j
  let v := mem (p 0 + idx).val
  have hs : (p 0 + idx).val = (p 0).val + j := address_val (p 0) regions.fieldsFit ⟨j,hj⟩
  have hv : v.val < cap := by change (mem (p 0 + idx).val).val < cap; rw [hs]; exact hmem ⟨j,hj⟩
  have hf := regions.inverseFit
  have hd : (p 1 + v).val = (p 1).val + v.val := by rw [Fin.val_add,Nat.mod_eq_of_lt (by omega)]
  have hr := (execute_prefix_unique (suffix := bits) (SlotScatter.visit_native p mem idx) he).2
  subst rep
  refine ⟨congrArg some (word_succ j), ?_, ?_, ?_⟩
  · intro b
    have hb := b.isLt
    have sep := regions.disjoint
    have neq : (p 0).val+b.val ≠ (p 1 + v).val := by rw [hd]; omega
    change (writeMemory mem (p 1+v) idx ((p 0).val+b.val)).val < cap
    rw [writeMemory,ite_eq_right neq]; exact hmem b
  · intro a x h
    simp only [SlotScatter.events,List.mem_cons,List.not_mem_nil,or_false,false_or,reduceCtorEq,Event.read.injEq] at h
    obtain ⟨rfl,_⟩ := h
    change InColumn _ _ (p 0 + idx).val
    rw [InColumn,hs]; omega
  · intro a x h
    simp only [SlotScatter.events,List.mem_cons,List.not_mem_nil,or_false,false_or,reduceCtorEq,Event.write.injEq] at h
    obtain ⟨rfl,_⟩ := h
    change InColumn _ _ (p 1 + v).val
    rw [InColumn,hd]; omega

/-- Footprint of the reports returned by `SlotScatter.run`, for any occupied
endpoint embedding. -/
theorem scatter_run {n cap : ℕ} {p : Fin 2 → Word w} (regions : SlotScatter.Regions p n cap)
    (field : Fin n ↪ Fin cap) {m : Memory w}
    (stored : ∀ i : Fin n, m ((p 0).val+i.val) = Fin.ofNat _ (field i).val)
    {rs : List (Report w)} (run : runSegment ((template SlotScatter.visit 0).instantiate w p).program 10
      (some 0) m (List.replicate n []) = some rs) :
    Reads (InColumn (p 0).val n) (eventLog rs) ∧ Writes (InColumn (p 1).val cap) (eventLog rs) :=
  scatter_run_bounded regions (fun i => by rw [stored i]; exact (Nat.mod_le ..).trans_lt (field i).isLt)
    (k := 0) (by simp) run

/-- In the layout used by the slot builder, the append call's readable interval
ends at the row base, and its writable interval begins after the owner stream. -/
theorem appendFields {base A B deg : ℕ} (fit : base+A+(B+A)+(B+A)*deg < 2^w)
    (hdw : deg < 2^w) {m : Memory w} {rs : List (Report w)}
    (run : runSegment ((template collectPreimage 3).instantiate w (SlotSchedule.parameters w base A B deg)).program
      23 (some 0) m (List.replicate A []) = some rs) :
    Reads (InColumn base (A+(B+A))) (eventLog rs) ∧
      Writes (InColumn (base+A) ((B+A)+(B+A)*deg)) (eventLog rs) := by
  let p := SlotSchedule.parameters w base A B deg
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := parameter_values fit hdw
  have reg : RowRegions p := ⟨by rw [h1,h0,h3], by rw [h3,h2,h5], by rw [h5,h2,h4]; omega⟩
  obtain ⟨rd,wr⟩ := append_run reg run
  constructor <;> intro a v ha
  · have r := rd a v ha
    simp only [AppendReads,InColumn,p,h1,h0,h3,h2] at r
    unfold InColumn; omega
  · have r := wr a v ha
    simp only [AppendWrites,InColumn,p,h3,h2,h5,h4] at r
    unfold InColumn; omega

variable {E : Type*} [Fintype E] {A B : ℕ}

/-- Bounds for scattering a rectangular endpoint table with its mathematical
ordering. Only the forward part of the table is needed as input. -/
theorem invertFields {deg : ℕ} (D : SlotSchedule.Directory E A B)
    (hc : ∀ b, Fintype.card {e // D.owner e = b} = deg)
    {p : Fin 2 → Word w} (regions : SlotScatter.Regions p (B*deg) A) {m : Memory w}
    (bySlot : ∀ e, m ((p 0).val+(SlotSchedule.sortedFields D deg hc e).val) = Fin.ofNat _ (D.address e).val)
    {rs : List (Report w)} (run : runSegment ((template SlotScatter.visit 0).instantiate w p).program
      10 (some 0) m (List.replicate (B*deg) []) = some rs) :
    Reads (InColumn (p 0).val (B*deg)) (eventLog rs) ∧ Writes (InColumn (p 1).val A) (eventLog rs) := by
  let order := SlotSchedule.sortedFields D deg hc
  apply scatter_run regions (order.symm.toEmbedding.trans D.address) _ run
  intro i
  have he := bySlot (order.symm i)
  change m ((p 0).val+(order (order.symm i)).val) = _ at he
  rwa [order.apply_symm_apply] at he

/-- Scattering immediately after the actual append pass uses the bounded entries
that pass produced. Equality of the native reports identifies its physical output
with the `PreimagesAt` postcondition from `fill_run`. -/
theorem invertFields_after_append (D : SlotSchedule.Directory E A B) {base deg : ℕ}
    (hdeg : 0 < deg) (hdw : deg < 2^w) (hc : ∀ b, Fintype.card {e // D.owner e = b} = deg)
    (fit : base+A+(B+A)+(B+A)*deg+A < 2^w) {m : Memory w}
    (owners : ∀ i : Word w, i.val < A → m (base+i.val) = D.wordOwner i)
    (zero : ∀ u : Word w, u.val < B+A → m (base+A+u.val) = 0)
    {fs ss : List (Report w)}
    (fill : runSegment ((template collectPreimage 3).instantiate w (SlotSchedule.parameters w base A B deg)).program
      23 (some 0) m (List.replicate A []) = some fs)
    (scatter : runSegment ((template SlotScatter.visit 0).instantiate w (SlotSchedule.scatterParameters w base A B deg)).program
      10 (some 0) (after m (eventLog fs)) (List.replicate (B*deg) []) = some ss) :
    Reads (InColumn (base+A+(B+A)) (B*deg)) (eventLog ss) ∧
      Writes (InColumn (base+A+(B+A)+(B+A)*deg) A) (eventLog ss) := by
  obtain ⟨rs,hr,rows,_⟩ := SlotSchedule.fill_run D hdeg hdw (fun b => (hc b).le) (by omega) m owners zero
  obtain rfl := Option.some.inj (fill.symm.trans hr)
  let p := SlotSchedule.scatterParameters w base A B deg
  have h0 : (p 0).val = base+A+(B+A) := Nat.mod_eq_of_lt (by omega)
  have h1 : (p 1).val = base+A+(B+A)+(B+A)*deg := Nat.mod_eq_of_lt (by omega)
  have hmul := Nat.mul_le_mul_right deg (Nat.le_add_right B A)
  have reg : SlotScatter.Regions p (B*deg) A :=
    ⟨by rw [h0]; omega, by rw [h1]; omega, Or.inl (by rw [h0,h1]; omega)⟩
  rw [← h1,← h0]
  apply invertFields D hc reg _ scatter
  intro e
  rw [h0]
  simpa only [Equiv.symm_apply_apply] using SlotSchedule.rectangular_rows D base deg hc (by omega) hdw _ rows
    (SlotSchedule.sortedFields D deg hc e)

/-- A selected state's forward mate column is a permutation in its canonical
base-port ordering. Its inverse pass reads and writes only those two columns. -/
theorem baseInverse {a l : ℕ} (Y : Compression.State a l) {shift : ℕ} {m : Memory w}
    {p : Fin 2 → Word w} (regions : SlotScatter.Regions p (Fintype.card Y.Base*2^a) (Fintype.card Y.Base*2^a))
    (forward : ShrinkSlots.BaseForward Y (p 0).val shift m) {rs : List (Report w)}
    (run : runSegment ((template SlotScatter.visit 0).instantiate w p).program 10
      (some 0) m (List.replicate (Fintype.card Y.Base*2^a) []) = some rs) :
    Reads (InColumn (p 0).val (Fintype.card Y.Base*2^a)) (eventLog rs) ∧
      Writes (InColumn (p 1).val (Fintype.card Y.Base*2^a)) (eventLog rs) := by
  let order := IncidenceDirectory.baseOrder Y
  let mate := order.symm.trans (Y.slots.base.target.trans order)
  apply scatter_run regions mate.toEmbedding _ run
  intro i
  have he := forward.mate (order.symm i)
  change m ((p 0).val+(order (order.symm i)).val) = _ at he
  rwa [order.apply_symm_apply] at he

open SlotLevel

/-- Read and write bounds for the append and invert phases of an actual shrinking
level. The genuine and dummy reports determine the physical input to append,
including all still-zero counters. The append reports then determine the actual
source rows read by the inversion. -/
theorem selected (s : Shape) (h : Heads) (D : SlotSchedule.Directory E (fields s) (owners s))
    {mem : Memory w} (input : SlotSchedule.OwnerInput D (bank s h w .genuineOwners)
      (bank s h w .dummyOwners) mem h.scratch (genuineCount s) (dummyCount s))
    (hdeg : 0 < s.newDegree) (hdw : s.newDegree < 2^w)
    (hc : ∀ b, Fintype.card {e // D.owner e = b} = s.newDegree)
    (fit : stopAddress s h < 2^w)
    (zero : ∀ u : Word w, u.val < owners s+fields s → mem (h.scratch+fields s+u.val) = 0)
    {r : Reports w} (native : r.Native s h mem) :
    (Reads (fun x => h.scratch ≤ x ∧ x < rowsHead s h) (eventLog r.append) ∧
      Writes (fun x => h.scratch+fields s ≤ x ∧ x < inverseHead s h) (eventLog r.append)) ∧
    (Reads (fun x => rowsHead s h ≤ x ∧ x < rowsHead s h+owners s*s.newDegree) (eventLog r.scatter) ∧
      Writes (fun x => inverseHead s h ≤ x ∧ x < targetsHead s h) (eventLog r.scatter)) := by
  obtain ⟨gr,dr,fill,scatter,_⟩ := native
  have fit' : h.scratch+fields s+(owners s+fields s)+(owners s+fields s)*s.newDegree+fields s < 2^w := by
    change targetsHead s h < 2^w
    unfold stopAddress shiftsHead at fit; omega
  obtain ⟨gs,ds,hg,hd,stored,frame,_⟩ := SlotSchedule.owner_table_run D _ _ mem input (by omega)
  obtain rfl := Option.some.inj (gr.symm.trans hg.executed)
  obtain rfl := Option.some.inj (dr.symm.trans hd.executed)
  have counts (u : Word w) (hu : u.val < owners s+fields s) :
      after (after mem (eventLog r.genuine)) (eventLog r.dummy) (h.scratch+fields s+u.val) = 0 :=
    (frame _ (Or.inr (Nat.le_add_right _ _))).trans (zero u hu)
  have append := appendFields (A := fields s) (B := owners s) (base := h.scratch) (deg := s.newDegree)
    (by omega) hdw fill
  have inverse := invertFields_after_append D hdeg hdw hc fit' stored counts fill scatter
  simpa only [Reads,Writes,InColumn,rowsHead,inverseHead,targetsHead,Nat.add_assoc] using And.intro append inverse

end CompressorRecords.SlotFillFootprint

end VPVNP
end Computability
end OAI

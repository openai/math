import OAI.Computability.VPVNP.LiveHeaderAllocated
import OAI.Computability.VPVNP.LiveHeaderCutInput
import OAI.Computability.VPVNP.LiveHeaderBoundedRun
import OAI.Computability.VPVNP.LiveStageSegments

/-!
# Fixed-capacity native live-cut scans

Each stage performs exactly its public number of calls. The runtime count
occupies a prefix, followed by idle calls that only read the count. Every
successful report preserves the reserved tag under arbitrary replay. A final
bounded call accepts and transfers control to the next stage.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader.Allocated

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM ChainAssignments CutSchedule
open scoped Fin.CommRing

variable {w d a h Δ : ℕ}

/-- Instantiate the allocated-field worker on the selected slot, copy or padding mode, and
public operands. -/
abbrev program (p : Parameters) (slot : Fin 4) (pad : Bool) (pub : Fin 16 → Word w) :=
  ((table p slot pad).instantiate w pub).program

/-- An address precedes the field array or lies at or beyond its exclusive end. -/
def Outside (base len addr : ℕ) : Prop := addr < base ∨ base+len ≤ addr

/-- Runtime offset and count were written by the descriptor stage. -/
structure Loaded (p : Parameters) (pub : Fin 16 → Word w) (iv : ℕ × ℕ) (m : Memory w) : Prop where
  offset : (m (pub p.srcOffsetAddress).val).val = iv.1
  count : (m (pub p.countAddress).val).val = iv.2

/-- Public scan capacity and bounds needed to read the occupied source sites. -/
structure Sizes (p : Parameters) (pub : Fin 16 → Word w) (iv : ℕ × ℕ) (cap : ℕ) : Prop where
  zero : pub p.firstCursor = 0
  occupied : iv.2 ≤ cap
  capFit : cap < 2^w
  sourceFit : iv.1+iv.2 ≤ 2^w

/-- The occupied destination is disjoint from its sources, count and offset. -/
structure CopyLayout (p : Parameters) (pub : Fin 16 → Word w) (iv : ℕ × ℕ) : Prop where
  sourceBefore : iv.1+iv.2 ≤ (pub p.destinationBase).val
  destinationFit : (pub p.destinationBase).val+iv.2 ≤ 2^w
  offsetOutside : Outside (pub p.destinationBase).val iv.2 (pub p.srcOffsetAddress).val
  countOutside : Outside (pub p.destinationBase).val iv.2 (pub p.countAddress).val

private theorem index_val {p pub iv cap} (size : Sizes (w := w) p pub iv cap) {j : ℕ} (hj : j < cap) :
    (j : Word w).val = j := Fin.val_cast_of_lt (hj.trans size.capFit)

private theorem active_iff {p pub iv cap} (size : Sizes (w := w) p pub iv cap)
    {j : ℕ} (hj : j < cap) {m : Memory w} (count : (m (pub p.countAddress).val).val = iv.2) :
    Active p pub (j : Word w) m ↔ j < iv.2 := by
  unfold Active position
  rw [size.zero, sub_zero]
  change (j : Word w).val < _ ↔ _
  rw [index_val size hj,count]

private theorem address_add (base : Word w) {j : ℕ} (fit : base.val+j < 2^w) :
    (base+(j : Word w)).val = base.val+j := by
  rw [Fin.val_add, Fin.val_cast_of_lt (show j < 2^w by omega), Nat.mod_eq_of_lt fit]

private theorem destination_val {p pub iv cap} (size : Sizes (w := w) p pub iv cap)
    (layout : CopyLayout p pub iv) {j : ℕ} (hj : j < iv.2) :
    (destination p pub (j : Word w)).val = (pub p.destinationBase).val+j := by
  rw [destination,position,size.zero,sub_zero,address_add _ (by have := layout.destinationFit; omega)]

private theorem read_bit {p pub iv cap} (size : Sizes (w := w) p pub iv cap) {m : Memory w}
    (offset : (m (pub p.srcOffsetAddress).val).val = iv.1) (slot : Fin 4) {j : ℕ} (hj : j < iv.2) :
    bitAt p slot pub (j : Word w) m = (m (iv.1+j)).val.testBit slot.val := by
  unfold bitAt position
  rw [size.zero,sub_zero,address_add _ (by rw [offset]; have := size.sourceFit; omega),offset]

private theorem run_good {C : Type*} (P : Program w C) (fuel cap : ℕ) (m : Memory w)
    (inv : ℕ → Memory w → Prop) (good : Report w → Prop) (init : inv 0 m)
    (step : ∀ j < cap, ∀ mem, inv j mem → ∃ es,
      execute P fuel (P.start (j : Word w)) mem [] = some ⟨es,some ((j+1 : ℕ) : Word w)⟩ ∧
      inv (j+1) (after mem es) ∧ good ⟨es,some ((j+1 : ℕ) : Word w)⟩) :
    ∃ rs, runSegment P fuel (some 0) m (List.replicate cap []) = some rs ∧
      endState (some 0) rs = some (cap : Word w) ∧ inv cap (after m (eventLog rs)) ∧
      rs.length = cap ∧ ∀ r ∈ rs, good r := by
  have go (n : ℕ) (hn : n ≤ cap) : ∃ rs, runSegment P fuel (some 0) m (List.replicate n []) = some rs ∧
      endState (some 0) rs = some (n : Word w) ∧ inv n (after m (eventLog rs)) ∧
      rs.length = n ∧ ∀ r ∈ rs, good r := by
    induction n with
    | zero => exact ⟨[],rfl,rfl,init,rfl,by simp⟩
    | succ n ih =>
      obtain ⟨rs,hr,he,hi,hlen,hg⟩ := ih (by omega)
      obtain ⟨es,hs,hnext,hrep⟩ := step n (by omega) _ hi
      let r : Report w := ⟨es,some ((n+1 : ℕ) : Word w)⟩
      refine ⟨rs++[r], ?_, ?_, ?_, by simp [hlen], ?_⟩
      · rw [List.replicate_succ',PrimedSchedule.runSegment_append,hr]
        simp only [Option.bind_some,he,runSegment,hs,Option.map_some,r]
      · rw [endState_append]; rfl
      · simpa only [eventLog,List.flatMap_append,List.flatMap_singleton,after,List.foldl_append] using hnext
      · intro x hx
        rcases List.mem_append.mp hx with hold | hnew
        · exact hg x hold
        · exact (List.mem_singleton.mp hnew) ▸ hrep
  exact go cap le_rfl

private theorem write_next {slot : Fin 4} {src dst j : ℕ} {original m : Memory w}
    (inv : FieldCopy original slot src dst j m) (addr : Word w) (ha : addr.val = dst+j) :
    FieldCopy original slot src dst (j+1)
      (writeMemory m addr (encodeBit w ((original (src+j)).val.testBit slot.val))) := by
  constructor
  · intro k hk
    by_cases he : k = j
    · simp [writeMemory,ha,he]
    · simp [writeMemory,ha,he,inv.copied k (by omega)]
  · intro z hz
    have ne : z ≠ dst+j := by omega
    simp [writeMemory,ha,ne,inv.frame z (by omega)]

/-- All active and idle calls, before the bounded wrapper's accepting call.
The final copy has exactly the runtime length and every report, even under
arbitrary replay, preserves any designated address outside its destination. -/
theorem copy_sweep (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (original : Memory w) (iv : ℕ × ℕ) (cap : ℕ) (size : Sizes p pub iv cap) (load : Loaded p pub iv original)
    (layout : CopyLayout p pub iv) (tag : Word w) (outside : Outside (pub p.destinationBase).val iv.2 tag.val) :
    ∃ rs, runSegment (program p slot false pub) 22 (some 0) original (List.replicate cap []) = some rs ∧
      endState (some 0) rs = some (cap : Word w) ∧
      FieldCopy original slot iv.1 (pub p.destinationBase).val iv.2 (after original (eventLog rs)) ∧
      rs.length = cap ∧ (∀ r ∈ rs, countProbes r.events ≤ 4) ∧ LiveStageLink.PreservesTag tag rs := by
  let dst := (pub p.destinationBase).val
  let inv j := FieldCopy original slot iv.1 dst (min j iv.2)
  let good (r : Report w) := countProbes r.events ≤ 4 ∧ ∀ m, after m r.events tag.val = m tag.val
  have step (j : ℕ) (hj : j < cap) (mem : Memory w) (hi : inv j mem) :
      ∃ es, execute (program p slot false pub) 22 ((program p slot false pub).start (j : Word w)) mem [] =
          some ⟨es,some ((j+1 : ℕ) : Word w)⟩ ∧ inv (j+1) (after mem es) ∧ good ⟨es,some ((j+1 : ℕ) : Word w)⟩ := by
    have unchanged (z : ℕ) (ho : Outside dst iv.2 z) : mem z = original z := by
      apply hi.frame
      exact ho.imp_right ((Nat.add_le_add_left (Nat.min_le_right ..) dst).trans ·)
    have hc := (congrArg Fin.val (unchanged _ layout.countOutside)).trans load.count
    have hoff := (congrArg Fin.val (unchanged _ layout.offsetOutside)).trans load.offset
    by_cases ha : j < iv.2
    · have act := (active_iff size hj hc).mpr ha
      have hd := destination_val size layout ha
      have hsrc : mem (iv.1+j) = original (iv.1+j) :=
        unchanged _ (Or.inl (by have := layout.sourceBefore; dsimp [dst]; omega))
      have safe : tag ≠ destination p pub (j : Word w) := by
        intro same
        have he := (congrArg Fin.val same).trans hd
        rcases outside with lo | hi <;> omega
      obtain ⟨es,hr,hm,_,hp,_⟩ := native_of_returns (copy_exec hw p slot pub (j : Word w) _ mem act)
        (show 21 < 22 by decide)
      have frame := report_frame p slot false pub (j : Word w) mem [] 22 hr tag (fun _ => Or.inr safe)
      refine ⟨es,by simpa using hr,?_,hp.le,frame⟩
      rw [hm,read_bit size hoff slot ha,hsrc]
      dsimp [inv] at hi ⊢
      rw [Nat.min_eq_left ha.le] at hi
      rw [Nat.min_eq_left ha]
      exact write_next hi _ hd
    · have idle := mt (active_iff size hj hc).mp ha
      obtain ⟨es,hr,hm,_,hp,_⟩ := native_of_returns (idle_exec p slot false pub (j : Word w) _ mem idle)
        (show 8 < 22 by decide)
      have frame := report_frame p slot false pub (j : Word w) mem [] 22 hr tag (fun h => (idle h).elim)
      refine ⟨es,by simpa using hr,?_,by change countProbes es ≤ 4; omega,frame⟩
      dsimp [inv] at hi ⊢
      rw [hm,Nat.min_eq_right (by omega)]
      simpa [Nat.min_eq_right (Nat.le_of_not_gt ha)] using hi
  obtain ⟨rs,hr,he,hi,hl,hg⟩ := run_good _ 22 cap original inv good (FieldCopy.initial ..) step
  exact ⟨rs,hr,he,by simpa [inv,Nat.min_eq_right size.occupied] using hi,hl,
    fun r h => (hg r h).1,fun r h => (hg r h).2⟩

/-- The occupied padding positions are zero in the original processor words. -/
def ZeroPad (slot : Fin 4) (iv : ℕ × ℕ) (m : Memory w) :=
  ∀ j < iv.2, (m (iv.1+j)).val.testBit slot.val = false

theorem padding_sweep (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (original : Memory w) (iv : ℕ × ℕ) (cap : ℕ) (size : Sizes p pub iv cap) (load : Loaded p pub iv original)
    (tag : Word w) (zero : ZeroPad slot iv original) :
    ∃ rs, runSegment (program p slot true pub) 22 (some 0) original (List.replicate cap []) = some rs ∧
      endState (some 0) rs = some (cap : Word w) ∧ after original (eventLog rs) = original ∧
      rs.length = cap ∧ (∀ r ∈ rs, countProbes r.events ≤ 3) ∧ LiveStageLink.PreservesTag tag rs := by
  let good (r : Report w) := countProbes r.events ≤ 3 ∧ ∀ m, after m r.events tag.val = m tag.val
  have step (j : ℕ) (hj : j < cap) (mem : Memory w) (hi : mem = original) :
      ∃ es, execute (program p slot true pub) 22 ((program p slot true pub).start (j : Word w)) mem [] =
          some ⟨es,some ((j+1 : ℕ) : Word w)⟩ ∧ after mem es = original ∧ good ⟨es,some ((j+1 : ℕ) : Word w)⟩ := by
    subst mem
    have use {steps probes : ℕ} (ret : Returns p slot true pub (j : Word w) (fun _ => 0) original original steps probes)
        (fuel : steps < 22) (bound : probes ≤ 3) : ∃ es,
        execute (program p slot true pub) 22 ((program p slot true pub).start (j : Word w)) original [] =
        some ⟨es,some ((j+1 : ℕ) : Word w)⟩ ∧ after original es = original ∧ good ⟨es,some ((j+1 : ℕ) : Word w)⟩ := by
      obtain ⟨es,hr,hm,_,hp,_⟩ := native_of_returns ret fuel
      have frame := report_frame p slot true pub (j : Word w) original [] 22 hr tag (fun _ => Or.inl rfl)
      exact ⟨es,by simpa using hr,hm,hp.le.trans bound,frame⟩
    by_cases active : j < iv.2
    · exact use (padding_exec hw p slot pub (j : Word w) _ original ((active_iff size hj load.count).mpr active)
        ((read_bit size load.offset slot active).trans (zero j active))) (by decide) le_rfl
    · exact use (idle_exec p slot true pub (j : Word w) _ original (mt (active_iff size hj load.count).mp active))
        (by decide) (by decide)
  obtain ⟨rs,hr,he,hm,hl,hg⟩ := run_good _ 22 cap original (fun _ mem => mem = original) good rfl step
  exact ⟨rs,hr,he,hm,hl,fun r h => (hg r h).1, fun r h => (hg r h).2⟩

private theorem pad_report {p pub iv cap} (hw : 4 ≤ w) (slot : Fin 4) (size : Sizes p pub iv cap)
    {m : Memory w} (load : Loaded p pub iv m) {j : ℕ} (hj : j < cap) (fuel : ℕ)
    (bits : List Bool) {r : Report w}
    (hr : execute (program p slot true pub) fuel ((program p slot true pub).start (j : Word w)) m bits = some r) :
    r.result = some ((j+1 : ℕ) : Word w) ∧ after m r.events = m ∧
      (j < iv.2 → (m (iv.1+j)).val.testBit slot.val = false) := by
  by_cases active : j < iv.2
  · have ha := (active_iff size hj load.count).mpr active
    have he := read_bit size load.offset slot active
    cases hb : (m (iv.1+j)).val.testBit slot.val with
    | false =>
      have hrep := native_report_of_returns (padding_exec hw p slot pub (j : Word w) _ m ha (he.trans hb)) hr
      exact ⟨by simpa using hrep.2.1,hrep.2.2.1,fun _ => rfl⟩
    | true =>
      have fail := padding_native_rejects hw p slot pub (j : Word w) m ha (he.trans hb) fuel bits
      have eq : none = some r := fail.symm.trans hr
      contradiction
  · have idle := mt (active_iff size hj load.count).mp active
    have hrep := native_report_of_returns (idle_exec p slot true pub (j : Word w) _ m idle) hr
    exact ⟨by simpa using hrep.2.1,hrep.2.2.1,fun h => (active h).elim⟩

private theorem pad_prefix_sound {C : Type*} (P : Program w C) (fuel cap : ℕ) (slot : Fin 4)
    (iv : ℕ × ℕ) (m : Memory w)
    (one : ∀ j < cap, ∀ bits r, execute P fuel (P.start (j : Word w)) m bits = some r →
      r.result = some ((j+1 : ℕ) : Word w) ∧ after m r.events = m ∧
        (j < iv.2 → (m (iv.1+j)).val.testBit slot.val = false))
    (bs : List (List Bool)) (start : ℕ) {rs : List (Report w)} (fit : start+bs.length ≤ cap)
    (hr : runSegment P fuel (some (start : Word w)) m bs = some rs) :
    ∀ j, start ≤ j → j < start+bs.length → j < iv.2 → (m (iv.1+j)).val.testBit slot.val = false := by
  induction bs generalizing start rs with
  | nil => intro j lo hi _; simp at hi; omega
  | cons b bs ih =>
    simp only [List.length_cons] at fit ⊢
    simp only [runSegment] at hr
    cases hx : execute P fuel (P.start (start : Word w)) m b with
    | none => simp [hx] at hr
    | some r =>
      simp only [hx, Option.map_eq_some_iff] at hr
      obtain ⟨rest,hr,_⟩ := hr
      obtain ⟨hnext,hm,hbit⟩ := one start (by omega) b r hx
      rw [hnext,hm] at hr
      intro j lo hi present
      rcases eq_or_lt_of_le lo with rfl | hlt
      · exact hbit present
      · exact ih (start+1) (by omega) hr j (by omega) (by omega) present

/-- Any successful sequence of padding calls covering the whole public
allocation forces each occupied original site to be zero. -/
theorem padding_sweep_sound (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (m : Memory w) (iv : ℕ × ℕ) (cap : ℕ) (size : Sizes p pub iv cap) (load : Loaded p pub iv m)
    (fuel : ℕ) (bs : List (List Bool)) (length : bs.length = cap) {rs : List (Report w)}
    (hr : runSegment (program p slot true pub) fuel (some 0) m bs = some rs) : ZeroPad slot iv m := by
  have sound := pad_prefix_sound (program p slot true pub) fuel cap slot iv m
    (fun _ hj b _ he => pad_report hw slot size load hj fuel b he) bs 0 (by simp [length]) hr
  intro j hj
  exact sound j (Nat.zero_le _) (by simpa [length] using hj.trans_le size.occupied) hj

/-- The instantiated allocated-field worker wrapped in a public capacity check. -/
abbrev boundedProgram (p : Parameters) (slot : Fin 4) (pad : Bool) (pub : Fin 16 → Word w) (cap : ℕ) :=
  (LiveHeaderBounded.machine (table p slot pad) pub (cap : Word w)).program

private theorem close_sweep (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pad : Bool)
    (pub : Fin 16 → Word w) (cap : ℕ) (hcap : cap < 2^w) (m : Memory w) (tag : Word w)
    (probes : ℕ) {rs : List (Report w)}
    (hr : runSegment (program p slot pad pub) 22 (some 0) m (List.replicate cap []) = some rs)
    (hl : rs.length = cap) (hp : ∀ r ∈ rs, countProbes r.events ≤ probes)
    (hf : LiveStageLink.PreservesTag tag rs) :
    let out := rs.map LiveHeaderBounded.activeReport ++ [LiveHeaderBounded.closedReport w]
    runSegment (boundedProgram p slot pad pub cap) 25 (some 0) m (List.replicate (cap+1) []) = some out ∧
      endState (some 0) out = none ∧ after m (eventLog out) = after m (eventLog rs) ∧
      out.length = cap+1 ∧ (∀ r ∈ out, countProbes r.events ≤ probes) ∧ LiveStageLink.PreservesTag tag out := by
  dsimp only
  have run := LiveHeaderBounded.runSegment_cursor_complete (table p slot pad) pub (cap : Word w)
    (by decide : 0 < 22) 0 m (List.replicate cap []) rs (by simp [Fin.val_cast_of_lt hcap]) hr (by
      intro j _ mem bits r h
      simpa using (report_successor hw p slot pad pub (j : Word w) mem bits 22 h).2)
  refine ⟨by simpa only [List.replicate_succ',Nat.cast_zero] using run,?_,?_,by simp [hl],?_,?_⟩
  · rw [endState_append]; rfl
  · rw [eventLog,List.flatMap_append,List.flatMap_singleton,after,List.foldl_append]
    exact LiveHeaderBounded.after_activeReports m rs
  · intro r h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
      exact hp r hr
    · obtain rfl := List.mem_singleton.mp h
      exact Nat.zero_le _
  · intro r h mem
    rcases List.mem_append.mp h with h | h
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
      exact hf r hr mem
    · obtain rfl := List.mem_singleton.mp h
      rfl

/-- The source stage in the native linker. Its accepting path includes one
closing call after the public capacity, and has the exact occupied copy. -/
theorem copy_bounded (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (m : Memory w) (iv : ℕ × ℕ) (cap : ℕ) (size : Sizes p pub iv cap) (load : Loaded p pub iv m)
    (layout : CopyLayout p pub iv) (tag : Word w) (outside : Outside (pub p.destinationBase).val iv.2 tag.val) :
    ∃ rs, runSegment (boundedProgram p slot false pub cap) 25 (some 0) m (List.replicate (cap+1) []) = some rs ∧
      endState (some 0) rs = none ∧ FieldCopy m slot iv.1 (pub p.destinationBase).val iv.2 (after m (eventLog rs)) ∧
      rs.length = cap+1 ∧ (∀ r ∈ rs, countProbes r.events ≤ 4) ∧ LiveStageLink.PreservesTag tag rs := by
  obtain ⟨rs,hr,_,hc,hl,hp,hf⟩ := copy_sweep hw p slot pub m iv cap size load layout tag outside
  obtain ⟨run,last,mem,len,probes,frame⟩ := close_sweep hw p slot false pub cap size.capFit m tag 4 hr hl hp hf
  exact ⟨_,run,last,mem.symm ▸ hc,len,probes,frame⟩

/-- The complete bounded padding stage succeeds on a zero padding field.
Neither its active nor its idle calls write any memory. -/
theorem padding_bounded (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (m : Memory w) (iv : ℕ × ℕ) (cap : ℕ) (size : Sizes p pub iv cap) (load : Loaded p pub iv m)
    (tag : Word w) (zero : ZeroPad slot iv m) :
    ∃ rs, runSegment (boundedProgram p slot true pub cap) 25 (some 0) m (List.replicate (cap+1) []) = some rs ∧
      endState (some 0) rs = none ∧ after m (eventLog rs) = m ∧
      rs.length = cap+1 ∧ (∀ r ∈ rs, countProbes r.events ≤ 3) ∧ LiveStageLink.PreservesTag tag rs := by
  obtain ⟨rs,hr,_,hm,hl,hp,hf⟩ := padding_sweep hw p slot pub m iv cap size load tag zero
  obtain ⟨run,last,mem,len,probes,frame⟩ := close_sweep hw p slot true pub cap size.capFit m tag 3 hr hl hp hf
  exact ⟨_,run,last,mem.trans hm,len,probes,frame⟩

/-- On arbitrary choice strings and for every allocated fuel, an accepting
bounded scan has checked every occupied original padding bit. Early stopping
leaves a live cursor and cannot skip a failing padding position. -/
theorem padding_bounded_sound (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (m : Memory w) (iv : ℕ × ℕ) (cap : ℕ) (size : Sizes p pub iv cap) (load : Loaded p pub iv m)
    (f : ℕ) (bs : List (List Bool)) {rs : List (Report w)}
    (hr : runSegment (boundedProgram p slot true pub cap) (f+3) (some 0) m bs = some rs)
    (last : endState (some 0) rs = none) : ZeroPad slot iv m := by
  let P := boundedProgram p slot true pub cap
  have go (bs : List (List Bool)) (start : ℕ) (rs : List (Report w))
      (run : runSegment P (f+3) (some (start : Word w)) m bs = some rs)
      (last : endState (some (start : Word w)) rs = none) :
      ∀ j, start ≤ j → j < iv.2 → (m (iv.1+j)).val.testBit slot.val = false := by
    induction bs generalizing start rs with
    | nil =>
      simp only [runSegment,Option.some.injEq] at run
      subst rs
      contradiction
    | cons b bs ih =>
      intro j lo hj
      have here : start < cap := lo.trans_lt (hj.trans_le size.occupied)
      have active : (start : Word w) < (cap : Word w) := by
        change (start : Word w).val < (cap : Word w).val
        rwa [index_val size here,Fin.val_cast_of_lt size.capFit]
      have heq := LiveHeaderBounded.execute_active (table p slot true) pub (cap : Word w) f
        (start : Word w) active m b
      simp only [runSegment] at run
      cases he : execute P (f+3) (P.start (start : Word w)) m b with
      | none => simp [he] at run
      | some r =>
        simp only [he,Option.map_eq_some_iff] at run
        obtain ⟨rest,tail,rfl⟩ := run
        have hx : (execute (program p slot true pub) f ((program p slot true pub).start (start : Word w)) m b).map
            LiveHeaderBounded.activeReport = some r := heq.symm.trans he
        obtain ⟨source,hs,rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨next,mem,checked⟩ := pad_report hw slot size load here f b hs
        change runSegment P (f+3) source.result (after m source.events) bs = some rest at tail
        change endState source.result rest = none at last
        rw [next,mem] at tail
        rw [next] at last
        rcases eq_or_lt_of_le lo with rfl | later
        · exact checked hj
        · exact ih (start+1) rest tail last j (by omega) hj
  exact fun j hj => go bs 0 rs hr last j (Nat.zero_le _) hj

/-- Runtime descriptors and the preserved headers identify the actual
incident cut in the completed fixed-capacity copy, with a full scratch
frame and the per-report linker frame. -/
theorem physical_copy_bounded {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ} {g : Fin (2^(h+1))}
    {m : Memory w} (headers : SiteHeaders d hw advice cuts g m) (side : LiveHeaderDescriptors.Side)
    (p : Parameters) (pub : Fin 16 → Word w) (iv : ℕ × ℕ) (cap : ℕ) (size : Sizes p pub iv cap)
    (load : Loaded p pub iv m) (layout : CopyLayout p pub iv) (tag : Word w)
    (outside : Outside (pub p.destinationBase).val iv.2 tag.val)
    (sites : iv.1+iv.2 ≤ 2^d) (scratch : 2^d ≤ (pub p.destinationBase).val) :
    ∃ rs, runSegment (boundedProgram p (cutSlot side) false pub cap) 25 (some 0) m (List.replicate (cap+1) []) = some rs ∧
      endState (some 0) rs = none ∧ rs.length = cap+1 ∧
      (∀ r ∈ rs, countProbes r.events ≤ 4) ∧ LiveStageLink.PreservesTag tag rs ∧
      FieldCopy m (cutSlot side) iv.1 (pub p.destinationBase).val iv.2 (after m (eventLog rs)) ∧
      CopiedSlice (cuts (incidentCut side g)) iv (pub p.destinationBase).val (after m (eventLog rs)) ∧
      SiteHeaders d hw advice cuts g (after m (eventLog rs)) := by
  obtain ⟨rs,run,last,copy,len,hp,frame⟩ := copy_bounded hw p (cutSlot side) pub m iv cap size load layout tag outside
  exact ⟨rs,run,last,len,hp,frame,copy,copy.physical headers side iv _ sites scratch⟩

/-- Among all possible paths through the bounded table, an accepting
path exists exactly for canonical zero padding in the actual cut field. -/
theorem physical_padding_bounded_iff {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ} {g : Fin (2^(h+1))}
    {m : Memory w} (headers : SiteHeaders d hw advice cuts g m) (side : LiveHeaderDescriptors.Side)
    (p : Parameters) (pub : Fin 16 → Word w) (iv : ℕ × ℕ) (cap : ℕ) (size : Sizes p pub iv cap)
    (load : Loaded p pub iv m) (tag : Word w) (sites : iv.1+iv.2 ≤ 2^d)
    (inside : iv.1+iv.2 ≤ width (h+1) Δ (incidentCut side g).val) :
    (∃ bs rs, runSegment (boundedProgram p (cutSlot side) true pub cap) 25 (some 0) m bs = some rs ∧
      endState (some 0) rs = none) ↔ LiveHeaderDescriptors.Physical.ZeroSlice (cuts (incidentCut side g)) iv := by
  rw [← headers.zeroSlice side iv sites inside]
  constructor
  · rintro ⟨bs,rs,hr,last⟩
    exact padding_bounded_sound hw p (cutSlot side) pub m iv cap size load 22 bs hr last
  · intro hz
    obtain ⟨rs,run,last,_⟩ := padding_bounded hw p (cutSlot side) pub m iv cap size load tag hz
    exact ⟨_,rs,run,last⟩

end LiveHeader.Allocated

end VPVNP
end Computability
end OAI

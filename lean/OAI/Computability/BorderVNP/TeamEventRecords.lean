import OAI.Computability.BorderVNP.TeamBurstProbeGeometry
import OAI.Computability.BorderVNP.TeamMemoryCallback
import OAI.Computability.BorderVNP.TeamRAM
import Mathlib.Data.List.Forall2

/-! # From physical callback rows to the chronological team transcript

The register interpreter chooses a list of old words for each event. Zipping this list
with its prescribed memory accesses reconstructs the four logical fields tested by the
global sorter. The same reconstruction applies across all instruction and block boundaries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamEventRecords

open VPVNP RAMSerialization TeamRAM
open BurstRAM (Word Memory)
variable {w : ℕ}

/-- Reconstruct the four fields at an instruction from its chosen previous words. -/
def eventFields (t : ℕ) (e : Event w) : List (TeamRecords.Record (Word w)) :=
  List.zipWith TeamRecords.Access.record (e.action.accesses t) e.old

/-- Chronological concatenation of the fields produced at each charged instruction. -/
def historyFields : ℕ → List (Event w) → List (TeamRecords.Record (Word w))
  | _, [] => []
  | t, e :: es => eventFields t e ++ historyFields (t+(1+e.action.extra)) es

private theorem zip_old {α : Type*} (as : List (TeamRecords.Access α)) (vs : List α)
    (h : as.length = vs.length) :
    (as.zipWith TeamRecords.Access.record vs).map TeamRecords.Record.before = vs ∧
      TeamRecords.Matches as (as.zipWith TeamRecords.Access.record vs) := by
  induction as generalizing vs with
  | nil => have he := List.length_eq_zero_iff.mp h.symm; subst vs; exact ⟨rfl,.nil⟩
  | cons a as ih =>
    cases vs with
    | nil => simp at h
    | cons v vs =>
      obtain ⟨ho,hm⟩ := ih vs (Nat.succ.inj h)
      exact ⟨congrArg (v :: ·) ho,.cons rfl hm⟩

/-- The number of probes specified by an action is independent of its starting clock. -/
theorem access_length (act : TeamTranscript.Action (Word w)) (t : ℕ) :
    (act.accesses t).length = match act with
      | .ordinary none => 0
      | .ordinary (some _) => 1
      | .burst _ q => q := by
  cases act with
  | ordinary v => cases v <;> rfl
  | burst a q =>
    change (TeamRecords.readBurst (Word := Word w) a t q).length = q
    induction q generalizing a t with
    | zero => rfl
    | succ q ih => exact congrArg (·+1) (ih (t+1) (a+1))

/-- Each locally executed instruction supplies exactly one previous word per access. -/
theorem arity_of_advance {S : Type*} (i : Instr w S) (e : Event w) (next : S)
    (act : i.action = some e.action) (go : i.advance e.choices e.old = some (next,e.sign))
    (t : ℕ) : (e.action.accesses t).length = e.old.length := by
  rcases e with ⟨ac,vs,bs,sg⟩
  cases i with
  | accept | reject => contradiction
  | call a q run nxt =>
    change (if a.val+q ≤ 2^w then some (.burst a.val q) else none) = some ac at act
    split at act <;> try contradiction
    cases act
    change (if vs.length = q then (run vs bs).map _ else none) = some _ at go
    split at go <;> try contradiction
    rw [access_length]; exact ‹vs.length=q›.symm
  | localStep nxt sign | choose nxt | load a nxt | store a v nxt =>
    cases act
    cases vs with
    | nil => cases bs <;> first | rfl | contradiction
    | cons v vs =>
      cases bs with
      | nil => cases vs <;> first | rfl | contradiction
      | cons b bs => cases bs <;> cases vs <;> first | rfl | contradiction

/-- Local register replay has the exact per-event word counts, including signed calls. -/
theorem arity_of_local {S : Type*} {P : S → Instr w S} {s : S} {es : List (Event w)}
    (h : Local P s es) : ∀ e ∈ es, ∀ t, (e.action.accesses t).length = e.old.length := by
  induction es generalizing s with
  | nil => simp
  | cons e es ih =>
    obtain ⟨act,next,go,rest⟩ := h
    intro f hf t
    rcases List.mem_cons.mp hf with rfl | hf
    · exact arity_of_advance _ _ _ act go t
    · exact ih rest _ hf t

/-- A physically reconstructed history satisfies both local field matching and the exact
segmentation and old-word readout required by the native RAM path predicate. -/
theorem history_spec (t : ℕ) (es : List (Event w))
    (arity : ∀ e ∈ es, ∀ i, (e.action.accesses i).length = e.old.length) :
    TeamRecords.Matches (TeamTranscript.probes Event.action t es) (historyFields t es) ∧
      Claims t es (historyFields t es) := by
  induction es generalizing t with
  | nil => exact ⟨.nil,rfl⟩
  | cons e es ih =>
    have hs := arity e (.head _) t
    obtain ⟨fields,matchHead⟩ := zip_old (e.action.accesses t) e.old hs
    obtain ⟨matchTail,claimsTail⟩ := ih (t+(1+e.action.extra))
      (fun x hx => arity x (List.mem_cons_of_mem _ hx))
    have hlen : (eventFields t e).length = (e.action.accesses t).length := matchHead.length_eq.symm
    refine ⟨List.rel_append matchHead matchTail, ?_⟩
    simpa only [Claims,historyFields,←hlen,List.take_left,List.drop_left] using And.intro (show (eventFields t e).map TeamRecords.Record.before = e.old from fields) claimsTail

private theorem zip_eq_of_matches {α : Type*} {as : List (TeamRecords.Access α)} {rs : List (TeamRecords.Record α)}
    (h : TeamRecords.Matches as rs) :
    as.zipWith TeamRecords.Access.record (rs.map TeamRecords.Record.before) = rs := by
  induction h with
  | nil => rfl
  | cons h _ ih => exact congrArg₂ List.cons h.symm ih

/-- The matched, segmented chronological fields are uniquely reconstructed from the
actual instruction events, with no freedom in any sorting payload. -/
theorem history_eq_of_claims (t : ℕ) (es : List (Event w)) (rs : List (TeamRecords.Record (Word w)))
    (matchRows : TeamRecords.Matches (TeamTranscript.probes Event.action t es) rs)
    (claims : Claims t es rs) : historyFields t es = rs := by
  induction es generalizing t rs with
  | nil => exact claims.symm
  | cons e es ih =>
    let n := (e.action.accesses t).length
    obtain ⟨fields,rest⟩ := claims
    have h := List.forall₂_take n matchRows
    have h' := List.forall₂_drop n matchRows
    simp only [TeamTranscript.probes,n,List.take_left] at h
    simp only [TeamTranscript.probes,n,List.drop_left] at h'
    have one : eventFields t e = rs.take n := by
      unfold eventFields
      rw [← fields]
      exact zip_eq_of_matches h
    rw [historyFields,one,ih _ _ h' rest,List.take_append_drop]

/-- Exact chronological memory correctness of the reconstructed event fields. -/
theorem history_eq_transcript_iff {S : Type*} {P : S → Instr w S} {s : S} {es : List (Event w)}
    (localRun : Local P s es) (m : Memory w) (t : ℕ) :
    historyFields t es = TeamRecords.transcript m (TeamTranscript.probes Event.action t es) ↔ Correct m es := by
  have hc := (history_spec t es (arity_of_local localRun)).2
  rw [← claims_transcript_iff m t es]
  exact ⟨fun h => h ▸ hc, history_eq_of_claims t es _ (TeamRecords.matches_transcript ..)⟩

/-- Consecutive blocks reassemble at their charged global times, even if either block is
empty. The result is independent of where the legal handoffs were placed. -/
theorem history_append (t : ℕ) (xs ys : List (Event w)) :
    historyFields t (xs++ys) = historyFields t xs ++
      historyFields (t + RAMBuckets.cost (fun e => e.action.extra) xs) ys := by
  induction xs generalizing t with
  | nil => simp [historyFields,RAMBuckets.cost]
  | cons e es ih =>
    simp only [List.cons_append,historyFields,ih,RAMBuckets.cost,List.append_assoc]
    simp only [Nat.add_assoc]

/-- The logical burst fields are exactly the ones encoded by the physical iterator. -/
theorem burst_fields (a t : ℕ) (vs : List (Word w)) (bs : List Bool) (sg : Sign) :
    eventFields t ⟨.burst a vs.length,vs,bs,sg⟩ = TeamBurstProbe.claimed a t vs := by
  induction vs generalizing a t with
  | nil => rfl
  | cons v vs ih => exact congrArg (⟨a,t,v,v⟩ :: ·) (ih (a+1) (t+1))

/-- Both real sorting slots produced by the physical ordinary load/store implement its
logical event, including the checked previous word on an overwrite. -/
theorem ordinary_decode {r : ℕ} (op : TeamMemoryCallback.Op r) (reg : Fin r → Word w)
    (t old : Word w) (bs : List Bool) (sg : Sign) :
    let act : TeamTranscript.Action (Word w) := .ordinary (some ((reg op.addr).val,
      match op with | .load .. => none | .store _ src => some (reg src)))
    ((TeamMemoryCallback.pair op reg t old).map WordRecord.record) =
      ((eventFields t.val ⟨act,[old],bs,sg⟩).map TeamProbeEmit.widenRecord).flatMap TeamRecords.pair := by
  cases op <;> rfl

/-- The physical consecutive-read slots and the ordinary slots use precisely the same
reconstruction from event fields, with the common widened sorter representation. -/
theorem burst_decode (a t : Word w) (vs : List (Word w)) (bs : List Bool) (sg : Sign)
    (ha : a.val+vs.length ≤ 2^w) (ht : t.val+vs.length ≤ 2^w) :
    (TeamBurstProbe.records a t vs).map WordRecord.record =
      ((eventFields t.val ⟨.burst a.val vs.length,vs,bs,sg⟩).map TeamProbeEmit.widenRecord).flatMap TeamRecords.pair := by
  rw [burst_fields]
  exact TeamBurstProbe.records_decode _ _ _ ha ht

/-- The physical read/write fields seen after deserializing the sorter's paired slots. -/
def physicalFields (t : ℕ) (e : Event w) : List (RAMMemory.Record (Word (w+1))) :=
  ((eventFields t e).map TeamProbeEmit.widenRecord).flatMap TeamRecords.pair

private def pack (x : RAMMemory.Record (Word w)) : WordRecord w :=
  ⟨x.kind, Fin.ofNat (2^w) x.address, x.value, Fin.ofNat (2^w) x.startCost, Fin.ofNat (2^w) x.ordinal⟩

private theorem pack_record (r : WordRecord w) : pack r.record = r := by
  obtain ⟨k,a,v,t,i⟩ := r
  have bounded (x : Word w) : Fin.ofNat (2^w) x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  simp only [pack,WordRecord.record,bounded]

/-- Typed sorter slots reconstructed from the physical fields. On every admitted memory
callback these are exactly the emitted words. -/
def physicalSlots (t : ℕ) (e : Event w) : List (WordRecord (w+1)) :=
  (physicalFields t e).map pack

/-- All physical slots appended by a local block at its charged starting tick. -/
def historySlots : ℕ → List (Event w) → List (WordRecord (w+1))
  | _, [] => []
  | t, e :: es => physicalSlots t e ++ historySlots (t+(1+e.action.extra)) es

/-- A verified decode determines the complete typed buffer append, without extra framing
or bounds hypotheses. -/
theorem physicalSlots_of_decode (t : ℕ) (e : Event w) (slots : List (WordRecord (w+1)))
    (h : slots.map WordRecord.record = physicalFields t e) : physicalSlots t e = slots := by
  rw [physicalSlots,← h,List.map_map]
  simp only [Function.comp_def,pack_record]
  exact List.map_id slots

/-- The staged ordinary callback appends exactly these typed words. -/
theorem ordinary_slots {r : ℕ} (op : TeamMemoryCallback.Op r) (reg : Fin r → Word w)
    (t old : Word w) (bs : List Bool) (sg : Sign) :
    let act : TeamTranscript.Action (Word w) := .ordinary (some ((reg op.addr).val,
      match op with | .load .. => none | .store _ src => some (reg src)))
    TeamMemoryCallback.pair op reg t old = physicalSlots t.val ⟨act,[old],bs,sg⟩ :=
  (physicalSlots_of_decode _ _ _ (ordinary_decode ..)).symm

/-- The mounted private-input loop appends the corresponding typed consecutive rows. -/
theorem burst_slots (a t : Word w) (vs : List (Word w)) (bs : List Bool) (sg : Sign)
    (ha : a.val+vs.length ≤ 2^w) (ht : t.val+vs.length ≤ 2^w) :
    TeamBurstProbe.records a t vs = physicalSlots t.val ⟨.burst a.val vs.length,vs,bs,sg⟩ :=
  (physicalSlots_of_decode _ _ _ (burst_decode a t vs bs sg ha ht)).symm

end TeamEventRecords

end BorderVNP
end Computability
end OAI

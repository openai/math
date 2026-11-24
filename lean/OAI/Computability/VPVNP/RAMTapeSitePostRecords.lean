import OAI.Computability.VPVNP.RAMTapeSitePost

/-! # Applying the physical memory pass to the emitted reports and decoded edge records -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SitePost

open BurstRAM RAMLayout RAMSerialization RAMMemory RAMSort RAMBoundary Boundary

variable {d e w : ℕ}

private theorem record_zero (hw : 2 ≤ w) :
    (recordBytes ((recordFormat hw).words none)).all (!·) = true := by
  rw [SortReplay.recordBytes_words, recordFormat_empty]
  simp

/-- The initial block and both predecessor payloads occupy their physical
encoding. Under the checked successor relation, the complete finite
post-pass computes exactly the word-level validator's memory decision. -/
theorem complete_records (hw : 2 ≤ w) (hc : 2^d*2^e<2^w) (b : SendArrays d (2^e) w)
    (v : Word d) (header : ℕ → Word w) (initial : Word w) (edges : SiteSuccessors w)
    (he : edges.Spec hw hc initial v b) (rs : List (Report w)) (records : List (WordRecord w))
    (hrecs : records.map WordRecord.record = initRecord header v.val :: probeRecords edges.input.cost rs)
    (pr sr : Option (WordRecord w)) (hp : pr.map WordRecord.record = edges.received)
    (hs : sr.map WordRecord.record = edges.sent) (t : ℕ) (ht : budget d e w 0 ≤ t) :
    let raw := rawBank d w (4*2^e) (BurstRAM.wordBits v)
      (List.ofFn ((blockFormat (2^e) hw).encode (RecordBuffer.slots (2^e) records)))
      ((List.ofFn (RAMLayout.incidentBits b v)).drop (16*w)) []
      (List.ofFn ((recordFormat hw).encode pr)) (List.ofFn ((recordFormat hw).encode sr))
    (∀ c, complete.body.count c t raw =
      (checkSiteMemory (e := e) hw v (header v) (sortIncident b v) edges rs).1.toNat) ∧
      (∀ c, complete.body.AllStops c t raw) := by
  classical
  intro raw
  let prev := (recordFormat hw).words pr
  let sent := (recordFormat hw).words sr
  let x : SortReplay.State (2+e) w := (SortReplay.emittedBlock hw e records, [])
  let m := (unpackMessages (parseMessages hw hc b)).memory
  have hprev : (parsedSlot hw prev).record = RAMBoundary.receive m.lastRecords v := by
    simpa only [prev, parsedSlot, Format.parse_words] using hp.trans he.received_eq
  have hsent : (parsedSlot hw sent).record = RAMBoundary.outgoing m.lastRecords v := by
    simpa only [sent, parsedSlot, Format.parse_words] using hs.trans he.sent_eq
  have hpz (hv : v.val = 0) : (recordBytes prev).all (!·) = true := by
    have hn : RAMBoundary.receive m.lastRecords v = none := by
      rcases v with ⟨i,hi⟩
      change i = 0 at hv
      subst i; rfl
    have hp' : pr = none := Option.map_eq_none_iff.mp (hp.trans (he.received_eq.trans hn))
    simpa only [prev, hp'] using record_zero (w := w) hw
  have hsz (hv : 2^d ≤ v.val+1) : (recordBytes sent).all (!·) = true := by
    have hn : RAMBoundary.outgoing m.lastRecords v = none := by simp [RAMBoundary.outgoing, Nat.not_lt.mpr hv]
    have hs' : sr = none := Option.map_eq_none_iff.mp (hs.trans (he.sent_eq.trans hn))
    simpa only [sent, hs'] using record_zero (w := w) hw
  have spec := complete_spec hw hc b v x (SortReplay.emittedBlock_canonical hw e records) prev sent
    hprev (fun _ => hsent) hpz hsz t ht
  let tail := (List.ofFn (RAMLayout.incidentBits b v)).drop (16*w)
  have hraw : prestate v prev sent x tail = raw := by
    rw [prestate_eq_raw]
    simp only [raw, x, tail, prev, sent, SortReplay.emittedBlock_bytes, SortReplay.recordBytes_words]
    rw [record_width]
  change (∀ c, complete.body.count c t (prestate v prev sent x tail) = _) ∧
    (∀ c, complete.body.AllStops c t (prestate v prev sent x tail)) at spec
  rw [hraw] at spec
  refine ⟨fun c => (spec.1 c).trans ?_, spec.2⟩
  let accept := (checkSiteMemory (e := e) hw v (header v) (sortIncident b v) edges rs).1
  have hiff : accept = true ↔ (x.2.all id = true ∧ SortCanonical hw hc b v ∧ MemoryAt m v (SortReplay.decoded hw x.1)) := by
    simp only [x, List.all_nil, true_and, SortReplay.decoded_emittedBlock hw header rs records hrecs]
    exact checkSiteMemory_iff hw hc b v header initial edges he rs
  let passing := x.2.all id = true ∧ SortCanonical hw hc b v ∧ MemoryAt m v (SortReplay.decoded hw x.1)
  change (@ite ℕ passing (Classical.propDecidable _) 1 0) = accept.toNat
  split
  · rename_i h
    rw [hiff.mpr h]; rfl
  · rename_i h
    have ha : accept = false := Bool.eq_false_iff.mpr (fun hp => h (hiff.mp hp))
    rw [ha]; rfl

end RAMTape.SitePost

end VPVNP
end Computability
end OAI

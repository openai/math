import OAI.Computability.VPVNP.RAMSortCost
import OAI.Computability.VPVNP.RAMSortIncident
import OAI.Computability.VPVNP.RAMSortBlockSlices

/-!
# Costed sorting replay on the validator's physical messages

The linear-address scan inspects the exact incident bit intervals allocated
to the site's own sort sends and to its partner's sends. Its acceptance
therefore checks canonicality of both physical fields and exactly the typed
send constraints. Its output recovers the typed validator's sorted block.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMLayout RAMSerialization RAMMemory RAMSort

variable {d e w : ℕ}

private abbrev layers (e d : ℕ) := phases ((2+e)+d) ((2+e)+d) le_rfl

private def physicalLayer (s : Stage ((2+e)+d)) (hs : 2+e ≤ s.stride) :=
  (crossStageEquiv (2+e) d).symm ⟨s, hs⟩

private theorem rawSlice (b : SendArrays d (2^e) w) (v : Fin (2^d)) (s : Stage ((2+e)+d))
    (hs : 2+e ≤ s.stride) (dir : Fin 2) (i : Fin (2^(2+e))) :
    (fun bit : Fin (5*w) ↦ sortIncident b v
      ((fieldStart (2+e) w s.phase s.stride dir i.val).eval + bit.val)) =
      recordSlice (2^e) w
        (b.2 (physicalLayer s hs) (if dir = 0 then v else (physicalLayer s hs).partner v))
        (recordPosition e i) := by
  funext bit
  rw [fieldStart_physical (record_width e) s hs dir i bit, sortIncident_offset]
  have hv : dir.val = 0 ∨ dir.val = 1 := by have := dir.isLt; omega
  rcases hv with he | he
  · obtain rfl : dir = 0 := Fin.ext he
    simp only [ite_true]
    exact incident_send b (.inr (physicalLayer s hs, v, _))
  · obtain rfl : dir = 1 := Fin.ext he
    rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    exact incident_receive_sort ..

/-- Both blocks actually incident at this site in each cross-layer have
canonical record encoding. -/
def SortCanonical (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (b : SendArrays d (2^e) w)
    (v : Fin (2^d)) : Prop :=
  ∀ l, b.2 l v = (messageBits hw hc (parseMessages hw hc b)).2 l v ∧
    b.2 l (l.partner v) = (messageBits hw hc (parseMessages hw hc b)).2 l (l.partner v)

private theorem readSlot_of_canonical (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (b : SendArrays d (2^e) w) (v : Fin (2^d)) (s : Stage ((2+e)+d)) (hs : 2+e ≤ s.stride)
    (dir : Fin 2) (i : Fin (2^(2+e))) (hcan : SortCanonical hw hc b v) :
    (readSlot hw (sortIncident b v) s dir i).1 =
      some ((unpackMessages (parseMessages hw hc b)).memory.sortSends (physicalLayer s hs)
        (if dir = 0 then v else (physicalLayer s hs).partner v) i) := by
  let l := physicalLayer s hs
  let u := if dir = 0 then v else l.partner v
  let records := (parseMessages hw hc b).2 l u
  have hbits : b.2 l u = (blockFormat (2^e) hw).encode records := by
    dsimp only [records, u]
    split
    · exact (hcan l).1
    · exact (hcan l).2
  have hslice : recordSlice (2^e) w (b.2 l u) (recordPosition e i) =
      (recordFormat hw).encode (records (recordPosition e i)) :=
    (congrArg (fun y ↦ recordSlice (2^e) w y (recordPosition e i)) hbits).trans (blockEncode_slice ..)
  simp only [readSlot, rawSlice b v s hs dir i, decodeSlot_eq]
  rw [show (recordFormat hw).decode (recordSlice (2^e) w (b.2 l u) (recordPosition e i)) =
    some (records (recordPosition e i)) from ((recordFormat hw).decode_iff ..).mpr hslice]
  rfl

private theorem loadsOfStages {h : ℕ} (hw : 2 ≤ w) (raw : ℕ → Bool) (v : Fin (2^d))
    (f : ∀ s : Stage (h+d), Sends h d s (OrderedSlot (Word w)))
    (hf : ∀ s, Loads hw raw s (f s) v) (ss : List (Stage (h+d))) (hn : ss.Nodup) :
    LoadsStages hw raw v ss ((fieldsOfStages ss hn) (fun s _ ↦ f s)) := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact ⟨hf s, ih hn.of_cons⟩

private theorem loadsMessages (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (b : SendArrays d (2^e) w)
    (v : Fin (2^d)) (hcan : SortCanonical hw hc b v) :
    LoadsStages hw (sortIncident b v) v (layers e d)
      (physicalFieldsEquiv.{0,0} (2+e) d _ (unpackMessages (parseMessages hw hc b)).memory.sortSends) := by
  apply loadsOfStages hw _ v
    (fun s hs ↦ (unpackMessages (parseMessages hw hc b)).memory.sortSends (physicalLayer s hs))
  intro s hs i
  constructor
  · simpa using readSlot_of_canonical hw hc b v s hs 0 i hcan
  · rw [sourceSite_eq_physical]
    simpa [physicalLayer] using readSlot_of_canonical hw hc b v s hs 1 i hcan
  exact phases_nodup le_rfl

private theorem canonicalOfScan (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (b : SendArrays d (2^e) w)
    (v : Fin (2^d)) (input : Wires (2+e) (OrderedSlot (Word w)))
    (hp : (scanStages hw (sortIncident b v) v (layers e d) input).ok = true) :
    SortCanonical hw hc b v := by
  intro l
  let s := (crossStageEquiv (2+e) d) l
  have hl : physicalLayer s.val s.property = l := (crossStageEquiv (2+e) d).symm_apply_apply l
  have hall (dir : Fin 2) :
      ∀ k, ∃ r, recordSlice (2^e) w (b.2 l (if dir = 0 then v else l.partner v)) k =
        (recordFormat hw).encode r := by
    intro k
    obtain ⟨i, rfl⟩ := (recordPosition e).surjective k
    obtain ⟨r, hr⟩ := scanStages_canonical hw (sortIncident b v) v _ input hp s.val (mem_fullPhases _)
      s.property dir i
    rw [rawSlice b v s.val s.property dir i, hl] at hr
    exact ⟨r, hr⟩
  constructor
  · exact (blockCanonical_iff (2^e) hw _).mpr (by simpa using hall 0)
  · exact (blockCanonical_iff (2^e) hw _).mpr (by simpa using hall 1)

/-- Exact acceptance criterion for the costed local sorting scan on an
arbitrary raw assignment. -/
theorem sortScan_messages (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (b : SendArrays d (2^e) w)
    (v : Fin (2^d)) (input : Wires (2+e) (OrderedSlot (Word w))) :
    (scanStages hw (sortIncident b v) v (layers e d) input).ok = true ↔
      SortCanonical hw hc b v ∧ checks v (layers e d)
        (physicalFieldsEquiv.{0,0} (2+e) d _ (unpackMessages (parseMessages hw hc b)).memory.sortSends)
        input := by
  constructor
  · intro hp
    have hcan := canonicalOfScan hw hc b v input hp
    exact ⟨hcan, ((scanStages_spec hw _ _ _ _ _ (loadsMessages hw hc b v hcan)).2).mp hp⟩
  · rintro ⟨hcan, hp⟩
    exact ((scanStages_spec hw _ _ _ _ _ (loadsMessages hw hc b v hcan)).2).mpr hp

/-- With canonically parsed sorting fields, the record array handed to the
predecessor check is the exact `outputAt` array of the typed validator. -/
theorem sortScan_output (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (b : SendArrays d (2^e) w)
    (v : Fin (2^d)) (input : Wires (2+e) (OrderedSlot (Word w))) (hcan : SortCanonical hw hc b v) :
    (fun i ↦ ((scanStages hw (sortIncident b v) v (layers e d) input).block i).record) =
      outputAt (unpackMessages (parseMessages hw hc b)).memory v input :=
  congrArg (fun f : Wires (2+e) (OrderedSlot (Word w)) ↦ fun i ↦ (f i).record)
    ((scanStages_spec hw _ _ _ _ _ (loadsMessages hw hc b v hcan)).1)

end BurstRAM

end VPVNP
end Computability
end OAI

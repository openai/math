import OAI.Computability.VPVNP.RAMTapeSuccessorGuard
import OAI.Computability.VPVNP.RAMTapeSuccessorEdgeValues
import OAI.Computability.VPVNP.RAMValidatorSuccessor

/-!
# The stack successor guard recognizes the shared-bit validator's fields

On an arbitrary local vector the finite stack program accepts exactly the
canonical present fields and the zero clamps. When the vector comes from a
shared-bit assignment, these tests are the successor parts of the local RAM
validator. A malformed field has zero accepting continuation count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successors

open BurstRAM RAMLayout RAMSerialization

variable {d e w cap : ℕ}

/-- A present successor field decodes to a canonical message, and an absent field consists
entirely of zero bits. -/
def GoodField (hw : 2 ≤ w) (hc : cap < 2 ^ w) (present : Bool) (bits : Fin (8*w) → Bool) : Prop :=
  if present then ∃ x, (successorFormat hw hc).decode bits = some x else bits = fun _ ↦ false

private theorem good_iff (hw : 2 ≤ w) (hc : cap < 2 ^ w) (present : Bool)
    (bits : Fin (8*w) → Bool) :
    Successor.valid present (Successor.wordTags ((arrayBits 8 w).symm bits))
      (decide ((((arrayBits 8 w).symm bits) 1).val ≤ cap)) = true ↔ GoodField hw hc present bits := by
  let s : Stacks SuccessorEdge.Port := fun _ ↦ []
  cases present with
  | true =>
    simpa only [GoodField, ↓reduceIte, SuccessorEdge.edgeResult, List.cons.injEq, and_true]
      using SuccessorEdge.present_verdict_iff hw hc s bits []
  | false =>
    simpa only [GoodField, Bool.false_eq_true, ↓reduceIte, SuccessorEdge.edgeResult,
      List.cons.injEq, and_true] using SuccessorEdge.clamp_verdict_iff s bits ⟨cap, hc⟩ []

/-- The machine's two validity bits, evaluated on an arbitrary fixed-size
incident vector, test the full format including every padding bit. -/
theorem finish_good_iff (hw : 2 ≤ w) (hc : cap < 2 ^ w) (s : Stacks Port) (outgoing incoming : Bool)
    (sent received : Fin (8*w) → Bool) (suffix : List Bool) :
    let out := finish s outgoing incoming sent received ⟨cap, hc⟩ suffix
    (out (.verdict .send)).head? = some true ∧ (out (.verdict .receive)).head? = some true ↔
      GoodField hw hc outgoing sent ∧ GoodField hw hc incoming received := by
  cases incoming <;> simp [finish, afterNormalize, afterEdge, SuccessorEdge.edgeResult, good_iff hw hc]

private theorem present_iff_canonical (hw : 2 ≤ w) (hc : cap < 2 ^ w) (bits : Fin (8*w) → Bool) :
    GoodField hw hc true bits ↔ bits =
      (successorFormat hw hc).encode ((successorFormat hw hc).parse ((arrayBits 8 w).symm bits)) := by
  change (∃ x, (successorFormat hw hc).decode bits = some x) ↔ _
  constructor
  · rintro ⟨x, h⟩
    have he := (successor_decode_iff hw hc _ _).mp h
    rw [he]
    simp [Format.encode, Format.parse_words]
  · intro h
    exact ⟨_, (successor_decode_iff hw hc _ _).mpr h⟩

/-- At shared-bit inputs the missing end vectors are clamped by construction,
and the two remaining tests are exactly the sender and receiver predicates. -/
theorem shared_fields_iff (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w)
    (a : SendArrays d (2 ^ e) w) (v : Fin (2 ^ d)) :
    let bits := RAMLayout.incidentBits a v
    (GoodField hw hc (decide (v.val+1 < 2^d)) (fun j ↦ bits (offset d (2^e) w (.inl (0, j)))) ∧
      GoodField hw hc (decide (0 < v.val)) (fun j ↦ bits (offset d (2^e) w (.inl (1, j))))) ↔
      SuccessorSendOK hw hc a v ∧ SuccessorReceiveOK hw hc a v := by
  dsimp only
  apply and_congr
  · by_cases hv : v.val + 1 < 2 ^ d
    · let j : Fin (2^d-1) := ⟨v.val, by omega⟩
      have he : (fun i ↦ RAMLayout.incidentBits a v (offset d (2^e) w (.inl (0, i)))) = a.1 j := by
        funext i
        rw [RAMLayout.incidentBits_offset]
        exact incident_send _ (.inl (j, i))
      simp only [hv, decide_true, he, present_iff_canonical, SuccessorSendOK, ↓reduceDIte]
      rfl
    · have he : v.val + 1 = 2 ^ d := by have := v.isLt; omega
      simp only [hv, decide_false, GoodField, Bool.false_eq_true, ↓reduceIte, SuccessorSendOK,
        ↓reduceDIte, iff_true]
      exact funext fun i ↦ (RAMLayout.incidentBits_offset ..).trans
        (incident_clamp a _ (peer_send_end v he i))
  · by_cases hv : 0 < v.val
    · let j : Fin (2^d-1) := ⟨v.val-1, by have := v.isLt; omega⟩
      have he : (fun i ↦ RAMLayout.incidentBits a v (offset d (2^e) w (.inl (1, i)))) = a.1 j := by
        funext i
        rw [RAMLayout.incidentBits_offset]
        exact incident_receive_successor a v hv i
      simp only [hv, decide_true, he, present_iff_canonical, SuccessorReceiveOK, ↓reduceDIte]
      rfl
    · have he : v.val = 0 := by omega
      simp only [hv, decide_false, GoodField, Bool.false_eq_true, ↓reduceIte, SuccessorReceiveOK,
        ↓reduceDIte, iff_true]
      exact funext fun i ↦ (RAMLayout.incidentBits_offset ..).trans
        (incident_clamp a _ (peer_receive_start v he i))

/-- The actual table spends the declared budget on valid fields and calls its
continuation once. On malformed fields its accepting multiplicity is zero. -/
theorem checked_shared_count (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w)
    (a : SendArrays d (2 ^ e) w) (s : Stacks Port) (v : Word d) (initial : Word w)
    (hv : s .address = BurstRAM.wordBits v) (hin : s .incident = List.ofFn (RAMLayout.incidentBits a v))
    (hwidth : s .width = List.replicate w true) (hcap : s .cap = BurstRAM.wordBits ⟨2^d * 2^e, hc⟩)
    (hi : s .initial = BurstRAM.wordBits initial) (ht : s .tmp = []) (hu : s .capTmp = [])
    (hblank : ∀ side i, s (.word side i) = []) (c : ℕ → Stacks Port → ℕ) (fuel : ℕ)
    [Decidable (SuccessorSendOK hw hc a v ∧ SuccessorReceiveOK hw hc a v)] :
    let bits := RAMLayout.incidentBits a v
    let out := finish s (decide (v.val+1 < 2^d)) (decide (0 < v.val))
      (fun j ↦ bits (offset d (2^e) w (.inl (0, j)))) (fun j ↦ bits (offset d (2^e) w (.inl (1, j))))
      ⟨2^d * 2^e, hc⟩ ((List.ofFn bits).drop (16*w))
    checked.body.count c (fuel + 2 + steps d w (decide (0 < v.val))) s =
      if SuccessorSendOK hw hc a v ∧ SuccessorReceiveOK hw hc a v then c fuel (guardResult out) else 0 := by
  dsimp only
  have h := read_incident_runs s v ⟨_, hc⟩ initial _ hv hin hwidth hcap hi ht hu hblank
  rw [checked_count_of_read h]
  have he := finish_good_iff hw hc s (decide (v.val+1 < 2^d)) (decide (0 < v.val))
    (fun j ↦ RAMLayout.incidentBits a v (offset d (2^e) w (.inl (0, j))))
    (fun j ↦ RAMLayout.incidentBits a v (offset d (2^e) w (.inl (1, j)))) ((List.ofFn (RAMLayout.incidentBits a v)).drop (16*w))
  have hiff := he.trans (shared_fields_iff hw hc a v)
  by_cases hp : SuccessorSendOK hw hc a v ∧ SuccessorReceiveOK hw hc a v
  · exact (ite_eq_left (hiff.mpr hp)).trans (ite_eq_left hp).symm
  · exact (ite_eq_right (mt hiff.mp hp)).trans (ite_eq_right hp).symm

end RAMTape.Successors

end VPVNP
end Computability
end OAI

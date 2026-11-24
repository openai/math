import OAI.Computability.VPVNP.RAMBitTranscript
import OAI.Computability.VPVNP.RAMSuccessorDecodeCost

/-!
# Reading both successor fields at a site

The two eight-word fields occupy the first `16*w` incident bits in Lemma 10.1.
On an internal edge the site parses and checks the candidate successor. On a
missing edge it checks the zero clamp. The initial site supplies its own start
state, and the terminal site has no target cut. The same fields supply the
two records used in the predecessor check after sorting.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMMemory RAMLayout RAMSerialization

variable {d e w : ℕ}

/-- Read the contiguous field at base address `8*w*dir`. -/
def successorField (w : ℕ) (raw : ℕ → Bool) (dir : Fin 2) : Fin (8 * w) → Bool :=
  fun j ↦ raw (8 * w * dir.val + j.val)

private def zeroPrefix {n : ℕ} (b : Fin n → Bool) : (k : ℕ) → k ≤ n → Bool × ℕ
  | 0, _ => (true, 1)
  | k+1, hk =>
    if b ⟨k, hk⟩ then (false, 6)
    else
      let next := zeroPrefix b k (by omega)
      (next.1, 6 + next.2)

private theorem zeroPrefix_spec {n : ℕ} (b : Fin n → Bool) (k : ℕ) (hk : k ≤ n) :
    (zeroPrefix b k hk).1 = true ↔ ∀ i : Fin n, i.val < k → b i = false := by
  induction k with
  | zero => simp [zeroPrefix]
  | succ k ih =>
    cases h : b ⟨k, hk⟩ with
    | true =>
      simp only [zeroPrefix, h, ↓reduceIte, Bool.false_eq_true, false_iff]
      exact fun hall ↦ Bool.noConfusion (h.symm.trans (hall ⟨k, hk⟩ (by simp)))
    | false =>
      simp only [zeroPrefix, h, Bool.false_eq_true, ↓reduceIte, ih]
      constructor
      · intro hall i hi
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | hi
        · exact hall i hi
        · exact (Fin.ext hi : i = ⟨k, hk⟩) ▸ h
      · exact fun hall i hi ↦ hall i (Nat.lt_succ_of_lt hi)

private theorem zeroPrefix_all {n : ℕ} (b : Fin n → Bool) :
    (zeroPrefix b n le_rfl).1 = true ↔ b = fun _ ↦ false := by
  rw [zeroPrefix_spec]
  exact ⟨fun h ↦ funext fun i ↦ h i i.isLt, fun h i _ ↦ congrFun h i⟩

private theorem zeroPrefix_steps {n : ℕ} (b : Fin n → Bool) (k : ℕ) (hk : k ≤ n) :
    (zeroPrefix b k hk).2 ≤ 6 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have := ih (by omega)
    rw [zeroPrefix]
    split <;> dsimp <;> omega

private structure EdgeRead (w cap : ℕ) where
  value : Option (Successor w cap)
  valid : Bool
  steps : ℕ

/-- Computing the base costs two multiplications. Each decoder bit read adds
the base to its within-field offset. In the zero test this addition is already
included in the six operations per iteration (test, decrement, address, load,
branch on bit, loop branch). The four fixed operations cover base setup,
dispatch and return. -/
private def readEdge {cap : ℕ} (hw : 2 ≤ w) (hc : cap < 2 ^ w) (raw : ℕ → Bool)
    (dir : Fin 2) (present : Bool) : EdgeRead w cap :=
  let bits := successorField w raw dir
  if present then
    let decoded := scanSuccessor hw hc bits
    ⟨some decoded.1.1, decoded.1.2, decoded.2 + 8 * w + 4⟩
  else
    let check := zeroPrefix bits (8 * w) le_rfl
    ⟨none, check.1, check.2 + 4⟩

private theorem readEdge_cost {cap : ℕ} (hw : 2 ≤ w) (hc : cap < 2 ^ w)
    (raw : ℕ → Bool) (dir : Fin 2) (present : Bool) :
    (readEdge hw hc raw dir present).steps ≤ 236 * (w+1) := by
  cases present
  · have := zeroPrefix_steps (successorField w raw dir) _ le_rfl
    simp only [readEdge, Bool.false_eq_true, ↓reduceIte]
    omega
  · have := scanSuccessor_cost hw hc (successorField w raw dir)
    simp only [readEdge, ↓reduceIte]
    omega

private def successorCut {cap : ℕ} (s : Successor w cap) : Cut w :=
  ⟨s.cost.val, s.state⟩

private def successorRecord {cap : ℕ} (s : Successor w cap) : Option (Record (Word w)) :=
  s.lastRecord.map WordRecord.record

/-- The parts of the successor fields needed before and after the local sort. -/
structure SiteSuccessors (w : ℕ) where
  /-- Incoming cumulative cost and persistent state for the site, using the prescribed initial
  cut at the first site. -/
  input : Cut w
  /-- Outgoing successor cut when the site has a following processor in the chain. -/
  output : Option (Cut w)
  /-- Predecessor's final record recovered from the incoming successor field for the boundary
  check. -/
  received : Option (Record (Word w))
  /-- Final record carried by the site's outgoing successor field and checked against its local
  record sequence. -/
  sent : Option (Record (Word w))
  /-- Whether both successor fields pass their decoding checks, including the zero clamp where
  an edge is absent. -/
  valid : Bool

/-- Check both fields even on malformed input. The fixed allowance covers
site endpoint tests, copies of the selected cut and record registers, and
combining the two success flags. -/
def scanSuccessors (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (initial : Word w) (v : Fin (2^d))
    (raw : ℕ → Bool) : SiteSuccessors w × ℕ :=
  let inc := readEdge hw hc raw 1 (decide (0 < v.val))
  let out := readEdge hw hc raw 0 (decide (v.val + 1 < 2^d))
  (⟨(inc.value.map successorCut).getD ⟨0, some initial⟩, out.value.map successorCut,
    inc.value.bind successorRecord, out.value.bind successorRecord, out.valid && inc.valid⟩,
    inc.steps + out.steps + 32)

/-- A uniform bound on raw incident arrays, including nonzero end fields
and unrecognized tags. -/
theorem scanSuccessors_cost (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (initial : Word w)
    (v : Fin (2^d)) (raw : ℕ → Bool) :
    (scanSuccessors hw hc initial v raw).2 ≤ 512 * (w+1) := by
  simp only [scanSuccessors]
  have := readEdge_cost hw hc raw 1 (decide (0 < v.val))
  have := readEdge_cost hw hc raw 0 (decide (v.val + 1 < 2^d))
  omega

/-- The first conjunct of the outgoing encoding check. -/
def SuccessorSendOK (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : SendArrays d (2^e) w)
    (v : Fin (2^d)) : Prop :=
  if h : v.val + 1 < 2^d then
    a.1 ⟨v.val, by omega⟩ = (messageBits hw hc (parseMessages hw hc a)).1 ⟨v.val, by omega⟩
  else True

/-- The first conjunct of the incoming encoding check. -/
def SuccessorReceiveOK (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : SendArrays d (2^e) w)
    (v : Fin (2^d)) : Prop :=
  if h : 0 < v.val then
    a.1 ⟨v.val - 1, by have := v.isLt; omega⟩ =
      (messageBits hw hc (parseMessages hw hc a)).1 ⟨v.val - 1, by have := v.isLt; omega⟩
  else True

private theorem successorField_at (raw : ℕ → Bool) (a : SendArrays d (2^e) w)
    (v : Fin (2^d)) (hraw : ∀ slot, raw (offset d (2^e) w slot).val =
      (incidentEquiv d (2^e) w a).val (v, slot)) (dir : Fin 2) (j : Fin (8*w)) :
    successorField w raw dir j = (incidentEquiv d (2^e) w a).val (v, .inl (dir, j)) := by
  simpa [successorField, offset_successor] using hraw (.inl (dir, j))

private theorem send_read_spec (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) (raw : ℕ → Bool)
    (hraw : ∀ slot, raw (offset d (2^e) w slot).val = (incidentEquiv d (2^e) w a).val (v,slot)) :
    let out := readEdge hw hc raw 0 (decide (v.val + 1 < 2^d))
    (out.value = if h : v.val + 1 < 2^d then some ((parseMessages hw hc a).1 ⟨v.val, by omega⟩)
      else none) ∧ (out.valid = true ↔ SuccessorSendOK hw hc a v) := by
  by_cases hv : v.val + 1 < 2^d
  · let edge : Fin (2^d-1) := ⟨v.val, by omega⟩
    have he : successorField w raw 0 = a.1 edge := funext fun j ↦
      (successorField_at raw a v hraw 0 j).trans (incident_send a (.inl (edge, j)))
    simp only [hv, decide_true, readEdge, ↓reduceIte, ↓reduceDIte, he, scanSuccessor_value,
      scanSuccessor_valid, SuccessorSendOK]
    exact ⟨rfl, Iff.rfl⟩
  · have he : successorField w raw 0 = fun _ ↦ false := funext fun j ↦
      (successorField_at raw a v hraw 0 j).trans (incident_clamp a _ (peer_send_end v (by
        have := v.isLt; omega) j))
    simp [hv, readEdge, he, zeroPrefix_all, SuccessorSendOK]

private theorem receive_read_spec (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) (raw : ℕ → Bool)
    (hraw : ∀ slot, raw (offset d (2^e) w slot).val = (incidentEquiv d (2^e) w a).val (v,slot)) :
    let inc := readEdge hw hc raw 1 (decide (0 < v.val))
    (inc.value = if h : 0 < v.val then
      some ((parseMessages hw hc a).1 ⟨v.val-1, by have := v.isLt; omega⟩) else none) ∧
      (inc.valid = true ↔ SuccessorReceiveOK hw hc a v) := by
  by_cases hv : 0 < v.val
  · let edge : Fin (2^d-1) := ⟨v.val-1, by have := v.isLt; omega⟩
    have he : successorField w raw 1 = a.1 edge := funext fun j ↦
      (successorField_at raw a v hraw 1 j).trans (incident_receive_successor a v hv j)
    simp only [hv, decide_true, readEdge, ↓reduceIte, ↓reduceDIte, he, scanSuccessor_value,
      scanSuccessor_valid, SuccessorReceiveOK]
    exact ⟨rfl, Iff.rfl⟩
  · have he : successorField w raw 1 = fun _ ↦ false := funext fun j ↦
      (successorField_at raw a v hraw 1 j).trans (incident_clamp a _ (peer_receive_start v (by omega) j))
    simp [hv, readEdge, he, zeroPrefix_all, SuccessorReceiveOK]

/-- Match both cut registers, both record registers and the validity flag
to the typed site validator on its incident shared-bit assignment. -/
structure SiteSuccessors.Spec (s : SiteSuccessors w) (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (initial : Word w) (v : Fin (2^d)) (a : SendArrays d (2^e) w) : Prop where
  input_eq : s.input = inputCut ⟨0, some initial⟩ (unpackMessages (parseMessages hw hc a)).chain v
  output_eq : s.output = outputCut (unpackMessages (parseMessages hw hc a)).chain v
  received_eq : s.received = RAMBoundary.receive (unpackMessages (parseMessages hw hc a)).memory.lastRecords v
  sent_eq : s.sent = RAMBoundary.outgoing (unpackMessages (parseMessages hw hc a)).memory.lastRecords v
  valid_iff : s.valid = true ↔ SuccessorSendOK hw hc a v ∧ SuccessorReceiveOK hw hc a v

theorem scanSuccessors_spec (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (initial : Word w)
    (v : Fin (2^d)) (raw : ℕ → Bool) (a : SendArrays d (2^e) w)
    (hraw : ∀ slot, raw (offset d (2^e) w slot).val = (incidentEquiv d (2^e) w a).val (v,slot)) :
    (scanSuccessors hw hc initial v raw).1.Spec hw hc initial v a := by
  obtain ⟨hout, hvalidOut⟩ := send_read_spec hw hc a v raw hraw
  obtain ⟨hin, hvalidIn⟩ := receive_read_spec hw hc a v raw hraw
  constructor
  · simp only [scanSuccessors, hin, inputCut]
    by_cases hv : 0 < v.val
    · simp [hv, Nat.ne_of_gt hv, successorCut, unpackMessages]
    · simp [show v.val = 0 by omega]
  · simp only [scanSuccessors, hout, outputCut]
    split <;> rfl
  · simp only [scanSuccessors, hin]
    rcases v with ⟨i, hi⟩
    cases i <;> rfl
  · simp only [scanSuccessors, hout, RAMBoundary.outgoing]
    split <;> rfl
  · simp only [scanSuccessors, Bool.and_eq_true, hvalidOut, hvalidIn]

end BurstRAM

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.UniversalMachine

/-!
# Recognizing the program prefix

A successful decode consumes exactly the canonical prefix of the returned machine. The length of
that prefix bounds the state space to be represented by a verifier on a fixed input length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

open private readUnary readFields decodeTable readRows
  readInstruction readBranch checkFin from OAI.Computability.VPVNP.UniversalMachine

private theorem readUnary_canonical {input rest : Word} {k : ℕ}
    (h : readUnary input = some (k, rest)) : input = unary k ++ rest := by
  induction input generalizing k rest with
  | nil => simp [readUnary] at h
  | cons b xs ih =>
    cases b with
    | false =>
      simp [readUnary] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | true =>
      obtain ⟨⟨j, ys⟩, hj, heq⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [ih hj]
      rfl

private theorem readFields_canonical {input : Word} {fields : List ℕ}
    (h : readFields input = some fields) : input = fields.flatMap unary := by
  induction input generalizing fields with
  | nil =>
    simp [readFields] at h
    subst fields
    rfl
  | cons b xs ih =>
    cases b with
    | false =>
      obtain ⟨ys, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [ih hy]
      rfl
    | true =>
      simp only [readFields] at h
      obtain ⟨ks, hk, heq⟩ := Option.bind_eq_some_iff.mp h
      cases ks with
      | nil => contradiction
      | cons j ys =>
        change some ((j + 1) :: ys) = some fields at heq
        obtain rfl := Option.some.inj heq
        rw [ih hk]
        rfl

private theorem checkFin_canonical {m k : ℕ} {a : Fin m} (h : checkFin m k = some a) :
    k = a.val := by
  unfold checkFin at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · contradiction

private theorem readInstruction_canonical {extra : ℕ} {xs tail : List ℕ} {a : Instruction extra}
    (h : readInstruction extra xs = some (a, tail)) : xs = instructionFields a ++ tail := by
  unfold readInstruction at h
  split at h
  · obtain ⟨target, hq, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨first, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨move₁, hu, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨second, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨move₂, hv, eq⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj eq)
    simp [instructionFields, checkFin_canonical hq, checkFin_canonical hx,
      checkFin_canonical hu, checkFin_canonical hy, checkFin_canonical hv]
  · contradiction

private theorem readBranch_canonical {extra : ℕ} {xs tail : List ℕ} {b : Branches extra}
    (h : readBranch extra xs = some (b, tail)) : xs = branchFields b ++ tail := by
  unfold readBranch at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rfl
  · obtain ⟨⟨a, rest⟩, ha, heq⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
    rw [readInstruction_canonical ha]
    rfl
  · obtain ⟨⟨a, rest⟩, ha, hs⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨c, last⟩, hc, heq⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
    rw [readInstruction_canonical ha, readInstruction_canonical hc]
    simp [branchFields, List.append_assoc]
  · contradiction

private theorem readRows_canonical {extra count : ℕ} {xs tail : List ℕ} {bs : List (Branches extra)}
    (h : readRows extra count xs = some (bs, tail)) : xs = bs.flatMap branchFields ++ tail := by
  induction count generalizing xs bs with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rfl
  | succ count ih =>
    obtain ⟨⟨b, rest⟩, hb, hs⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨rows, last⟩, hr, heq⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
    rw [readBranch_canonical hb, ih hr]
    simp [List.flatMap_cons, List.append_assoc]


private theorem decodeTable_canonical {bits : Word} {p : Program}
    (h : decodeTable bits = some p) : bits = tableBits p := by
  obtain ⟨fields, hfields, heq⟩ := Option.bind_eq_some_iff.mp h
  rw [readFields_canonical hfields]
  cases fields with
  | nil =>
    change some emptyProgram = some p at heq
    obtain rfl := Option.some.inj heq
    rfl
  | cons k xs =>
    obtain ⟨⟨rows, tail⟩, hrows, hp⟩ := Option.bind_eq_some_iff.mp heq
    cases tail with
    | cons _ _ => contradiction
    | nil =>
      change (if h : rows.length = (k + 1) * 9 then some ⟨k + 1, rows, h⟩ else none) =
        some p at hp
      split at hp
      · obtain rfl := Option.some.inj hp
        simpa [tableBits] using congrArg (fun ns => (k :: ns).flatMap unary)
          (readRows_canonical hrows)
      · contradiction

/-- An input successfully decodes to a given program exactly when it begins with that program's
self-delimiting code. -/
theorem decode_eq_some_iff {input : Word} {p : Program} :
    decode input = some p ↔ ∃ payload, input = programPrefix p ++ payload := by
  constructor
  · intro h
    obtain ⟨⟨len, rest⟩, hlen, hp⟩ := Option.bind_eq_some_iff.mp h
    change (if len ≤ rest.length then decodeTable (rest.take len) else none) = some p at hp
    split at hp
    next hle =>
      have ht := decodeTable_canonical hp
      have hl : (tableBits p).length = len := by simp [← ht, hle]
      refine ⟨rest.drop len, ?_⟩
      rw [readUnary_canonical hlen, programPrefix, hl, List.append_assoc, ← ht,
        List.take_append_drop]
    next => contradiction
  · rintro ⟨payload, rfl⟩
    exact decode_programPrefix p payload

private theorem row_fields_length {extra : ℕ} (rows : List (Branches extra)) :
    rows.length ≤ (rows.flatMap branchFields).length := by
  induction rows with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hb : 1 ≤ (branchFields b).length := by cases b <;> simp [branchFields]
    omega

private theorem unary_fields_length (fields : List ℕ) :
    fields.length ≤ (fields.flatMap unary).length := by
  induction fields with
  | nil => rfl
  | cons k fields ih =>
    simp only [List.flatMap_cons, List.length_cons, List.length_append, unary,
      List.length_replicate]
    change _ ≤ k + 1 + _
    omega

/-- A nonempty table spends one unary bit per running state in its header and at least nine bits
per running state on its rows. The empty table satisfies the same bound. -/
theorem tableBits_length_ge (p : Program) : 10 * p.extra ≤ (tableBits p).length := by
  by_cases h : p.extra = 0
  · simp [h]
  · have h₁ := row_fields_length p.rows
    have h₂ := unary_fields_length (p.rows.flatMap branchFields)
    rw [p.rows_length] at h₁
    simp only [tableBits, ite_eq_right h, List.flatMap_cons, List.length_append, unary,
      List.length_replicate]
    change _ ≤ p.extra - 1 + 1 + _
    omega

/-- A decoded program occupies a unary-framed prefix of length at least twenty bits per running
state, plus the terminator. -/
theorem decoded_state_bound {p : Program} {input : Word} (h : decode input = some p) :
    20 * p.extra + 1 ≤ input.length := by
  obtain ⟨payload, rfl⟩ := decode_eq_some_iff.mp h
  have htable := tableBits_length_ge p
  simp only [List.length_append, programPrefix, unary, List.length_replicate]
  change _ ≤ (tableBits p).length + 1 + (tableBits p).length + payload.length
  omega

theorem decoded_extra_le_length {p : Program} {input : Word} (h : decode input = some p) :
    p.extra ≤ input.length := by
  have := decoded_state_bound h
  omega

end UniversalMachine

end VPVNP
end Computability
end OAI

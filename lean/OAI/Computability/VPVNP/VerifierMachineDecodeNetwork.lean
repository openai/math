import OAI.Computability.VPVNP.VerifierMachineDecodeFinish
import OAI.Computability.VPVNP.VerifierMachineNetwork

/-!
# Boolean circuit for decoding a literal transition table

The circuit simultaneously tests candidate lengths and state counts. For each output
query it stores a bit at each possible endpoint of the prefix parsed so far. One
layer consumes a complete transition row. Once a candidate has consumed all its
rows, later layers copy its bits. The final disjunction checks the endpoint against
the outer length header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierMachineDecode

open UniversalMachine
open VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

private abbrev Offset (n : ℕ) := Fin (n + 1)

private abbrev DecodeState (n : ℕ) :=
  Fin n ⊕ (DecoderWire n × Offset n × Offset n × Offset n)

private def beginExpr (n : ℕ) : DecodeState n → Expr (Fin n)
  | .inl i => .input i
  | .inr (_, len, extra, pos) =>
    if pos.val = (header len extra).length then matchAt n 0 (header len extra) else .const false

private noncomputable def nextExpr (n t : ℕ) : DecodeState n → Expr (DecodeState n)
  | .inl i => .input (.inl i)
  | .inr (q, len, extra, pos) =>
    if t < 9 * extra.val then
      (rowStep n extra pos (keepRow q t)).rename
        (Sum.elim Sum.inl (fun i => .inr (q, len, extra, i)))
    else .input (.inr (q, len, extra, pos))

private noncomputable def parse (n t : ℕ) : Frame (Fin n) (DecodeState n) :=
  ((Frame.initial id).step (beginExpr n)).steps (nextExpr n) t

private theorem parse_eval {n : ℕ} (x : Fin n → Bool) (t : ℕ) :
    (∀ i, (parse n t).eval x (.inl i) = x i) ∧
    (∀ (q : DecoderWire n) (len extra pos : Offset n),
      (parse n t).eval x (.inr (q, len, extra, pos)) = true ↔
        Reach (List.ofFn x) q len extra t pos) := by
  induction t with
  | zero =>
    have hx : (Frame.initial id : Frame (Fin n) (Fin n)).eval x = x := by
      funext i
      simp
    constructor
    · intro i
      simp [parse, beginExpr, Expr.eval, hx]
    · intro q len extra pos
      rw [Reach_zero]
      by_cases hp : pos.val = (header len extra).length <;>
        simp [parse, beginExpr, hp, hx, Expr.eval, eval_matchAt]
  | succ t ih =>
    have hstep : parse n (t + 1) = (parse n t).step (nextExpr n t) := rfl
    constructor
    · intro i
      simpa [hstep, nextExpr, Expr.eval] using ih.1 i
    · intro q len extra pos
      rw [hstep, Frame.step_eval]
      by_cases ht : t < 9 * extra.val
      · have he : (fun i : Fin n ⊕ Offset n =>
              (parse n t).eval x (Sum.elim Sum.inl (fun j => .inr (q, len, extra, j)) i)) =
            Sum.elim x (fun j => (parse n t).eval x (.inr (q, len, extra, j))) := by
          funext i
          cases i with
          | inl i => exact ih.1 i
          | inr i => rfl
        simp only [nextExpr, ite_eq_left ht, Expr.eval_rename, he, rowStep_eval, ih.2]
        rw [Reach_succ_of_lt q len extra t pos ht]
        constructor <;> rintro ⟨b, i, hb, hi, hp, hm⟩ <;>
          exact ⟨b, ⟨i.val, by simpa using i.isLt⟩, hb, hi, hp, hm⟩
      · simpa only [nextExpr, ite_eq_right ht, Expr.eval,
          Reach_succ_of_le q len extra t pos (Nat.le_of_not_gt ht)] using ih.2 q len extra pos

private def endpointExpr {n : ℕ} (q : DecoderWire n) :
    Offset n × Offset n × Offset n → Expr (DecodeState n)
  | (len, extra, pos) =>
    if queryAllowed q extra ∧ pos.val = 2 * len.val + 1 then .input (.inr (q, len, extra, pos))
    else .const false

private noncomputable def finishExpr {n : ℕ} (q : DecoderWire n) : Expr (DecodeState n) :=
  Expr.disjoin (Finset.univ.toList.map (endpointExpr q))

private theorem finishExpr_eval {n : ℕ} (q : DecoderWire n) (s : DecodeState n → Bool) :
    (finishExpr q).eval s = true ↔
    ∃ len extra : Offset n, queryAllowed q extra ∧
      ∃ pos : Offset n, pos.val = 2 * len.val + 1 ∧ s (.inr (q, len, extra, pos)) = true := by
  simp only [finishExpr, Expr.eval_disjoin_true, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and, exists_exists_eq_and]
  constructor
  · rintro ⟨⟨len, extra, pos⟩, h⟩
    simp only [endpointExpr] at h
    split at h
    · rename_i hp
      exact ⟨len, extra, hp.1, pos, hp.2, h⟩
    · contradiction
  · rintro ⟨len, extra, hq, pos, hp, h⟩
    exact ⟨⟨len, extra, pos⟩, by simpa [endpointExpr, hq, hp, Expr.eval] using h⟩

/-- Decode every output bit of the literal table from the same input fragment. -/
noncomputable def decoder (n : ℕ) : Frame (Fin n) (DecoderWire n) :=
  (parse n (9 * n)).step finishExpr

/-- Every accepted bit describes the unique program parsed from the input. -/
theorem decoder_eval_iff {n : ℕ} (x : Fin n → Bool) (q : DecoderWire n) :
    (decoder n).eval x q = true ↔ ∃ p, decode (List.ofFn x) = some p ∧ wireHolds p q := by
  simp only [decoder, Frame.step_eval, finishExpr_eval, (parse_eval x (9 * n)).2]
  exact finished_iff x q

private theorem beginExpr_size_le (n : ℕ) (i : DecodeState n) :
    (beginExpr n i).size ≤ 8 * (n + 1) := by
  rcases i with i | ⟨q, len, extra, pos⟩
  · simp only [beginExpr, Expr.size]
    omega
  · simp only [beginExpr]
    split
    · have h := size_matchAt n 0 (header len extra)
      rw [header_length] at h
      have := len.isLt
      have := extra.isLt
      omega
    · simp only [Expr.size]
      omega

private theorem nextExpr_size_le (n t : ℕ) (i : DecodeState n) :
    (nextExpr n t i).size ≤ 200000 * (n + 1) ^ 3 := by
  rcases i with i | ⟨q, len, extra, pos⟩
  · simp only [nextExpr, Expr.size]
    exact Nat.succ_le_of_lt (by positivity)
  · simp only [nextExpr]
    split
    · rw [Expr.size_rename]
      exact rowStep_size_le n extra pos (keepRow q t) (Nat.le_of_lt_succ extra.isLt)
    · simp only [Expr.size]
      exact Nat.succ_le_of_lt (by positivity)

private theorem finishExpr_size_le {n : ℕ} (q : DecoderWire n) :
    (finishExpr q).size ≤ 2 * (n + 1) ^ 3 + 1 := by
  apply (Expr.size_disjoin_le _ 1 ?_).trans
  · simp [Offset, pow_succ, Nat.mul_assoc, Nat.mul_comm]
  · intro e he
    obtain ⟨⟨len, extra, pos⟩, _, rfl⟩ := List.mem_map.mp he
    simp only [endpointExpr]
    split <;> simp [Expr.size]

private theorem query_count_le (n : ℕ) :
    Fintype.card (DecoderWire n) ≤ 2000 * (n + 1) ^ 2 := by
  rw [decoderWire_card]
  nlinarith [Nat.zero_le (n ^ 2)]

private theorem parse_width_le (n : ℕ) :
    Fintype.card (DecodeState n) ≤ 2001 * (n + 1) ^ 5 := by
  simp only [DecodeState, Offset, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have hn : n ≤ (n + 1) ^ 5 := by
    calc n ≤ n + 1 := by omega
         _ ≤ (n + 1) ^ 5 := Nat.le_self_pow (by decide) _
  calc
    _ ≤ (n + 1) ^ 5 + 2000 * (n + 1) ^ 2 * ((n + 1) * ((n + 1) * (n + 1))) := by
      gcongr
      exact query_count_le n
    _ = _ := by ring

/-- The number of gates is polynomial even though the table is part of the input. -/
theorem decoder_size_le (n : ℕ) : (decoder n).size ≤ 6000000000 * (n + 1) ^ 9 := by
  let first := (Frame.initial id).step (beginExpr n)
  have hfirst := Frame.step_size_le (Frame.initial id) (beginExpr n) _ (beginExpr_size_le n)
  have hparse := Frame.steps_size_le first (nextExpr n) (9 * n) _
    (fun t _ => nextExpr_size_le n t)
  have hfinish := Frame.step_size_le (parse n (9 * n)) finishExpr _ finishExpr_size_le
  change (decoder n).size ≤ (first.steps (nextExpr n) (9 * n)).size + _ at hfinish
  rw [Frame.initial_size, Nat.zero_add] at hfirst
  change first.size ≤ _ at hfirst
  have hw := parse_width_le n
  have hq := query_count_le n
  calc
    _ ≤ Fintype.card (DecodeState n) * (8 * (n + 1)) +
        9 * n * (Fintype.card (DecodeState n) * (200000 * (n + 1) ^ 3)) +
        Fintype.card (DecoderWire n) * (2 * (n + 1) ^ 3 + 1) := by omega
    _ ≤ 2001 * (n + 1) ^ 5 * (8 * (n + 1)) +
        9 * (n + 1) * (2001 * (n + 1) ^ 5 * (200000 * (n + 1) ^ 3)) +
        2000 * (n + 1) ^ 2 * (2 * (n + 1) ^ 3 + 1) := by
      gcongr
      omega
    _ ≤ _ := by ring_nf; omega

end VerifierMachineDecode

end VPVNP
end Computability
end OAI

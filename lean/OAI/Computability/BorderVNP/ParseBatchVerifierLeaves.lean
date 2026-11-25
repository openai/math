import OAI.Computability.BorderVNP.ParseBatchVerifierLeavesSort
import OAI.Computability.BorderVNP.ParseBatchVerifierLeavesEncoding

/-!
# Circuit for the leaf check in Lemma 2.3

The free wires are the query and the guessed preorder record bits. Each sorting
lane selects just the tag, selected bit and position field of its record.
No bits are guessed for the padding or for the reference query array.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLeaves

open VPVNP VPVNP.VerifierNetwork BorderVNP.ParseRecords BorderVNP.ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin

variable {m g n rows b : ℕ}

/-- Query bits followed by all guessed bits of the preorder records. -/
abbrev Inputs (m g n rows : ℕ) := Fin m ⊕ (Fin rows × BitSlot (recordWidth m g n))

private def rowExpr (m g n rows : ℕ) (i : Fin rows) :
    Fin (recordWidth m g n + 2) → Expr (Inputs m g n rows) :=
  Fin.cons (.input (.inr (i, .inl false)))
    (Fin.cons (.input (.inr (i, .inl true))) fun j => .input (.inr (i, .inr (5, j))))

private def queryExpr (g n rows : ℕ) (i : Fin m) :
    Fin (recordWidth m g n + 2) → Expr (Inputs m g n rows) :=
  Fin.cons (.const false) (Fin.cons (.input (.inl i)) fun j =>
    .const (RAMSerialization.wordBits _ ⟨i.val, position_lt g n i⟩ j))

private def dummyExpr (m g n rows : ℕ) :
    Fin (recordWidth m g n + 2) → Expr (Inputs m g n rows) :=
  fun j => .const (keyBits (m := m) g n none j)

private def prepare (m g n rows b : ℕ) :
    SortInputs b (recordWidth m g n + 2) → Expr (Inputs m g n rows)
  | .inl (i, j) => if h : i.val < rows then rowExpr m g n rows ⟨i.val,h⟩ j else dummyExpr m g n rows j
  | .inr (i, j) => if h : i.val < m then queryExpr g n rows ⟨i.val,h⟩ j else dummyExpr m g n rows j

/-- The shared-gate Boolean verifier for the leaf multiset. Its two sort arrays
are filled deterministically with record labels and the external query. -/
noncomputable def frame (m g n rows b : ℕ) : Frame (Inputs m g n rows) Unit :=
  (compareFrame b (recordWidth m g n + 2)).subst ((Frame.initial id).step (prepare m g n rows b))

/-- Canonical input values used to state the correspondence with typed records. -/
def inputBits (q : Fin m → Bool)
    (r : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n) : Inputs m g n rows → Bool :=
  Sum.elim q (fun a => packBits (r a.1) a.2)

private theorem rowExpr_eval (q : Fin m → Bool)
    (r : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n) (i : Fin rows) :
    (fun j => (rowExpr m g n rows i j).eval (inputBits q r)) = keyBits g n (terminal (r i)) := by
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j
  all_goals
    rcases hr : r i with ⟨a,v,bit⟩ | ⟨d,a,l,u,v⟩ <;>
      simp [rowExpr, StatementCircuit.Expr.eval, inputBits, hr, packBits, terminal, pack, keyBits,
        Fields.word, RAMSerialization.wordBits_zero]

private theorem queryExpr_eval (q : Fin m → Bool)
    (r : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n) (i : Fin m) :
    (fun j => (queryExpr g n rows i j).eval (inputBits q r)) = keyBits g n (some (i, q i)) := by
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j <;>
    simp [queryExpr, StatementCircuit.Expr.eval, inputBits, keyBits]

private theorem prepare_left (q : Fin m → Bool)
    (r : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n) (i : Fin (2^b)) :
    (fun j => (prepare m g n rows b (.inl (i,j))).eval (inputBits q r)) =
      keyBits g n (pad (terminal ∘ r) none i) := by
  by_cases h : i.val < rows
  · simpa only [prepare, h, ↓reduceDIte, pad, Function.comp_apply] using rowExpr_eval q r ⟨i.val,h⟩
  · simp [prepare, h, pad, dummyExpr, StatementCircuit.Expr.eval]

private theorem prepare_right (q : Fin m → Bool)
    (r : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n) (i : Fin (2^b)) :
    (fun j => (prepare m g n rows b (.inr (i,j))).eval (inputBits q r)) =
      keyBits g n (pad (fun t => some (t, q t)) none i) := by
  by_cases h : i.val < m
  · simpa only [prepare, h, ↓reduceDIte, pad] using queryExpr_eval q r ⟨i.val,h⟩
  · simp [prepare, h, pad, dummyExpr, StatementCircuit.Expr.eval]

/-- On canonical preorder records the concrete Boolean circuit accepts exactly the
multiset of leaves requested by the external query, with all multiplicities. -/
theorem frame_eval (d : Fin n) (q : Fin m → Bool)
    (r : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n)
    (hd : rows = 2*d.val+1) (hm : m = d.val+1) (hcap : rows ≤ 2^b) :
    (frame m g n rows b).eval (inputBits q r) () = true ↔
      Matches d (fun i => (i, q i)) (List.ofFn r) := by
  have hinput : (Frame.initial id).eval (inputBits q r) = inputBits q r := by
    funext t
    simp
  simp only [frame, Frame.subst_eval, compareFrame_eval, Frame.step_eval, hinput]
  simp_rw [prepare_left, prepare_right]
  exact padded_keys_iff d (fun i => (i, q i)) r hd hm hcap

/-- Arbitrary guessed bit strings that pass the format checks agree with the
canonical input. In particular, unused bits create no extra accepting encodings. -/
theorem frame_eval_of_unpacked (d : Fin n) (x : Inputs m g n rows → Bool)
    (r : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n)
    (hr : ∀ i, unpack m g n (fieldsOfBits (fun j => x (.inr (i,j)))) = some (r i))
    (hd : rows = 2*d.val+1) (hm : m = d.val+1) (hcap : rows ≤ 2^b) :
    (frame m g n rows b).eval x () = true ↔
      Matches d (fun i => (i, x (.inl i))) (List.ofFn r) := by
  have hx : x = inputBits (fun i => x (.inl i)) r := by
    funext i
    rcases i with t | ⟨i,j⟩
    · rfl
    · exact congrFun (unpack_bits_iff.mp (hr i)) j
  conv_lhs => rw [hx]
  exact frame_eval d _ r hd hm hcap

private theorem prepare_size (t : SortInputs b (recordWidth m g n + 2)) :
    (prepare m g n rows b t).size ≤ 1 := by
  rcases t with ⟨i,j⟩ | ⟨i,j⟩ <;> simp only [prepare] <;> split
  all_goals
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j <;>
      simp [rowExpr, queryExpr, dummyExpr, StatementCircuit.Expr.size]

/-- Near-linear gate count at a power-of-two row bound. The additive cost is
the wiring of the two key blocks and the scan after sorting. -/
theorem frame_size (m g n rows b : ℕ) :
    let w := recordWidth m g n + 2
    (frame m g n rows b).size ≤ 2 * (b^2 * (2^b * (24*w+1))) + 12 * (2^b * w) + 2 := by
  let w := recordWidth m g n + 2
  have h := Frame.step_size_le (Frame.initial (id : Inputs m g n rows → Inputs m g n rows))
    (prepare m g n rows b) 1 (fun t => prepare_size t)
  simp only [Frame.initial_size, zero_add, mul_one, SortInputs, Pins, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin] at h
  have hs := compareFrame_size b w
  dsimp only
  rw [frame, Frame.subst_size]
  dsimp only [w] at hs
  omega

end ParseBatchLeaves

end BorderVNP
end Computability
end OAI

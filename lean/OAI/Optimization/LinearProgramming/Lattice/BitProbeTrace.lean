import OAI.Optimization.LinearProgramming.Lattice.BitProbe
import OAI.Optimization.LinearProgramming.Lattice.QuerySize

/-! Exact finite traces of the residual-probe row interpreter. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

/-- An execution segment can stop immediately before its continuation emits the next row. -/
inductive Steps (o : Row → Bool) : Action → List Row → Action → Prop
  | stop (a) : Steps o a [] a
  | ask {a c qs t} (tail : Steps o (advance (o a) c) qs t) : Steps o (.inr (a,c)) (a::qs) t

namespace Steps

theorem append {o a b c qs rs} (h : Steps o a qs b) (k : Steps o b rs c) : Steps o a (qs++rs) c := by
  induction h with
  | stop => exact k
  | ask _ ih => exact .ask (ih k)

theorem finish {o a b qs rs r} (h : Steps o a qs b) (k : Runs o b rs r) : Runs o a (qs++rs) r := by
  induction h with
  | stop => exact k
  | ask _ ih => exact .ask (ih k)

end Steps

/-- The mathematical decision tree logs queries in reverse order. A bit-stack segment
consumes the serialized row at the moment it makes the oracle call. -/
def queryRows {p : ℕ} {α : Type*} (o : (Fin p → ℤ) → Bool) (t : SignQueries p α) : List Row :=
  (SignQueries.history o t).reverse.map List.ofFn

@[simp] theorem queryRows_done {p : ℕ} {α : Type*} (o : (Fin p → ℤ) → Bool) (v : α) :
    queryRows o (.done v) = [] := rfl

@[simp] theorem queryRows_ask {p : ℕ} {α : Type*} (o : (Fin p → ℤ) → Bool)
    (a : Fin p → ℤ) (t : Bool → SignQueries p α) :
    queryRows o (.ask a t) = List.ofFn a :: queryRows o (t (o a)) := by
  simp [queryRows,SignQueries.history]

@[simp] theorem queryRows_bind {p : ℕ} {α β : Type*} (o : (Fin p → ℤ) → Bool)
    (t : SignQueries p α) (c : α → SignQueries p β) :
    queryRows o (t.bind c) = queryRows o t ++ queryRows o (c (SignQueries.run o t)) := by
  simp [queryRows]

/-- Both the orientation of a candidate and the comparison with its predecessor are
queried, including when the rows are equal or identically zero. -/
private theorem max_one {p : ℕ} (O : Row → Bool) (o : (Fin p→ℤ) → Bool)
    (h : ∀ a, O (List.ofFn a) = o a) (z : Params) (pending : IntMatrix) (a best : Fin p→ℤ) :
    let att := if o a then a else -a
    Steps O (nextMax z (List.ofFn a :: pending) (List.ofFn best))
      [List.ofFn a,List.ofFn (att-best)]
      (nextMax z pending (List.ofFn (if o (att-best) then att else best))) := by
  dsimp only
  apply Steps.ask
  change Steps O (orient (O (List.ofFn a)) ((z,pending),(List.ofFn a,List.ofFn best))) _ _
  rw [h]
  let att := if o a then a else -a
  have ha : (if o a then List.ofFn a else (List.ofFn a).map Neg.neg) = List.ofFn att := by
    cases hc : o a with
    | false => simpa only [att,hc,Bool.false_eq_true,ite_false] using negateRow_pack a
    | true => simp only [att,hc,ite_true]
  simp only [orient,ha,rowDifference_pack]
  apply Steps.ask
  change Steps O (nextMax z pending (if O (List.ofFn (att-best)) then List.ofFn att else List.ofFn best)) [] _
  rw [h]
  cases o (att-best) <;> exact .stop _

/-- For any pending continuation, walking the reversed row list emits precisely the
maximum tree's chronological query list and preserves its selected row. -/
theorem max_prefix {p : ℕ} (O : Row → Bool) (o : (Fin p→ℤ) → Bool)
    (h : ∀ a, O (List.ofFn a) = o a) (z : Params) (rows : List (Fin p→ℤ)) (pending : IntMatrix) :
    Steps O (nextMax z ((rows.map List.ofFn).reverse++pending) (List.ofFn (0 : Fin p→ℤ)))
      (queryRows o (maxRowQ rows)) (nextMax z pending (List.ofFn (SignQueries.run o (maxRowQ rows)))) := by
  induction rows generalizing pending with
  | nil => exact .stop _
  | cons a rows ih =>
    let best := SignQueries.run o (maxRowQ rows)
    have first := ih (List.ofFn a :: pending)
    have last := max_one O o h z pending a best
    simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append,
      maxRowQ,queryRows_bind,queryRows_ask,queryRows_done,SignQueries.run_bind,SignQueries.run,best] using first.append last

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

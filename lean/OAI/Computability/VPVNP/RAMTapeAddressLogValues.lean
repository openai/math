import OAI.Computability.VPVNP.RAMTapeAddressLogControl

/-!
# Scanning a value during an addressed load

Each saved query bit controls one iteration of the value scan. The loop
restores the query while saving the value for the later log rewind. On a
match, it also saves the result for delivery in its original bit order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AddressLog

local macro "value_step" : tactic => `(tactic|
  first | refine StackRuns.cons (stepPop _ rfl) ?_
        | refine StackRuns.cons (stepPush _ rfl) ?_)

/-- The matched branch uses five instructions per bit. A miss omits the
push to the result stack and uses four. The final empty test selects the
next record on a miss and starts the log rewind on a match. -/
theorem valueRuns (hit : Bool) (qbits vbits tail : List Bool) (s : Bank)
    (len : qbits.length = vbits.length) :
    StackRuns loadCode ((if hit then 5 else 4) * qbits.length + 1) (.value hit)
      ({s with sq := qbits, vs := vbits ++ tail} : Bank).stacks
      (if hit then .rewind .keys else .record)
      ({s with
          sq := [], vs := tail, q := qbits.reverse ++ s.q, sv := vbits.reverse ++ s.sv,
          so := if hit then vbits.reverse ++ s.so else s.so} : Bank).stacks := by
  induction qbits generalizing s vbits with
  | nil =>
    have hv : vbits = [] := List.length_eq_zero_iff.mp len.symm
    subst vbits
    cases hit <;> simp only [↓reduceIte, Bool.false_eq_true, List.length_nil, Nat.mul_zero,
      Nat.zero_add, List.reverse_nil, List.nil_append] <;> value_step <;> exact .nil ..
  | cons b qs ih =>
    cases vbits with
    | nil => simp at len
    | cons v vs =>
      have hlen : qs.length = vs.length := by simpa using len
      cases hit
      · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.mul_succ]
        value_step
        value_step
        value_step
        value_step
        simpa [Bank.set, Bank.stacks, List.append_assoc] using
          ih vs {s with q := b :: s.q, sv := v :: s.sv} hlen
      · simp only [↓reduceIte, List.length_cons, Nat.mul_succ]
        value_step
        value_step
        value_step
        value_step
        value_step
        simpa [Bank.set, Bank.stacks, List.append_assoc] using
          ih vs {s with q := b :: s.q, sv := v :: s.sv, so := v :: s.so} hlen

end RAMTape.AddressLog

end VPVNP
end Computability
end OAI

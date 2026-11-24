import OAI.Computability.VPVNP.RAMTapeDivisionCore

/-!
# Forward scan of a restoring division step

The control holds the next shifted candidate bit in `prev`. For each low
position it saves the divisor, candidate and difference bits. At the high
position it subtracts the zero extension of the divisor to obtain the final
borrow. Only the low positions occupy the three scratch stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.DivisionStack

private theorem forwardBit (feed q d r saved orig diff : List Bool) (c prev a b : Bool) :
    Run 5 (.forward c prev) ⟨[], feed, a :: d, b :: r, q, saved, orig, diff⟩
      (.forward (subBit c prev a).2 b)
      ⟨[], feed, d, r, q, a :: saved, prev :: orig, (subBit c prev a).1 :: diff⟩ := by
  apply prepend (by rfl)
  apply prepend (by rfl)
  apply prepend (by rfl)
  apply prepend (by rfl)
  apply prepend (by rfl)
  exact .nil ..

private theorem forwardAux (feed q d r saved orig diff : List Bool)
    (c prev : Bool) (hlen : r.length = d.length) :
    let candidate := prev :: r
    let trial := subScan c candidate (d ++ [false])
    Run (5 * d.length + 1) (.forward c prev) ⟨[], feed, d, r, q, saved, orig, diff⟩
      (.restore trial.2)
      ⟨[], feed, [], [], q, d.reverse ++ saved, (candidate.take d.length).reverse ++ orig,
        (trial.1.take d.length).reverse ++ diff⟩ := by
  induction d generalizing r c prev saved orig diff with
  | nil =>
    have hr : r = [] := List.length_eq_zero_iff.mp hlen
    subst r
    apply prepend (by rfl)
    exact .nil ..
  | cons a d ih =>
    cases r with
    | nil => simp at hlen
    | cons b r =>
      have tail := ih r (a :: saved) (prev :: orig) ((subBit c prev a).1 :: diff)
        (subBit c prev a).2 b (Nat.succ.inj hlen)
      have run := (forwardBit feed q d r saved orig diff c prev a b).trans tail
      dsimp only at run ⊢
      simpa only [List.length_cons, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm, List.cons_append, subScan, scan, List.take_succ_cons, List.reverse_cons,
        List.append_assoc, List.nil_append] using run

/-- A full forward pass saves the three reversed low words and branches on
the same final borrow as subtraction of the zero-extended divisor. -/
theorem forwardRun (feed q d r : List Bool) (b : Bool) (hlen : r.length = d.length) :
    let cand := b :: r
    let tr := subScan false cand (d ++ [false])
    Run (5 * d.length + 1) (.forward false b) ⟨[], feed, d, r, q, [], [], []⟩
      (.restore tr.2)
      ⟨[], feed, [], [], q, d.reverse, (cand.take d.length).reverse, (tr.1.take d.length).reverse⟩ := by
  simpa only [List.append_nil] using forwardAux feed q d r [] [] [] false b hlen

end TapeWord.DivisionStack

end VPVNP
end Computability
end OAI

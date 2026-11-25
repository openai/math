import OAI.Computability.BorderVNP.RoutingISARuns

/-! # Joining nonempty instruction blocks

Splitting a block at an interior boundary preserves its instruction count and
the full event trace, register bank and memory of each successful execution.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Normal execution of a sequence splits at the state reached by the first statement. -/
theorem Runs.seq_iff {a b : Code} {s m es t mt} :
    Runs pub macros (.seq a b) s m es t mt ↔
      ∃ u mu fs gs, es = fs ++ gs ∧ Runs pub macros a s m fs u mu ∧
        Runs pub macros b u mu gs t mt := by
  constructor
  · intro run
    cases run with
    | atom ha _ _ => cases ha
    | seq first second => exact ⟨_, _, _, _, rfl, first, second⟩
  · rintro ⟨_, _, _, _, rfl, first, second⟩
    exact first.seq second

private theorem seq_assoc {a b c : Code} {s m es t mt} :
    Runs pub macros (.seq a (.seq b c)) s m es t mt ↔
      Runs pub macros (.seq (.seq a b) c) s m es t mt := by
  constructor
  · intro run
    obtain ⟨_, _, _, _, rfl, first, tail⟩ := Runs.seq_iff.mp run
    obtain ⟨_, _, _, _, rfl, mid, last⟩ := Runs.seq_iff.mp tail
    simpa only [List.append_assoc] using (first.seq mid).seq last
  · intro run
    obtain ⟨_, _, _, _, rfl, head, last⟩ := Runs.seq_iff.mp run
    obtain ⟨_, _, _, _, rfl, first, mid⟩ := Runs.seq_iff.mp head
    simpa only [List.append_assoc] using first.seq (mid.seq last)

/-- Running concatenated nonempty blocks is equivalent to sequencing their executions. -/
theorem Runs.block_append_iff {a b : List Code} (ha : a ≠ []) (hb : b ≠ [])
    {s m es t mt} :
    Runs pub macros (.block (a ++ b)) s m es t mt ↔
      Runs pub macros (.seq (.block a) (.block b)) s m es t mt := by
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb
  induction a generalizing s m es t mt with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      change Runs _ _ (.seq x (.block ((y :: ys) ++ (z :: zs)))) _ _ _ _ _ ↔
        Runs _ _ (.seq (.seq x (.block (y :: ys))) (.block (z :: zs))) _ _ _ _ _
      rw [← seq_assoc]
      simp only [Runs.seq_iff, ih (List.cons_ne_nil _ _)]

/-- The split of a nonempty instruction block introduces no additional opcode slot. -/
theorem Code.slots_block_append {a b : List Code} (ha : a ≠ []) (hb : b ≠ []) :
    (Code.block (a ++ b)).slots = (Code.block a).slots + (Code.block b).slots := by
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb
  induction a with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      change x.slots + (Code.block ((y :: ys) ++ (z :: zs))).slots =
        x.slots + (Code.block (y :: ys)).slots + (Code.block (z :: zs)).slots
      rw [ih (List.cons_ne_nil _ _), Nat.add_assoc]

end RoutingISA

end BorderVNP
end Computability
end OAI

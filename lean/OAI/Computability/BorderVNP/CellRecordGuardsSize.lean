import OAI.Computability.BorderVNP.CellRecordGuardsDepth
import OAI.Computability.BorderVNP.CellProfileCompact

/-! # Size of the public generator for all sparse record guards

The generator syntax lists each descriptor once. Scratch flags, copy loops
and lane loops affect the sizes of binary fields without replicating the
descriptor in the public stream.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Static nodes needed to add two scoped scratch-management loops. -/
theorem mass_localFlags (len : ℕ) (s : Stmt) : (localFlags len s).mass = 12 + s.mass := by
  simp [localFlags, Stmt.mass, NatExpr.mass]; omega

/-- A public record's static description bound. The numerical copy and lane
multiplicities affect only the binary fields in the emitted command. -/
def Record.guardMassBound : Record → ℕ
  | .profile _ _ w hist routes => 12 + 10000*(w+1)*(hist.length+routes.length+1)
  | _ => 1024

/-- A record's generator uses only the bounded static template above. -/
theorem recordGuard_mass_le (boxes : List (List Factor)) (r : Record) :
    (recordGuard boxes r).mass ≤ r.guardMassBound := by
  cases r with
  | zero c l p =>
    let t := (Term.wire (p.expr (.index 1) (.index 0))).not
    have h := t.guard_mass_le
    change 2+(2+t.guard.mass) ≤ 1024
    have ht : t.mass = 11 := rfl
    omega
  | equal c l p q =>
    let t := (Term.wire (p.expr (.index 1) (.index 0))).equal (.wire (q.expr (.index 1) (.index 0)))
    have h := t.guard_mass_le
    change 2+(2+t.guard.mass) ≤ 1024
    have ht : t.mass = 45 := rfl
    omega
  | profile c p w hist routes =>
    rw [recordGuard, profileRow, mass_localFlags]
    exact Nat.add_le_add_left (Profile.profileGen_mass_le ..) _
  | box id base copies stride =>
    change 3 ≤ 1024
    decide

/-- The serialized descriptor stream is linear in the total number of static
record nodes times the binary digit length of the largest numeric field. -/
theorem Directory.recordGuards_code_le (D : Directory) :
    D.recordGuards.code.length ≤
      (D.records.length + (D.records.map Record.guardMassBound).sum + 1) *
        (2*D.recordGuards.field.size+10) := by
  apply (Stmt.code_length_le _).trans
  apply Nat.mul_le_mul_right
  rw [Directory.recordGuards, mass_sequence, List.length_map, List.map_map]
  have h (rs : List Record) :
      (rs.map (Stmt.mass ∘ recordGuard D.boxes)).sum ≤ (rs.map Record.guardMassBound).sum := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      exact Nat.add_le_add (recordGuard_mass_le D.boxes r) ih
  exact Nat.add_le_add_right (Nat.add_le_add_left (h D.records) _) _

end CellSparse

end BorderVNP
end Computability
end OAI

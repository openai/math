import OAI.Computability.BorderVNP.CellRecordGuardsBudget
import OAI.Computability.BorderVNP.CellRecordGuardsSize
import OAI.Computability.BorderVNP.CellProfileBinarySize

/-! # Static syntax of the public wiring records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Nodes for the public wiring and profile rows, counting each static row once. -/
def Directory.recordMass (D : Directory) : ℕ :=
  D.records.length + (D.records.map Record.guardMassBound).sum + 1

/-- The numeric iteration counts do not multiply the syntax of a wiring row. -/
theorem Directory.recordGuards_mass_le (D : Directory) : D.recordGuards.mass ≤ D.recordMass := by
  rw [recordGuards, mass_sequence, List.length_map, List.map_map]
  have h (rs : List Record) :
      (rs.map (Stmt.mass ∘ recordGuard D.boxes)).sum ≤ (rs.map Record.guardMassBound).sum := by
    induction rs with
    | nil => rfl
    | cons r rs ih => exact Nat.add_le_add (recordGuard_mass_le D.boxes r) ih
  exact Nat.add_le_add_right (Nat.add_le_add_left (h _) _) _

/-- Scoping temporary guesses adds only the count of allocated flags to the numeric fields. -/
theorem field_localFlags (len : ℕ) (s : Stmt) :
    (localFlags len s).field = max len s.field := by
  simp [localFlags, Stmt.field, NatExpr.field, max_comm]

private theorem portFields {M B : ℕ} {p : Port} (hp : Profile.PortBound M p)
    (hM : M ≤ B) (hB : 1 ≤ B) : (p.expr (.index 1) (.index 0)).field ≤ B := by
  rcases hp with ⟨hb,hc,hl⟩
  simp only [Port.expr, NatExpr.field, max_le_iff]
  omega

/-- The largest wiring literal comes either from a bounded public port or from the
locally allocated prefix rectangle for a histogram. -/
theorem recordGuard_field_le (boxes : List (List Factor)) (r : Record) {M : ℕ}
    (hr : r.GuardBound M) : (recordGuard boxes r).field ≤ 100*(M+2)^3+1 := by
  let B := 100*(M+2)^3+1
  have hB : M+10 ≤ B := by dsimp [B]; nlinarith [Nat.zero_le (M^2), Nat.zero_le (M^3)]
  change _ ≤ B
  cases r with
  | zero c l p =>
    obtain ⟨hc,hl,hp⟩ := hr
    apply max_le (hc.trans (by omega)) (max_le (hl.trans (by omega)) (Term.guard_field_le _ ?_ ?_))
    · exact portFields hp (by omega) (by omega)
    · change 2 ≤ B; omega
  | equal c l p q =>
    obtain ⟨hc,hl,hp,hq⟩ := hr
    apply max_le (hc.trans (by omega)) (max_le (hl.trans (by omega)) (Term.guard_field_le _ ?_ ?_))
    · rw [Term.fields_equal]
      exact ⟨portFields hp (by omega) (by omega), portFields hq (by omega) (by omega)⟩
    · change 9 ≤ B; omega
  | box id base c stride => exact Nat.zero_le _
  | profile c p w hist routes =>
    obtain ⟨hc,hw,hh,_,hs,hr⟩ := hr
    have hn : Profile.auxSize c hist.length ≤ (M+1)^3 := by
      change hist.length*((c+1)*(c+1)) ≤ _
      calc
        _ ≤ (M+1)*((M+1)*(M+1)) := by gcongr; omega
        _ = _ := by ring
    rw [recordGuard,profileRow,field_localFlags]
    apply max_le (hn.trans ?_) (Profile.profileGen_field_le (Nat.zero_le _) hn hc hw hh hs hr)
    nlinarith [Nat.zero_le (M^2), Nat.zero_le (M^3)]

/-- All wiring rows obey a common cubic literal bound. -/
theorem Directory.recordGuards_field_le (D : Directory) {M : ℕ} (h : ∀ r ∈ D.records, r.GuardBound M) :
    D.recordGuards.field ≤ 100*(M+2)^3+1 := by
  apply field_sequence_le
  intro s hs
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hs
  exact recordGuard_field_le _ _ (h _ hr)

end CellSparse

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.TransmissionReadback
import OAI.Computability.BorderVNP.TransmissionProgram

/-! # Final consumer words after all transmission rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- The bank at a bit offset of the selected row, with its cursor in register 16. -/
def Range.bitBank (r : Range w) (team : Word w) (j : ℕ) : Bank w :=
  Function.update (r.bank team) 16 (Fin.ofNat _ j)

/-- Memory just before the bit handler reads its source, after all preceding rows
and the already processed slots of the current row. -/
def bitMemory (rows : ℕ → Range w) (team : Word w) (pub : Arg → Word w) (m : Memory w)
    (bits : ℕ → ℕ → Bool) (i : ℕ) (mode : Role) (j : ℕ) : Memory w :=
  rangeMemory mode pub ((rows i).bank team) (tableMemory rows team pub m bits i) (bits i) j

/-- A bit is the last physical writer of one consumer address in a table prefix. -/
structure LastWrite (rows : ℕ → Range w) (team : Word w) (count i : ℕ)
    (mode : Role) (j a : ℕ) : Prop where
  /-- The nominated writer belongs to the executed prefix. -/
  row_lt : i < count
  /-- The nominated offset is processed by its row. -/
  slot_lt : j < (rows i).width.val
  /-- The nominated role is the one selected on the executing team. -/
  selected : (rows i).selected team = some (some mode)
  /-- The nominated handler writes this address. -/
  hit : mode.writes ((rows i).bitBank team j) a
  /-- Later offsets of this row leave the address alone. -/
  laterBits : ∀ k, j < k → k < (rows i).width.val → ¬mode.writes ((rows i).bitBank team k) a
  /-- No selected role in any remaining row writes the address. -/
  laterRows : ∀ later, i < later → later < count → ∀ nextMode,
    (rows later).selected team = some (some nextMode) → ∀ k < (rows later).width.val,
      ¬nextMode.writes ((rows later).bitBank team k) a

private theorem row_preserves (r : Range w) (team : Word w) (pub : Arg → Word w)
    (m : Memory w) (bits : ℕ → Bool) (a : ℕ)
    (apart : ∀ mode, r.selected team = some (some mode) → ∀ j < r.width.val,
      ¬mode.writes (r.bitBank team j) a) : r.apply team pub m bits a = m a := by
  unfold Range.apply
  cases sel : r.selected team with
  | none => rfl
  | some role =>
    cases role with
    | none => rfl
    | some mode =>
      have keep (k : ℕ) (hk : k ≤ r.width.val) : rangeMemory mode pub (r.bank team) m bits k a = m a := by
        induction k with
        | zero => rfl
        | succ k ih =>
          have miss := apart mode sel k hk
          unfold Range.bitBank at miss
          rw [rangeMemory,Role.output_at,ite_eq_right miss]
          exact ih (Nat.le_of_succ_le hk)
      exact keep r.width.val le_rfl

/-- The final consumer word equals the payload read by its last writer from the
true intermediate memory of that physical row and bit. -/
theorem LastWrite.readback {rows : ℕ → Range w} {team : Word w} {count i : ℕ}
    {mode : Role} {j a : ℕ} (h : LastWrite rows team count i mode j a) (pub : Arg → Word w)
    (m : Memory w) (bits : ℕ → ℕ → Bool) :
    tableMemory rows team pub m bits count a =
      mode.payload pub ((rows i).bitBank team j) (bitMemory rows team pub m bits i mode j) (bits i j) := by
  have after (t : ℕ) (ht : i < t) (endAt : t ≤ count) :
      tableMemory rows team pub m bits t a =
        mode.payload pub ((rows i).bitBank team j) (bitMemory rows team pub m bits i mode j) (bits i j) := by
    induction t with
    | zero => omega
    | succ k ih =>
      rw [tableMemory]
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with earlier | rfl
      · rw [row_preserves (rows k) team pub _ (bits k) a (h.laterRows k earlier endAt)]
        exact ih earlier (Nat.le_of_succ_le endAt)
      · exact (rows i).readback team pub _ _ h.selected h.slot_lt h.hit h.laterBits
  exact after count h.row_lt le_rfl

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI

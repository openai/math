import OAI.Computability.VPVNP.RAMProcessorLocalResult

/-!
# Bounds and emitted events of a private segment

A returned segment has no internal probe records. Every terminal or external
instruction consumes a fuel unit. The remaining fuel also bounds the total
growth of the private log when several segments are executed in one call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.LocalProcessor

open BurstRAM PrivateRAM

variable {w p r k : ℕ}

/-- Callbacks that return control from the private scan to the site processor, namely external
reads or writes, state returns, acceptance and rejection. -/
def externalOrTerminal : ISA.Callback p r → Prop
  | .next _ | .choose _ _ => False
  | _ => True

theorem scan_bounds (T : Template p r k) (pub : Fin k → Word w) (f : ℕ)
    (c : LogConfig w p r) (bs : List Bool) :
    let y := scan T pub f c bs
    y.fuel ≤ f ∧ (y.exit ≠ .reject → y.fuel < f) ∧ externalOrTerminal y.exit ∧
      y.cfg.writes.length + y.fuel ≤ c.writes.length + f ∧
      (∀ start ord, eventRecords start ord y.prefixEvents = []) := by
  induction f generalizing c bs with
  | zero => simp [scan, eventRecords, externalOrTerminal]
  | succ f ih =>
    let out := instructionPost T pub c
    have hg : out.writes.length ≤ c.writes.length + 1 := ISA.post_writes_length_le ..
    dsimp only
    rw [scan]
    cases h : instructionExit T c with
    | next j =>
      obtain ⟨hf, _, he, hl, hrec⟩ := ih {out with pc := j} bs
      simp only [Yield.prepend, eventRecords]
      dsimp only [out] at hf hl hg ⊢
      exact ⟨by omega, fun _ => by omega, he, by omega, hrec⟩
    | choose yes no =>
      cases bs with
      | nil => dsimp only; exact ⟨by omega, fun _ => by omega, trivial, by change out.writes.length+f ≤ _; omega, fun _ _ => rfl⟩
      | cons b bs =>
        obtain ⟨hf, _, he, hl, hrec⟩ := ih {out with pc := if b then yes else no} bs
        simp only [Yield.prepend, eventRecords]
        dsimp only [out] at hf hl hg ⊢
        exact ⟨by omega, fun _ => by omega, he, by omega, hrec⟩
    | read _ _ _ | write _ _ _ | accept | returnState _ | reject =>
      dsimp only
      exact ⟨by omega, fun _ => by omega, trivial, by change out.writes.length+f ≤ _; omega, fun _ _ => rfl⟩

theorem scan_fuel_lt (T : Template p r k) (pub : Fin k → Word w) (f : ℕ)
    (c : LogConfig w p r) (bs : List Bool) (h : (scan T pub f c bs).exit ≠ .reject) :
    (scan T pub f c bs).fuel < f := (scan_bounds ..).2.1 h

theorem scan_writes_le (T : Template p r k) (pub : Fin k → Word w) (f : ℕ)
    (c : LogConfig w p r) (bs : List Bool) :
    let y := scan T pub f c bs
    y.cfg.writes.length + y.fuel ≤ c.writes.length + f := (scan_bounds ..).2.2.2.1

theorem scan_no_probes (T : Template p r k) (pub : Fin k → Word w) (f : ℕ)
    (c : LogConfig w p r) (bs : List Bool) (start ord : ℕ) :
    eventRecords start ord (scan T pub f c bs).prefixEvents = [] := (scan_bounds ..).2.2.2.2 start ord

end RAMTape.LocalProcessor

end VPVNP
end Computability
end OAI

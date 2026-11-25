import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Return and rejection contracts for the two native compressor procedures -/

namespace ThreeFlat.RAM.TickStageSpec

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
variable {F : Type*} [Semiring F] {w n nr k p r K : ℕ}

/-- An accepted raw stage record deterministically returns to the supplied
continuation with the verified memory relation. A rejected bitstring has
zero total field weight, independently of the following code or extra fuel. -/
def Admission (field : FieldCode F w) (b : Block w n nr k) (baseline : Fin k → Word w)
    (pre : Memory w → Prop) (ok : Memory w → Prop) (post : Memory w → Memory w → Prop)
    (budget : ℕ) : Prop :=
  ∀ {p r K : ℕ} (M : Machine w p r K) (P : Fin n ↪ Fin p) (R : Fin nr ↪ Fin r)
    (pub : Fin k → Fin K) (exit : Fin p), b.Installed M P R pub exit →
    (∀ i, M.publicData (pub i) = baseline i) →
    ∀ (c : Config w p r) (mem : Memory w), c.pc = P b.first → pre mem →
      (ok mem → ∃ t ≤ budget, ∃ d : Config w p r, ∃ out : Memory w,
        d.pc = exit ∧ post mem out ∧ advance M.program t c mem = some (d,out)) ∧
      (¬ok mem → ∀ extra, mass field M.program (extra+budget) c mem = 0)

/-- A selected-cell procedure has a deterministic continuation under its
validated navigation input. Root ownership, compact metadata, and the
unchanged raw pins/hidden frame are expressed together in its postcondition. -/
def Prepare (b : Block w n nr k) (baseline : Fin k → Word w)
    (pre : Memory w → Prop) (post : Memory w → Memory w → Prop) (budget : ℕ) : Prop :=
  ∀ {p r K : ℕ} (M : Machine w p r K) (P : Fin n ↪ Fin p) (R : Fin nr ↪ Fin r)
    (pub : Fin k → Fin K) (exit : Fin p), b.Installed M P R pub exit →
    (∀ i, M.publicData (pub i) = baseline i) →
    ∀ (c : Config w p r) (mem : Memory w), c.pc = P b.first → pre mem →
      ∃ t ≤ budget, ∃ d : Config w p r, ∃ out : Memory w,
        d.pc = exit ∧ post mem out ∧ advance M.program t c mem = some (d,out)

theorem admission_mass (field : FieldCode F w) (b : Block w n nr k) (data : Fin k → Word w)
    (pre ok : Memory w → Prop) (post : Memory w → Memory w → Prop) (budget : ℕ)
    (spec : Admission field b data pre ok post budget) (M : Machine w p r K)
    (P : Fin n ↪ Fin p) (R : Fin nr ↪ Fin r) (pub : Fin k → Fin K) (exit : Fin p)
    (rom : b.Installed M P R pub exit) (params : ∀ i, M.publicData (pub i) = data i)
    (c : Config w p r) (mem : Memory w) (start : c.pc = P b.first) (hp : pre mem) :
    (ok mem → ∃ t ≤ budget, ∃ d : Config w p r, ∃ out : Memory w,
      d.pc = exit ∧ post mem out ∧ ∀ extra,
        mass field M.program (extra+t) c mem = mass field M.program extra d out) ∧
      (¬ok mem → ∀ extra, mass field M.program (extra+budget) c mem = 0) := by
  obtain ⟨accept,reject⟩ := spec M P R pub exit rom params c mem start hp
  refine ⟨?_,reject⟩
  intro hx
  obtain ⟨t,limit,d,out,pc,rel,run⟩ := accept hx
  exact ⟨t,limit,d,out,pc,rel,mass_of_advance field M.program run⟩

end ThreeFlat.RAM.TickStageSpec

end OAI

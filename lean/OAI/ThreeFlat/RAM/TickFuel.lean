import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Accumulating certified native phase bounds at a single common fuel -/

namespace ThreeFlat.RAM.TickFuel
open Computability.VPVNP.BurstRAM PrivateRAM

variable {F C : Type*} [Semiring F] {w : ℕ} {field : FieldCode F w} {P : Program w C}
    {a b : C} {mem out : Memory w} {t cap cap' : ℕ} {v : F}

def Returns (field : FieldCode F w) (P : Program w C) (cap : ℕ) (a : C) (m : Memory w) (v : F) : Prop :=
  ∀ extra, mass field P (extra+cap) a m = v

theorem Returns.later (run : Returns field P cap a mem v) (bound : cap ≤ cap') :
    Returns field P cap' a mem v := by
  intro extra
  simpa only [show extra+(cap'-cap)+cap = extra+cap' by omega] using run (extra+(cap'-cap))

theorem Returns.prefix (step : advance P t a mem = some (b,out)) (run : Returns field P cap b out v) :
    Returns field P (t+cap) a mem v := by
  intro extra
  rw [show extra+(t+cap) = (extra+cap)+t by omega, mass_of_advance field P step]
  exact run extra

theorem Returns.guard (valid : Prop) [Decidable valid]
    (step : ∀ f, mass field P (f+t) a mem =
      if valid then mass field P f b out else 0)
    (run : Returns field P cap b out v) :
    Returns field P (t+cap) a mem (if valid then v else 0) := by
  intro extra
  rw [show extra+(t+cap) = (extra+cap)+t by omega,step,run]

theorem accept {p r k : ℕ} (M : Machine w p r k) (c : Config w p r) (m : Memory w)
    (rom : M.code c.pc = .accept) : Returns field M.program 1 c m 1 := by
  intro extra
  simp [mass,Machine.program,rom,Instr.run,FieldCode.terminal]

end ThreeFlat.RAM.TickFuel

end OAI

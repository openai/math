import OAI.ThreeFlat.RAM.TickControlHeader

namespace OAI
/-! # Native branch selection from the physically supplied auxiliary endpoints -/

namespace ThreeFlat.RAM.TickMarkerSwitch

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickChronology

variable {w p r k : ℕ}

def emitOn (P : Fin 4 → Fin p) (R : Fin 2 → Fin r) (marker expected : Word w)
    (identity history : Fin p) : Fin 4 → Instr w p r k
  | 0 => .constant (R 0) marker (P 1)
  | 1 => .readExternal (R 1) (R 0) (P 2)
  | 2 => .constant (R 0) expected (P 3)
  | _ => .jumpEq (R 1) (R 0) identity history

/-- Four rows read the physical branch bit. Values held in every caller register
outside the two selector temporaries survive the choice. -/
theorem advance_on (M : Machine w p r k) (P : Fin 4 → Fin p) (R : Fin 2 ↪ Fin r)
    (marker expected : Word w) (identity history : Fin p)
    (installed : ∀ i, M.code (P i) = emitOn P R marker expected identity history i)
    (c : Config w p r) (m : Memory w) (entry : c.pc = P 0) :
    ∃ d : Config w p r, d.pc = (if m marker.val = expected then identity else history) ∧
      (∀ j, (∀ i, j ≠ R i) → d.reg j = c.reg j) ∧
      d.persistent = c.persistent ∧ d.privateMem = c.privateMem ∧
      advance M.program 4 c m = some (d,m) := by
  let endPC := if m marker.val = expected then identity else history
  let x := (((c.put (P 1) (R 0) marker).put (P 2) (R 1) (m marker.val)).put (P 3) (R 0) expected)
  refine ⟨{ x with pc := endPC },rfl,?_,rfl,rfl,?_⟩
  · intro j hj
    simp [x,Config.put,Function.update,hj]
  · by_cases h : m marker.val = expected <;>
      simp [advance,Machine.program,entry,installed,emitOn,Instr.run,Config.put,Function.update,
        R.injective.eq_iff,x,endPC,h]

def emit (P : Fin 4 → Fin p) (R : Fin 2 → Fin r) (marker : Word w)
    (identity history : Fin p) := emitOn (k:=k) P R marker 0 identity history

/-- Four rows read the physical branch bit. Values held in every caller register
outside the two selector temporaries survive the choice. -/
theorem advance_switch (M : Machine w p r k) (P : Fin 4 → Fin p) (R : Fin 2 ↪ Fin r)
    (marker : Word w) (identity history : Fin p)
    (installed : ∀ i, M.code (P i) = emit P R marker identity history i)
    (c : Config w p r) (m : Memory w) (entry : c.pc = P 0) :
    ∃ d : Config w p r, d.pc = (if m marker.val = 0 then identity else history) ∧
      (∀ j, (∀ i, j ≠ R i) → d.reg j = c.reg j) ∧
      d.persistent = c.persistent ∧ d.privateMem = c.privateMem ∧
      advance M.program 4 c m = some (d,m) :=
  advance_on M P R marker 0 identity history installed c m entry

end ThreeFlat.RAM.TickMarkerSwitch

end OAI

import OAI.Computability.NearSquareRoot.InterchangeROMBankRulersRun
import OAI.Computability.NearSquareRoot.InterchangeROMBankRulersPrepare
import OAI.Computability.NearSquareRoot.InterchangeROMBankRulersCount

/-! # A fixed physical header command for the packed interchange center -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBankRulers

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims NearSquareRoot.InterchangeROMExpose NearSquareRoot.Space

abbrev input (i : Input) (W : ℕ) : Raw := ((tally W,tally i.b,tally i.n),centerHeader i)

abbrev bankHeader (i : Input) (W : ℕ) : InterchangeROMAddress.Header :=
  InterchangeROMAddress.header (f i) (i.req.before ++ [BatchRows.groups i.b W])
    (centerGap i) (centerSuffix i)

abbrev cutTriple (i : Input) (m : ℕ) := (tally (prefixFactor i),tally m,tally (tailFactor i))

abbrev output (i : Input) (W : ℕ) : Triples :=
  (cutTriple i i.b,cutTriple i (BatchRows.groups i.b W),bankHeader i W)

def work (d : ℕ) (i : Input) (W : ℕ) := i.req.rows.count + (size (input i W)+1)^d

private def rulers (i : Input) (W : ℕ) : Rulers :=
  ⟨i.req.before, tailFactors i, prefix_solid i, tailFactors_solid i,
    tally i.b,tally (BatchRows.groups i.b W),bankHeader i W⟩

/-- One program works for every physically supplied template and center, and
pays a polynomial only on their compact descriptor. -/
theorem bounded : ∃ d : ℕ, BoundedTask
    (fun z : Input × ℕ => work d z.1 z.2) (fun z => work d z.1 z.2)
    (fun z => send (input z.1 z.2)) (fun z => send (output z.1 z.2)) :=
  prepared_bounded (fun (z : Input × ℕ) => input z.1 z.2) (fun z => rulers z.1 z.2)
    (fun z => z.1.req.rows.count) prepare prepare_poly (fun z => prepare_center z.1 z.2)
    (fun z => prefixFactor_le z.1) (fun z => tailFactor_le z.1)

noncomputable def command : Cmd := bounded.choose_spec.choose

theorem command_fits : ∃ C d : ℕ, ∀ (i : Input) (W : ℕ) env deck base, DeckCap base deck →
    BoundedFits env command (pile 0 (send (input i W)) deck)
      (pile 0 (send (output i W)) deck) (C*(work d i W+1)) (base+C*(work d i W+1))
      (C*(work d i W+1)) := by
  obtain ⟨C,hr⟩ := bounded.choose_spec.choose_spec
  exact ⟨C,bounded.choose,fun i W => hr (i,W)⟩

end InterchangeROMBankRulers

end NearSquareRoot
end Computability
end OAI

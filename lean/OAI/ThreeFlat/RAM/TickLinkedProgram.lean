import OAI.ThreeFlat.RAM.TickTextBudget
import OAI.ThreeFlat.RAM.TickPublicData

namespace OAI
/-! # Installing both native procedures in one age-uniform RAM text -/

noncomputable section
namespace ThreeFlat.RAM.TickMachine
open Computability.VPVNP.BurstRAM PrivateRAM TickActiveROM ContinuationLink Contraction BitLayout HistoryFactors
open scoped Fin.CommRing

variable {F : Type*} [Field F] [Fintype F] {w p H J np sp nr sr nk sk u : ℕ}

/-- This cutoff depends only on the fixed ROM sizes of the two procedures and the field. -/
def textCutoff (F : Type*) [Fintype F] (np sp nr sr nk sk : ℕ) :=
  max (3400+9*(Fintype.card F*Fintype.card F)+np+sp)
    (max (400+3*(Fintype.card F*Fintype.card F)+nr+sr) (TickPublicData.count nk sk))

omit [Field F] in
theorem fits_text (large : textCutoff F np sp nr sr nk sk ≤ u) :
    3400+9*(Fintype.card F*Fintype.card F)+np+sp ≤ u ∧
    400+3*(Fintype.card F*Fintype.card F)+nr+sr ≤ u ∧ TickPublicData.count nk sk ≤ u := by
  simpa only [textCutoff,max_le_iff] using large

variable (A : Layout) (c : Diagonal.TickChronology.Clock) (fit : Fits (TickWeightedBank.shape F p H J) w)
variable (nav : Block w np nr nk) (prep : Block w sp sr sk)
variable (nd : Fin nk → Word w) (sd : Fin sk → Word w)

def linkedData (q nt ns : ℕ) : Fin (TickPublicData.count nk sk) → Word w :=
  TickPublicData.data q nt ns (interpreter p H J A.metadata A.lut (F:=F) fit).publicData nd sd

/-- The real label table and public ROM of the tick, with both independent
procedures placed in disjoint operand banks. Register allocation uses the
age's public bound directly. -/
def linkedProgram (large : textCutoff F np sp nr sr nk sk ≤ u) (q nt ns : ℕ) :
    Machine w (Fintype.card (All (n:=np) (m:=sp) (k:=TickPublicData.count nk sk) A c fit)) u
      (TickPublicData.count nk sk) :=
  let size := fits_text large
  program A c fit (frontRegisters c (by have := size.2.1; omega)) (registers A c fit size.2.1)
    (TickPublicData.keys nk sk) (linkedData A fit nd sd q nt ns) (TickPublicData.evaluator nk sk)
    (nav.reindex (Function.Embedding.refl _) (TickPublicData.navigator nk sk))
    (prep.reindex (Function.Embedding.refl _) (TickPublicData.preparer nk sk))

theorem linkedProgram_fits (large : textCutoff F np sp nr sr nk sk ≤ u) :
    Fintype.card (All (n:=np) (m:=sp) (k:=TickPublicData.count nk sk) A c fit) ≤ u ∧
    TickPublicData.count nk sk ≤ u :=
  ⟨(text_count A c fit).trans (fits_text large).1,(fits_text large).2.2⟩

end ThreeFlat.RAM.TickMachine

namespace ThreeFlat.RAM.TickMachine

/-- A single constant cutoff covers the original tick ROM and the fixed base-zero
startup procedure, once both physical producer tables have been bounded. -/
theorem shifted_text_room {F : Type*} [Fintype F] {np sp nr sr nk sk navBound prepBound u : ℕ}
    (nav : np+nr+nk≤navBound) (prepare : sp+sr+sk≤prepBound)
    (age : 3437+9*(Fintype.card F*Fintype.card F)+navBound+prepBound≤u) :
    textCutoff F np sp nr sr nk sk≤u ∧
    37+(3400+9*(Fintype.card F*Fintype.card F)+np+sp)≤u ∧ 6+TickPublicData.count nk sk≤u := by
  simp only [textCutoff,max_le_iff,TickPublicData.count]
  omega


end ThreeFlat.RAM.TickMachine

end
end OAI

import OAI.ThreeFlat.RAM.TickActiveROM
import Mathlib.Tactic.FinCases

namespace OAI
/-! # A single physical text for the native age-dependent diagonal tick -/

noncomputable section
namespace ThreeFlat.RAM.TickMachine

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr ContinuationLink Diagonal.TickChronology
open TickActiveROM BitLayout Contraction

variable {F : Type*} [Field F] [Fintype F] {p H J w k n m nr mr r : ℕ}

def selectedRegs {w k : ℕ} {c : Clock} (front : TickFrontROM.Reg w k c ↪ Fin r) : Fin 5 ↪ Fin r :=
  let slots : Fin 5 → TickFrontROM.Reg w k c :=
    ![.inl (.inl 2),.inl (.inr (.inl 2)),.inl (.inr (.inr (.inl 0))),.inr 0,.inr 1]
  (⟨slots,by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all [slots]⟩ :
    Fin 5 ↪ TickFrontROM.Reg w k c).trans front

variable (A : Layout) (c : Clock) (fit : Fits (TickWeightedBank.shape F p H J) w)

abbrev Active := Labels (k:=k) (n:=n) (m:=m) A c fit
abbrev All := TickFrontROM.Labels w k (Fintype.card (Active (n:=n) (m:=m) (k:=k) A c fit)) c

def historyLocation : Active (n:=n) (m:=m) (k:=k) A c fit ↪ Fin (Fintype.card (All (n:=n) (m:=m) (k:=k) A c fit)) :=
  let addr := TickFrontROM.allPC w k (Fintype.card (Active (n:=n) (m:=m) (k:=k) A c fit)) c
  ⟨fun i => TickFrontROM.historyPC addr (Fintype.equivFin _ i),
    fun i j h => by
      apply (Fintype.equivFin _).injective
      simpa only [TickFrontROM.historyPC,addr.injective.eq_iff,Sum.inr.injEq] using h⟩

def historyEntry (ph : Phase) : Fin (Fintype.card (Active (n:=n) (m:=m) (k:=k) A c fit)) :=
  Fintype.equivFin _ (.control (.inl (TickFrontROM.phaseNo ph,0)))

/-- All phase paths begin in the advice/identifier reader. Navigation and
slot preparation are linked relocatable instruction blocks; every other
counter belongs to one of the explicit fixed tables. -/
def program (front : TickFrontROM.Reg w k c ↪ Fin r)
    (registers : Registers A c fit nr mr r k) (keys : TickPrefix.Keys k)
    (data : Fin k → Word w) (evalPublic : Fin 7 → Fin k)
    (nav : Block w n nr k) (prep : Block w m mr k) :
    Machine w (Fintype.card (All (n:=n) (m:=m) (k:=k) A c fit)) r k :=
  let R := {registers with control := selectedRegs front}
  let inside := TickActiveROM.emit A c fit nav prep (historyLocation A c fit) R evalPublic
  TickFrontROM.machine front data keys A.bits A.regions (historyEntry A c fit)
    (fun j => inside ((Fintype.equivFin _).symm j))

theorem program_history (front : TickFrontROM.Reg w k c ↪ Fin r)
    (registers : Registers A c fit nr mr r k) (keys : TickPrefix.Keys k)
    (data : Fin k → Word w) (evalPublic : Fin 7 → Fin k)
    (nav : Block w n nr k) (prep : Block w m mr k) (i : Active (n:=n) (m:=m) (k:=k) A c fit) :
    (program A c fit front registers keys data evalPublic nav prep).code (historyLocation A c fit i) =
      TickActiveROM.emit A c fit nav prep (historyLocation A c fit) {registers with control := selectedRegs front} evalPublic i := by
  let inside := TickActiveROM.emit A c fit nav prep (historyLocation A c fit)
    {registers with control := selectedRegs front} evalPublic
  let numbers := Fintype.equivFin (Active (n:=n) (m:=m) (k:=k) A c fit)
  let history := fun j => inside (numbers.symm j)
  have read := TickFrontROM.installed front data keys A.bits A.regions (historyEntry A c fit)
    history (.inr (.inr (.inr (.inr (numbers i)))))
  refine read.trans ?_
  change inside (numbers.symm (numbers i)) = inside i
  rw [Equiv.symm_apply_apply]


end ThreeFlat.RAM.TickMachine

end
end OAI

import OAI.Hierarchy.ProbeStripMenu
import OAI.Hierarchy.ProtocolRAMVectorROMTable

namespace OAI
/-! # The physical lookup table for a fixed packet menu's selector encoding -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe DiscrepancyROM
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing Classical

namespace MenuROM
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N w : ℕ}
  (menu : Probe.FixedMenu F edge req box ε tree N)

def chargeWord : ℕ→ℕ
  | 0=>0
  | i+1=>if small : i<Fintype.card menu.index
    then (menu.packet ((Fintype.equivFin menu.index).symm ⟨i,small⟩)).selectorBits else 0

theorem chargeWord_le (cap : ℕ) (bound : ∀ i, (menu.packet i).selectorBits ≤ cap) (i : ℕ) :
    chargeWord menu i ≤ cap := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i =>
    rw [chargeWord]
    by_cases small : i < Fintype.card menu.index
    · rw [dite_eq_left small]
      exact bound _
    · rw [dite_eq_right small]
      exact Nat.zero_le _

def selectorCharges (base : ℕ) : Table 1 1 :=
  ⟨base,Fintype.card menu.index+1,fun _ key=>chargeWord menu (key 0).val⟩

theorem charge_lookup (base : ℕ) (m : Memory w) (ready : (selectorCharges menu base).Resident m)
    (j : menu.index) : ((selectorCharges menu base).bank 0).read m
      (((Fintype.equivFin menu.index j).val+1:ℕ):Word w) = ((menu.packet j).selectorBits:Word w) := by
  let a:=Fintype.equivFin menu.index j
  let k : Fin 1→Fin (Fintype.card menu.index+1):=fun _=>⟨a.val+1,Nat.succ_lt_succ a.isLt⟩
  have index : (finFunctionFinEquiv k).val=a.val+1 := by simp [k]
  have decoded : chargeWord menu (a.val+1) = (menu.packet j).selectorBits := by
    rw [chargeWord, dite_eq_left a.isLt]
    exact congrArg (fun i => (menu.packet i).selectorBits) ((Fintype.equivFin menu.index).symm_apply_apply j)
  calc
    _ = ((selectorCharges menu base).bank 0).read m ((finFunctionFinEquiv k).val : Word w) :=
      congrArg (fun n : ℕ => ((selectorCharges menu base).bank 0).read m (n : Word w)) index.symm
    _ = _ := (ready 0 k).trans (congrArg (fun n : ℕ => (n : Word w)) decoded)

structure Charges where
  payload : Table 1 1
  purchase : Table 1 1

def Charges.stop (s : Charges) := s.purchase.stop
def Charges.words (s : Charges) (m : Memory w) := both s.payload s.purchase m
def Charges.Resident (s : Charges) (m : Memory w) := s.payload.Resident m ∧ s.purchase.Resident m

end MenuROM

end Hierarchy.ProtocolRAM.Calendar
end

end OAI

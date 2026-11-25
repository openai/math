import OAI.Hierarchy.ProtocolRAMVectorROMTable

namespace OAI
/-! # Uniform bounds on initialized price ROMs, including the unused cell addresses -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {p D w q : ℕ}

namespace DiscrepancyROM.Table
def Capped (t : Table p D) (q : ℕ) (m : Memory w) : Prop :=
  ∀x,t.base≤x → x<t.stop → (m x).val≤q

theorem capped_words (t : Table p D) (rest : Memory w) (bound : ∀i a,t.word i a≤q) :
    t.Capped q (t.words rest) := by
  intro x lo hi
  have on : t.base≤x ∧ x<t.base+p*t.size := ⟨lo,hi⟩
  simp only [words,fillSegment,ite_eq_left on]
  split
  · split
    · exact (Nat.mod_le _ _).trans (bound _ _)
    · simp
  · simp

theorem Capped.transport {t : Table p D} {m n : Memory w} (h : t.Capped q m)
    (frame : ∀x,t.base≤x→ x<t.stop → n x=m x) : t.Capped q n := by
  intro x lo hi
  rw [frame x lo hi]
  exact h x lo hi

theorem Capped.lookup {t : Table 1 D} {m : Memory w} (h : t.Capped q m) (u : Word w) :
    ((t.bank 0).read m u).val≤q := by
  change (m (t.base+0*t.size+u.val%t.size)).val≤q
  have span : 0<t.size := Nat.zero_lt_of_lt (ProtocolRAMPurchaseSampler.lt_span t.entries)
  have small:=Nat.mod_lt u.val span
  simp only [Nat.zero_mul,Nat.add_zero]
  apply h _ (Nat.le_add_right ..)
  simpa only [stop,Nat.one_mul] using Nat.add_lt_add_left small t.base
end DiscrepancyROM.Table

end Hierarchy.ProtocolRAM.Calendar
end

end OAI

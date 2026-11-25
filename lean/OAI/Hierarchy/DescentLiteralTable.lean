import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Fixed literal banks compiled from their entries -/
namespace Hierarchy.DescentSeedCountCheck
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {w : ℕ}

/-- Emit the fixed words of an immutable lookup table. -/
def literals (base : ℕ) (entry : ℕ→ℕ) : ℕ→List Pass
  | 0=>[]
  | n+1=>⟨base+n,1,.lit (entry n)⟩::literals base entry n

theorem literal_rows (base : ℕ) (v : ℕ→ℕ) (n : ℕ) (m : Memory w) (a : ℕ) :
    result (literals base v n) m a=if base ≤ a ∧ a < base+n then (v (a-base):Word w) else m a := by
  induction n generalizing m with
  | zero=>simp [literals,result,show ¬(base≤a ∧ a<base) by omega]
  | succ n ih=>
    change result (literals base v n) (image (base+n) 1 (.lit (v n)) m) a=_
    rw [ih]
    by_cases h : base ≤ a ∧ a < base+n
    · rw [ite_eq_left h,ite_eq_left (show base ≤ a ∧ a < base+(n+1) by omega)]
    · rw [ite_eq_right h]
      by_cases eq : a=base+n
      · subst a
        simp only [image,fillSegment,ite_eq_left (show base+n ≤ base+n ∧ base+n < base+n+1 by omega),
          Expr.eval,ite_eq_left (show base ≤ base+n ∧ base+n < base+(n+1) by omega),Nat.add_sub_cancel_left]
      · simp only [image,fillSegment,ite_eq_right (show ¬(base+n ≤ a ∧ a < base+n+1) by omega),
          ite_eq_right (show ¬(base ≤ a ∧ a < base+(n+1)) by omega)]

theorem literals_fit (base : ℕ) (v : ℕ→ℕ) (n : ℕ) (fit : base+n < 2^w) :
    ∀ p∈literals base v n,p.Fits w := by
  induction n with
  | zero=>simp [literals]
  | succ n ih=>
    intro p member
    rcases List.mem_cons.mp member with eq|later
    · subst p;exact ⟨trivial,by omega⟩
    · exact ih (by omega) p later

theorem literal_time (base : ℕ) (entry : ℕ→ℕ) (n : ℕ) :
    clock (literals base entry n)=4+10*n := by
  induction n with
  | zero=>rfl
  | succ n ih=>change 10+clock (literals base entry n)=_;rw [ih];omega


end Hierarchy.DescentSeedCountCheck

end OAI

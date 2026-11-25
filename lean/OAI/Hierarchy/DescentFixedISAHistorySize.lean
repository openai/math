import OAI.Hierarchy.DescentFixedISATariff
import OAI.Hierarchy.CheapISAHostClock
import OAI.Hierarchy.CheapISABanks

namespace OAI
/-! # Physical record capacity for the fixed interpreter's expanded image and clock -/

namespace Hierarchy.DescentCompiler

/-- A legal exponent for the selected seven-level sort. The image has one
dyadic padding and the minimum allowed stage width. -/
def terminalHistoryOrder (h records : ℕ) := max (h-1) (Nat.clog 2 records)

theorem terminal_history_order (h records : ℕ) (upper : records≤2^(3*h)) :
    let m:=terminalHistoryOrder h records
    h-1≤ m ∧ m≤3*h ∧ records≤2^m ∧ 2^m≤2*records+1+2^h := by
  have rounded : 2^(Nat.clog 2 records)≤2*records+1 := by
    by_cases z : Nat.clog 2 records=0
    · simp [z]
    · have small:=Nat.pow_lt_of_lt_clog
        (show Nat.clog 2 records-1<Nat.clog 2 records by omega)
      rw [show Nat.clog 2 records=Nat.clog 2 records-1+1 by omega,pow_succ]
      omega
  dsimp only [terminalHistoryOrder]
  refine ⟨le_max_left ..,max_le (by omega) (Nat.clog_le_of_le_pow upper),
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (le_max_right ..)),?_⟩
  rcases le_total (h-1) (Nat.clog 2 records) with higher|lower
  · rw [max_eq_right higher]
    exact rounded.trans (Nat.le_add_right ..)
  · rw [max_eq_left lower]
    have small:=(Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le h 1))
    exact small.trans (Nat.le_add_left ..)

/-- Each of the seven words of source code, all source registers and all
original stored words appear in the target trace. The converted clock uses 64
physical steps per source instruction, including the final stop. -/
theorem fixed_isa_history_room (h labels regs initial fuel obs : ℕ) :
    let total:=CheapISA.dataBase labels regs+initial+(CheapISA.hostFuel fuel+obs)
    let m:=terminalHistoryOrder h total
    total≤2^(3*h) →
    h-1≤ m ∧ m≤3*h ∧ total≤2^m ∧
    CheapISA.hostFuel fuel+1+2^m+obs ≤ 256*(labels+regs+initial+fuel+obs+2^h+1) := by
  intro total m cap
  obtain ⟨lo,hi,full,rounded⟩:=terminal_history_order h total cap
  refine ⟨lo,hi,full,?_⟩
  change 2^m ≤ 2*total+1+2^h at rounded
  calc
    _ ≤ CheapISA.hostFuel fuel+1+(2*total+1+2^h)+obs := Nat.add_le_add_right (Nat.add_le_add_left rounded _) _
    _ ≤ _ := by
      dsimp only [total,CheapISA.dataBase,CheapISA.regBase,CheapISA.hostFuel]
      have paid : 1≤(2:ℕ)^h := Nat.one_le_two_pow
      omega

/-- The expanded clock, image and wider native word retain one common
bit cost per word, including a one-time charge for the program and registers. -/
theorem fixed_isa_source_cost (h labels regs initial fuel obs w A : ℕ)
    (wide : w≤A*h) :
    let total:=CheapISA.dataBase labels regs+initial+(CheapISA.hostFuel fuel+obs)
    let m:=terminalHistoryOrder h total
    total≤2^(3*h) →
    fixedISAPrice*(CheapISA.hostFuel fuel+1+2^m+obs)*(CheapISA.width w+1) ≤
      (256*fixedISAPrice*(A+6))*(labels+regs+initial+fuel+obs+2^h+1)*(h+1) := by
  intro total m cap
  have words := (fixed_isa_history_room h labels regs initial fuel obs cap).2.2.2
  have bits : CheapISA.width w+1≤(A+6)*(h+1) := by
    dsimp only [CheapISA.width]
    rw [Nat.add_mul,Nat.mul_add]
    omega
  calc
    _ ≤ fixedISAPrice*(256*(labels+regs+initial+fuel+obs+2^h+1))*((A+6)*(h+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ words) bits
    _ = _ := by ring

end Hierarchy.DescentCompiler

end OAI

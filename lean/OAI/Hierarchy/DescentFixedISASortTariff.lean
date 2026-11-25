import OAI.Hierarchy.DescentFixedISAHistorySize
import OAI.Hierarchy.DescentTerminalChosenSort

namespace OAI
/-! # The fixed interpreter's actual chosen sorting calls and the price of all their pins -/

namespace Hierarchy.DescentCompiler
open TaggedShorterHistoryOrder DescentTerminalChosenSort DescentTerminalHost.SortBank

theorem fixed_isa_sort_tariff (κ : Type*) [LinearOrder κ] {h m : ℕ}
    (base : 4≤h) (lo : h-1≤ m) (hi : m≤3*h) (w A : ℕ) (wide : w≤A*h) :
    let K:=7*(A+6)
    let bits:=RecordWidth (CheapISA.width w+1)
    let parts:=TaggedWidthSlices.count (h+bits) h
    bits≤K*h ∧ parts≤K+1 ∧
      1000*(K+parts+1)*(localCount (stages κ base lo hi)*2^h+2^h)*(h+1) ≤
        (1000*(2*K+2)*(2*4^7+1))*(2^m+2^h)*(h+1) := by
  intro K bits parts
  have span : bits≤K*h := by
    change RecordWidth (w+5+1)≤7*(A+6)*h
    rw [recordWidth_eq,Nat.mul_assoc,Nat.add_mul]
    omega
  have count := (fields bits K (by omega : 0<h) span).2.1
  change parts≤K+1 at count
  have volume:=DescentTerminalChosenSort.volume κ base lo hi
  refine ⟨span,count,?_⟩
  calc
    _ ≤ 1000*(2*K+2)*((2*4^7+1)*(2^m+2^h))*(h+1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) volume)
    _ = _ := by ring

/-- The price of the actual sort bank is linear in the expanded resident image
and clock, uniformly in the source program and the number of external pins. -/
theorem fixed_isa_source_sort (κ : Type*) [LinearOrder κ] (h labels regs initial fuel obs w A : ℕ)
    (base : 4≤h) (wide : w≤A*h) :
    let N:=CheapISA.dataBase labels regs+initial+(CheapISA.hostFuel fuel+obs)
    let _m:=terminalHistoryOrder h N
    ∀ cap : N≤2^(3*h),
      let legal:=terminal_history_order h N cap
      let K:=7*(A+6)
      let bits:=RecordWidth (CheapISA.width w+1)
      let parts:=TaggedWidthSlices.count (h+bits) h
      1000*(K+parts+1)*(localCount (stages κ base legal.1 legal.2.1)*2^h+2^h)*(h+1) ≤
        (257*(1000*(2*K+2)*(2*4^7+1)))*(labels+regs+initial+fuel+obs+2^h+1)*(h+1) := by
  intro N m cap legal K bits parts
  let raw:=labels+regs+initial+fuel+obs+2^h+1
  have cover:= (fixed_isa_history_room h labels regs initial fuel obs cap).2.2.2
  change CheapISA.hostFuel fuel+1+2^m+obs≤256*raw at cover
  have lower : 2^h≤ raw := by dsimp [raw];omega
  have cells : 2^m+2^h≤257*raw := by omega
  have price:=(fixed_isa_sort_tariff κ base legal.1 legal.2.1 w A wide).2.2
  apply price.trans
  calc
    _ ≤ (1000*(2*K+2)*(2*4^7+1))*(257*raw)*(h+1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cells)
    _ = _ := by dsimp only [raw];ring

end Hierarchy.DescentCompiler

end OAI

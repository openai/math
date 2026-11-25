import Mathlib.Tactic.Ring

namespace OAI
/-! # Physical cost of the original exterior packets on a shared compiled word -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
theorem packet_bill (copies s e j r h word factor:ℕ) (shape:copies=2^(j+(j+r))) (packing:h≤32*((2^j)*s))
    (cpu:word≤factor*h) :
    (e*2^(j+r))*word≤(32*factor)*(copies*s)*e := by
  have a:=Nat.mul_le_mul_left factor packing
  calc
    _ ≤ (e*2^(j+r))*(factor*(32*((2^j)*s))) := Nat.mul_le_mul_left _ (cpu.trans a)
    _ = _ := by rw [shape,pow_add (2:ℕ) j (j+r)];ring

end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI

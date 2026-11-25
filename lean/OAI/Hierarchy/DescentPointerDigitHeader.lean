import OAI.Hierarchy.DescentCompactedOperandHeaders

namespace OAI
/-! # Pointer headers at the physical word width -/
namespace Hierarchy.DescentOperandStateBanks
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section

/-- Reducing four coordinates modulo the native width preserves the pointer kind and its forced zero fields. -/
theorem Pointer.typed_digits (p : Pointer) (bits : ℕ) (wide : 2<2^bits) :
    TypedHeader (fun f=>(p.header f : Cell bits)) :=by
  have one : 1<2^bits:=by omega
  cases p with
  | privateWord n=>
    refine ⟨.privateWord (n%2^bits),?_⟩
    intro f;fin_cases f <;> simp [Pointer.header,Fin.val_natCast]
  | cable peer serial chunk=>
    refine ⟨.cable (peer%2^bits) (serial%2^bits) (chunk%2^bits),?_⟩
    intro f;fin_cases f <;> simp [Pointer.header,Fin.val_natCast,Nat.mod_eq_of_lt one]
  | pin port chunk=>
    refine ⟨.pin (port%2^bits) (chunk%2^bits),?_⟩
    intro f;fin_cases f <;> simp [Pointer.header,Fin.val_natCast,Nat.mod_eq_of_lt wide]

theorem component_typed (bits : ℕ) (wide : 2<2^bits) (tag peer serial chunk priorAlias : ℕ) :
    TypedHeader (fun f=>(component tag peer serial chunk priorAlias f : Cell bits)) :=by
  by_cases cable : tag=3
  · simpa only [component,ite_eq_left cable] using (Pointer.cable peer serial chunk).typed_digits bits wide
  by_cases pin : tag=4
  · simpa only [component,ite_eq_right cable,ite_eq_left pin] using (Pointer.pin serial chunk).typed_digits bits wide
  · simpa only [component,ite_eq_right cable,ite_eq_right pin] using (Pointer.privateWord (priorAlias-1)).typed_digits bits wide

end
end Hierarchy.DescentOperandStateBanks

end OAI

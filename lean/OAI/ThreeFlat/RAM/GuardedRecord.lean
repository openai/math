import OAI.ThreeFlat.Diagonal.GuardedNetwork
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Individual source and coefficient words in the repeated guarded network -/

namespace ThreeFlat.RAM.GuardedRecord

open Computability.VPVNP.BurstRAM Diagonal Diagonal.TraceCircuit Diagonal.GuardedNetwork BitLayout

variable {F : Type*} [CommSemiring F] {q b p e t w : ℕ}
variable (N : BitNetwork F q) (input : Fin t → Fin q → BitSource b p)
  (left right : Fin t → Fin e → BitSource b p)
  (code : FieldCode F w)

def mapped (i : Fin t) : BitSource N.internal q → ℕ
  | .constant v => v.toNat
  | .pin j => sourceAddress (input i j)
  | .hidden k => hiddenBase p + b + i.val * N.internal + k.val

theorem copied_address (i : Fin t) (k : Fin N.cells) (j : Fin 3) :
    sourceAddress ((network N input left right).source (finProdFinEquiv (i,k.castAdd e)) j) =
      mapped N input i (N.source k j) := by
  cases h : N.source k j with
  | constant v => simp [network, assemble, row, widen, rowAddress, mapped, h, sourceAddress]
  | hidden v =>
    simp [network, assemble, row, widen, rowAddress, mapped, h, sourceAddress]
    ac_rfl
  | pin v =>
    cases hv : input i v <;>
      simp [network, assemble, row, widen, rowAddress, ports, mapped, h, hv, sourceAddress]

theorem copied_table (i : Fin t) (k : Fin N.cells) (v : Fin 3 → Bool) :
    (network N input left right).table (finProdFinEquiv (i,k.castAdd e)) v = N.table k v := by
  simp [network, assemble, row]

theorem guard_address (i : Fin t) (k : Fin e) (j : Fin 3) :
    sourceAddress ((network N input left right).source
      (finProdFinEquiv (i,Fin.natAdd N.cells k)) j) =
      if j = 0 then sourceAddress (left i k) else
        if j = 1 then sourceAddress (right i k) else 0 := by
  fin_cases j
  · cases h : left i k <;> simp [network, assemble, row, rowAddress, ports, h, sourceAddress]
  · have addr : k.addNat e = Fin.natAdd e k := Fin.ext (Nat.add_comm k.val e)
    have rd : Fin.append (left i) (right i) (k.addNat e) = right i k := by
      rw [addr,Fin.append_right]
    cases h : right i k <;> simp [network, assemble, row, rowAddress, ports, h, rd, sourceAddress]
  · simp [network, assemble, row, rowAddress, sourceAddress]

theorem guard_table (i : Fin t) (k : Fin e) (v : Fin 3 → Bool) :
    (network N input left right).table (finProdFinEquiv (i,Fin.natAdd N.cells k)) v =
      if v 0 = v 1 then 1 else 0 := by
  simp [network, assemble, row]

theorem copied_record (i : Fin t) (k : Fin N.cells) (j : Fin 11) :
    record (network N input left right) code (finProdFinEquiv (i,k.castAdd e)) j =
      if h : j.val < 3 then
        Fin.ofNat _ (mapped N input i (N.source k ⟨j.val,h⟩))
      else record N code k j := by
  by_cases h : j.val < 3
  · simp only [record,dite_eq_left h]
    exact congrArg (Fin.ofNat _) (copied_address N input left right i k ⟨j.val,h⟩)
  · simp only [record,dite_eq_right h,copied_table]

theorem guard_record (i : Fin t) (k : Fin e) (j : Fin 11) :
    record (network N input left right) code (finProdFinEquiv (i,Fin.natAdd N.cells k)) j =
      if j.val = 0 then Fin.ofNat _ (sourceAddress (left i k)) else
      if j.val = 1 then Fin.ofNat _ (sourceAddress (right i k)) else
      if j.val = 2 then 0 else
        if (j.val-3).testBit 0 = (j.val-3).testBit 1 then code.encode 1 else code.encode 0 := by
  by_cases h : j.val < 3
  · simp only [record,dite_eq_left h]
    rw [guard_address N input left right i k]
    have hj : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
    rcases hj with a|a|a <;> simp [Fin.ext_iff, a]
  · have h0 : j.val ≠ 0 := by omega
    have h1 : j.val ≠ 1 := by omega
    have h2 : j.val ≠ 2 := by omega
    simp only [record,dite_eq_right h,guard_table,h0,h1,h2,ite_false,bits]
    change code.encode (if (j.val-3).testBit 0=(j.val-3).testBit 1 then 1 else 0) = _
    exact apply_ite _ _ _ _

end ThreeFlat.RAM.GuardedRecord

end OAI

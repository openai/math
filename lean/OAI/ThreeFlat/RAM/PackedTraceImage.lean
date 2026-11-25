import OAI.ThreeFlat.RAM.FixedTraceImage
import OAI.ThreeFlat.RAM.PackWordBoot

namespace OAI
/-! # Native construction of the physical gate and port tables from public bits -/

namespace ThreeFlat.RAM.FixedTraceImage

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TraceAddressRecord
open scoped Fin.CommRing
variable {F : Type*} [CommSemiring F] {w q p r k : ℕ}

def parameter (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record) :
    Fin (w*count N) → Bool := fun i => bits (word N code R) i.val

omit [CommSemiring F] in
theorem generate_disjoint (M : Machine w p r k) (boot : Fin 5 → Fin p) (loopPc : Fin 10 → Fin p)
    (reg : Fin 8 ↪ Fin r) (pub : Fin 4 → Fin k) (exit : Fin p)
    (init : ∀ i, M.code (boot i) = PackWordBoot.header boot (loopPc 0) reg pub i)
    (rom : ∀ i, M.code (loopPc i) = PackWordTable.instruction loopPc reg exit i)
    (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record) (src dst : ℕ)
    (c : Config w p r) (m : Memory w) (entry : c.pc=boot 0)
    (params : ∀ i, M.publicData (pub i) = (![src,dst,dst+count N,w] i : ℕ))
    (apart : dst+count N ≤ src ∨ src+w*count N ≤ dst)
    (dstFit : dst+count N < 2^w) (fit : src+w*count N < 2^w)
    (input : ∀ i, m (src+i.val) = ((parameter N code R i).toNat : Word w)) :
    ∃ out, advance M.program (count N*(5*w+6)+6) c m = some (out,packed N code R dst m) ∧
      out.pc=exit := by
  apply PackWordBoot.generate_disjoint M boot loopPc reg pub exit init rom src dst (count N)
    (fun a => word N code R (a-dst)) c m entry params apart dstFit fit
  intro i hi j hj
  have bound : w*i+j<w*count N := calc
    w*i+j < w*i+w := Nat.add_lt_add_left hj _
    _ = w*(i+1) := (Nat.mul_succ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hi
  have h := input ⟨_,bound⟩
  simpa only [Nat.add_assoc,parameter,bits_at (word N code R) i (⟨j,hj⟩ : Fin w),
    Nat.add_sub_cancel_left] using h

omit [CommSemiring F] in
theorem generate (M : Machine w p r k) (boot : Fin 5 → Fin p) (loopPc : Fin 10 → Fin p)
    (reg : Fin 8 ↪ Fin r) (pub : Fin 4 → Fin k) (exit : Fin p)
    (init : ∀ i, M.code (boot i) = PackWordBoot.header boot (loopPc 0) reg pub i)
    (rom : ∀ i, M.code (loopPc i) = PackWordTable.instruction loopPc reg exit i)
    (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record) (src dst : ℕ)
    (c : Config w p r) (m : Memory w) (entry : c.pc=boot 0)
    (params : ∀ i, M.publicData (pub i) = (![src,dst,dst+count N,w] i : ℕ))
    (apart : dst+count N ≤ src) (fit : src+w*count N < 2^w)
    (input : ∀ i, m (src+i.val) = ((parameter N code R i).toNat : Word w)) :
    ∃ out, advance M.program (count N*(5*w+6)+6) c m = some (out,packed N code R dst m) ∧
      out.pc=exit :=
  generate_disjoint M boot loopPc reg pub exit init rom N code R src dst c m entry params
    (.inl apart) (by omega) fit input


end ThreeFlat.RAM.FixedTraceImage

end OAI

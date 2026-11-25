import OAI.ThreeFlat.RAM.PackedTraceImage
import OAI.ThreeFlat.RAM.ContinuationLink

namespace OAI
/-! # Relocatable packing of the public local trace image -/

namespace ThreeFlat.RAM.PackWordBlock

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink Diagonal.TraceAddressRecord
open scoped Fin.CommRing
variable {w p r k : ℕ}

def headPC (pc : Fin 15 ↪ Fin p) (i : Fin 5) := pc (i.castAdd 10)
def loopPC (pc : Fin 15 ↪ Fin p) (i : Fin 10) := pc (Fin.natAdd 5 i)

def block (w : ℕ) : Block w 15 8 4 where
  first := (0 : Fin 5).castAdd 10
  emit pc reg pub exit i := Fin.addCases (m:=5) (n:=10) (PackWordBoot.header (headPC pc) (loopPC pc 0) reg pub)
    (PackWordTable.instruction (loopPC pc) reg exit) i

theorem advance_disjoint {F : Type*} [CommSemiring F] {q : ℕ} (M : Machine w p r k)
    (pc : Fin 15 ↪ Fin p) (reg : Fin 8 ↪ Fin r) (pub : Fin 4 → Fin k) (exit : Fin p)
    (rom : (block w).Installed M pc reg pub exit)
    (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record) (src dst : ℕ)
    (c : Config w p r) (m : Memory w) (entry : c.pc=pc (block w).first)
    (params : ∀ i, M.publicData (pub i) = (![src,dst,dst+FixedTraceImage.count N,w] i : ℕ))
    (apart : dst+FixedTraceImage.count N ≤ src ∨ src+w*FixedTraceImage.count N ≤ dst)
    (dstFit : dst+FixedTraceImage.count N < 2^w) (fit : src+w*FixedTraceImage.count N < 2^w)
    (input : ∀ i, m (src+i.val) = ((FixedTraceImage.parameter N code R i).toNat : Word w)) :
    ∃ out, RAM.advance M.program (FixedTraceImage.count N*(5*w+6)+6) c m =
      some (out,FixedTraceImage.packed N code R dst m) ∧ out.pc=exit := by
  apply FixedTraceImage.generate_disjoint M (headPC pc) (loopPC pc) reg pub exit _ _
    N code R src dst c m entry params apart dstFit fit input
  · intro i
    simpa [block,headPC] using rom (i.castAdd 10)
  · intro i
    simpa [block,loopPC] using rom (Fin.natAdd 5 i)

theorem advance {F : Type*} [CommSemiring F] {q : ℕ} (M : Machine w p r k)
    (pc : Fin 15 ↪ Fin p) (reg : Fin 8 ↪ Fin r) (pub : Fin 4 → Fin k) (exit : Fin p)
    (rom : (block w).Installed M pc reg pub exit)
    (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record) (src dst : ℕ)
    (c : Config w p r) (m : Memory w) (entry : c.pc=pc (block w).first)
    (params : ∀ i, M.publicData (pub i) = (![src,dst,dst+FixedTraceImage.count N,w] i : ℕ))
    (apart : dst+FixedTraceImage.count N ≤ src) (fit : src+w*FixedTraceImage.count N < 2^w)
    (input : ∀ i, m (src+i.val) = ((FixedTraceImage.parameter N code R i).toNat : Word w)) :
    ∃ out, RAM.advance M.program (FixedTraceImage.count N*(5*w+6)+6) c m =
      some (out,FixedTraceImage.packed N code R dst m) ∧ out.pc=exit :=
  advance_disjoint M pc reg pub exit rom N code R src dst c m entry params
    (.inl apart) (by omega) fit input


end ThreeFlat.RAM.PackWordBlock

end OAI

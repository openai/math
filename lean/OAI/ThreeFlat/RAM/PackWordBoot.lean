import OAI.ThreeFlat.RAM.PackWordTable

namespace OAI
/-! # Entering the bit-to-word packer from arbitrary registers -/

namespace ThreeFlat.RAM.PackWordBoot

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {w p r k : ℕ}

/-- Public operands hold the bit source, word destination, exclusive word end, and word width. -/
def header (pc : Fin 5 → Fin p) (start : Fin p) (reg : Fin 8 ↪ Fin r) (pub : Fin 4 → Fin k) :
    Fin 5 → Instr w p r k :=
  ![.publicWord (reg 0) (pub 0) (pc 1), .publicWord (reg 5) (pub 1) (pc 2),
    .publicWord (reg 6) (pub 2) (pc 3), .publicWord (reg 7) (pub 3) (pc 4),
    .constant (reg 2) 1 start]

theorem generate_disjoint (M : Machine w p r k) (boot : Fin 5 → Fin p) (pc : Fin 10 → Fin p)
    (reg : Fin 8 ↪ Fin r) (pub : Fin 4 → Fin k) (exit : Fin p)
    (init : ∀ i, M.code (boot i) = header boot (pc 0) reg pub i)
    (rom : ∀ i, M.code (pc i) = PackWordTable.instruction pc reg exit i)
    (src dst n : ℕ) (word : ℕ → Word w) (c : Config w p r) (m : Memory w) (entry : c.pc=boot 0)
    (params : ∀ i, M.publicData (pub i) = (![src,dst,dst+n,w] i : ℕ))
    (apart : dst+n ≤ src ∨ src+w*n ≤ dst) (dstFit : dst+n < 2^w) (fit : src+w*n < 2^w)
    (bits : ∀ i<n, ∀ j<w, m (src+w*i+j) =
      (((word (dst+i)).val.testBit (w-1-j)).toNat : Word w)) :
    ∃ out, advance M.program (n*(5*w+6)+6) c m = some (out,fillSegment dst n word m) ∧ out.pc=exit := by
  let d := ((((c.put (boot 1) (reg 0) (src : Word w)).put (boot 2) (reg 5) (dst : Word w)).put
    (boot 3) (reg 6) ((dst+n : ℕ) : Word w)).put (boot 4) (reg 7) (w : Word w)).put (pc 0) (reg 2) 1
  have head : advance M.program 5 c m = some (d,m) := by
    simp [advance,Machine.program,entry,init,header,Instr.run,Config.put,d,params]
  have hsrc : (d.reg (reg 0)).val = src := by
    simp (config := { decide := true }) [d,Config.put,Fin.val_cast_of_lt (show src<2^w by omega)]
  have hdst : (d.reg (reg 5)).val = dst := by
    simp (config := { decide := true }) [d,Config.put,Fin.val_cast_of_lt (show dst<2^w by omega)]
  have hend : (d.reg (reg 6)).val = dst+n := by
    have h : d.reg (reg 6) = ((dst+n : ℕ) : Word w) := by
      simp (config := { decide := true }) [d,Config.put]
    rw [h,Fin.val_cast_of_lt (by omega : dst+n<2^w)]
  have width : d.reg (reg 7) = (w : Word w) := by simp (config := {decide := true}) [d,Config.put]
  obtain ⟨out,run,exitPc⟩ := PackWordTable.generate_disjoint M pc reg exit rom word n d m rfl (by simp [d]) width
    (by rw [hdst,hend]) (by rwa [hend,hsrc,hdst]) (by rwa [hsrc]) (by simpa [hsrc,hdst] using bits)
  refine ⟨out,?_,exitPc⟩
  rw [hdst] at run
  simpa only [show 5+(n*(5*w+6)+1)=n*(5*w+6)+6 by omega] using advance_trans head run

theorem generate (M : Machine w p r k) (boot : Fin 5 → Fin p) (pc : Fin 10 → Fin p)
    (reg : Fin 8 ↪ Fin r) (pub : Fin 4 → Fin k) (exit : Fin p)
    (init : ∀ i, M.code (boot i) = header boot (pc 0) reg pub i)
    (rom : ∀ i, M.code (pc i) = PackWordTable.instruction pc reg exit i)
    (src dst n : ℕ) (word : ℕ → Word w) (c : Config w p r) (m : Memory w) (entry : c.pc=boot 0)
    (params : ∀ i, M.publicData (pub i) = (![src,dst,dst+n,w] i : ℕ))
    (apart : dst+n ≤ src) (fit : src+w*n < 2^w)
    (bits : ∀ i<n, ∀ j<w, m (src+w*i+j) =
      (((word (dst+i)).val.testBit (w-1-j)).toNat : Word w)) :
    ∃ out, advance M.program (n*(5*w+6)+6) c m = some (out,fillSegment dst n word m) ∧ out.pc=exit :=
  generate_disjoint M boot pc reg pub exit init rom src dst n word c m entry params
    (.inl apart) (by omega) fit bits


end ThreeFlat.RAM.PackWordBoot

end OAI

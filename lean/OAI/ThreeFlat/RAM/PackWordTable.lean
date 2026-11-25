import OAI.ThreeFlat.RAM.ReadPackedWord
import OAI.ThreeFlat.RAM.WordSegment
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Packing an entire bit parameter string by a fixed ten-instruction loop -/

namespace ThreeFlat.RAM.PackWordTable

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {w p r k : ℕ}

private def ix (reg : Fin 8 ↪ Fin r) : Fin 5 ↪ Fin r :=
  (Fin.castAddEmb 3 : Fin 5 ↪ Fin 8).trans reg

private def ip (pc : Fin 10 → Fin p) (i : Fin 5) := pc (Fin.natAdd 3 (i.castAdd 2))

/-- The bit-loop cursor remains at the first unread input bit on return.
Registers five, six and seven are the output cursor, end, and word width. -/
def instruction (pc : Fin 10 → Fin p) (reg : Fin 8 ↪ Fin r) (exit : Fin p) :
    Fin 10 → Instr w p r k :=
  let scan := ReadPackedWord.instruction (ip pc) (ix reg) (pc 8)
  ![.jumpLt (reg 5) (reg 6) (pc 1) exit, .constant (reg 3) 0 (pc 2),
    .binary .add (reg 1) (reg 0) (reg 7) (ip pc 0),
    scan 0, scan 1, scan 2, scan 3, scan 4,
    .writeExternal (reg 5) (reg 3) (pc 9), .binary .add (reg 5) (reg 5) (reg 2) (pc 0)]

theorem generate_disjoint (M : Machine w p r k) (pc : Fin 10 → Fin p) (reg : Fin 8 ↪ Fin r) (exit : Fin p)
    (rom : ∀ i, M.code (pc i) = instruction pc reg exit i)
    (word : ℕ → Word w) (n : ℕ) (c : Config w p r) (m : Memory w) (entry : c.pc=pc 0)
    (unit : c.reg (reg 2)=1) (width : c.reg (reg 7)=(w : Word w))
    (len : (c.reg (reg 5)).val+n=(c.reg (reg 6)).val)
    (apart : (c.reg (reg 6)).val ≤ (c.reg (reg 0)).val ∨
      (c.reg (reg 0)).val + w*n ≤ (c.reg (reg 5)).val)
    (fits : (c.reg (reg 0)).val + w*n < 2^w)
    (bits : ∀ i<n, ∀ j<w, m ((c.reg (reg 0)).val+w*i+j) =
      (((word ((c.reg (reg 5)).val+i)).val.testBit (w-1-j)).toNat : Word w)) :
    ∃ d, advance M.program (n*(5*w+6)+1) c m =
      some (d,fillSegment (c.reg (reg 5)).val n word m) ∧ d.pc=exit := by
  have installed (i : Fin 5) : M.code (ip pc i) = ReadPackedWord.instruction (ip pc) (ix reg) (pc 8) i := by
    refine (rom (Fin.natAdd 3 (i.castAdd 2))).trans ?_
    fin_cases i <;> rfl
  induction n generalizing c m with
  | zero =>
    have eq : c.reg (reg 5)=c.reg (reg 6) := Fin.ext (by simpa using len)
    refine ⟨{c with pc:=exit},?_,rfl⟩
    simp [advance,Machine.program,entry,rom,instruction,Instr.run,eq]
  | succ n ih =>
    let src := (c.reg (reg 0)).val
    let dst := (c.reg (reg 5)).val
    let stop := (c.reg (reg 6)).val
    have lt : c.reg (reg 5)<c.reg (reg 6) := by change _ < (c.reg (reg 6)).val; omega
    have fits' : src+w<2^w := by change src+w*(n+1)<_ at fits; rw [Nat.mul_succ] at fits; omega
    let start := (c.put (pc 2) (reg 3) 0).put (ip pc 0) (reg 1) (c.reg (reg 0)+c.reg (reg 7))
    have head : advance M.program 3 c m = some (start,m) := by
      simp (config := {decide:=true}) [advance,Machine.program,entry,rom,instruction,Instr.run,
        lt,start,BinaryOp.eval,Config.put,ip]
    have original (i : Fin 8) (hi : i≠1) (hj : i≠3) : start.reg (reg i)=c.reg (reg i) := by
      simp [start,Config.put,Function.update_of_ne,hi,hj]
    have first : start.reg (ix reg 0) = c.reg (reg 0) := original 0 (by decide) (by decide)
    have endw : start.reg (ix reg 1) = ((src+w : ℕ) : Word w) := by
      change (start.reg (reg 1)) = _
      simp [start,width,src]
    have empty : start.reg (ix reg 3)=0 := by
      change start.reg (reg 3) = _
      simp (config := {decide:=true}) [start,Config.put]
    obtain ⟨z,hz,pc8,value,after,_,_,keep⟩ := ReadPackedWord.run M (ip pc) (ix reg) (pc 8)
      installed m w start rfl ((original 2 (by decide) (by decide)).trans unit)
      (by rw [first,endw,Fin.val_cast_of_lt fits'])
    have read : z.reg (reg 3) = word dst := by
      change z.reg (ix reg 3) = _
      rw [value,first,empty]
      apply ReadPackedWord.accumulate_full
      intro j hj
      simpa [src,dst] using bits 0 (by omega) j hj
    have readEnd : z.reg (reg 0) = ((src+w : ℕ) : Word w) := after.trans endw
    have saved (i : Fin 8) (h0 : i≠0) (h1 : i≠1) (h3 : i≠3) (h4 : i≠4) :
        z.reg (reg i) = c.reg (reg i) :=
      (keep _ (reg.injective.ne h0) (reg.injective.ne h3) (reg.injective.ne h4)).trans (original i h1 h3)
    have k2 := saved 2 (by decide) (by decide) (by decide) (by decide)
    have k5 := saved 5 (by decide) (by decide) (by decide) (by decide)
    have k6 := saved 6 (by decide) (by decide) (by decide) (by decide)
    have k7 := saved 7 (by decide) (by decide) (by decide) (by decide)
    let next := z.put (pc 0) (reg 5) (z.reg (reg 5)+z.reg (reg 2))
    let m' := writeMemory m (c.reg (reg 5)) (word dst)
    have write : advance M.program 2 z m = some (next,m') := by
      simp [advance,Machine.program,pc8,rom,instruction,Instr.run,read,k5,k2,
        BinaryOp.eval,m',next,Config.put]
    have nextSrc : (next.reg (reg 0)).val=src+w := by
      have same : next.reg (reg 0) = z.reg (reg 0) := by
        simp (config := {decide:=true}) [next,Config.put]
      rw [same,readEnd,Fin.val_cast_of_lt fits']
    have nextDest : (next.reg (reg 5)).val=dst+1 := by
      simp only [next,Config.put_same,k5,k2,unit]
      apply Fin.val_add_one_of_lt'
      have := (c.reg (reg 6)).isLt
      omega
    have nextStop : next.reg (reg 6)=c.reg (reg 6) := by
      simp (config := {decide:=true}) [next,Config.put,k6]
    have nextUnit : next.reg (reg 2)=1 := by
      simp (config := {decide:=true}) [next,Config.put,k2,unit]
    have nextWidth : next.reg (reg 7)=(w : Word w) := by
      simp (config := {decide:=true}) [next,Config.put,k7,width]
    change (c.reg (reg 6)).val ≤ src ∨ src + w*(n+1) ≤ dst at apart
    rw [Nat.mul_succ] at apart
    obtain ⟨d,rest,done⟩ := ih next m' rfl nextUnit nextWidth
      (by rw [nextDest,nextStop]; change dst+(n+1)=_ at len; omega)
      (by rw [nextStop,nextSrc,nextDest]; omega)
      (by rw [nextSrc]; rw [Nat.mul_succ] at fits; dsimp [src] at *; omega)
      (by
        intro i hi j hj
        rw [nextSrc,nextDest]
        have ne : src+w+w*i+j≠(c.reg (reg 5)).val := by
          have bound := Nat.mul_le_mul_left w (show i+1≤n by omega)
          rw [Nat.mul_succ] at bound
          change _≠dst
          omega
        have block : src+w+w*i+j=src+w*(i+1)+j := by ring
        change (if src+w+w*i+j=(c.reg (reg 5)).val then word dst else m (src+w+w*i+j)) = _
        rw [ite_eq_right ne,block,show dst+1+i=dst+(i+1) by omega]
        exact bits (i+1) (by omega) j hj)
    refine ⟨d,?_,done⟩
    have allSteps := advance_trans (advance_trans (advance_trans head hz) write) rest
    rw [show (n+1)*(5*w+6)+1 = 3+(5*w+1)+2+(n*(5*w+6)+1) by ring,
      fillSegment_succ]
    simpa only [nextDest] using allSteps

theorem generate (M : Machine w p r k) (pc : Fin 10 → Fin p) (reg : Fin 8 ↪ Fin r) (exit : Fin p)
    (rom : ∀ i, M.code (pc i) = instruction pc reg exit i)
    (word : ℕ → Word w) (n : ℕ) (c : Config w p r) (m : Memory w) (entry : c.pc=pc 0)
    (unit : c.reg (reg 2)=1) (width : c.reg (reg 7)=(w : Word w))
    (len : (c.reg (reg 5)).val+n=(c.reg (reg 6)).val)
    (apart : (c.reg (reg 6)).val≤(c.reg (reg 0)).val)
    (fits : (c.reg (reg 0)).val + w*n < 2^w)
    (bits : ∀ i<n, ∀ j<w, m ((c.reg (reg 0)).val+w*i+j) =
      (((word ((c.reg (reg 5)).val+i)).val.testBit (w-1-j)).toNat : Word w)) :
    ∃ d, advance M.program (n*(5*w+6)+1) c m =
      some (d,fillSegment (c.reg (reg 5)).val n word m) ∧ d.pc=exit :=
  generate_disjoint M pc reg exit rom word n c m entry unit width len (.inl apart) fits bits


end ThreeFlat.RAM.PackWordTable

end OAI

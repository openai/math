import OAI.ThreeFlat.RAM.PackWordBoot
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Native unpacking of the common histogram and static compressor archives

The same word collector mounts a public immutable archive and the histogram prefix.
The latter starts in the new auxiliary register at opening and in the old one elsewhere.
-/

namespace ThreeFlat.RAM.PackedStageArchive

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink PhysicalProcedure
open scoped Fin.CommRing
variable {w p r k : ℕ}

structure Layout where
  phase : ℕ
  oldSource : ℕ
  newSource : ℕ
  destination : ℕ
  count : ℕ

def Layout.source (x : Layout) (m : Memory w) : ℕ :=
  if m x.phase=1 then x.newSource else x.oldSource

/-- Ten setup labels. Each branch executes nine instructions and joins at label 6. -/
def head (x : Layout) (pc : Fin 10 → Fin p) (reg : Fin 8 ↪ Fin r) (body : Fin p) :
    Fin 10 → Instr w p r k :=
  ![.constant (reg 0) x.phase (pc 1), .readExternal (reg 1) (reg 0) (pc 2),
    .constant (reg 2) 1 (pc 3), .jumpEq (reg 1) (reg 2) (pc 4) (pc 5),
    .constant (reg 0) x.newSource (pc 6), .constant (reg 0) x.oldSource (pc 6),
    .constant (reg 5) x.destination (pc 7), .constant (reg 6) (x.destination+x.count:ℕ) (pc 8),
    .constant (reg 7) w (pc 9), .constant (reg 2) 1 body]

def block (x : Layout) : Block w 20 8 0 where
  first := 0
  emit pc reg _ exit i :=
    let a := (Fin.castAddEmb 10 : Fin 10 ↪ Fin 20).trans pc
    let b := (Fin.natAddEmb 10 : Fin 10 ↪ Fin 20).trans pc
    Fin.addCases (m:=10) (n:=10) (motive:=fun _ => Instr w _ _ _)
      (head x a reg (b 0)) (PackWordTable.instruction b reg exit) i

def procedure (x : Layout) : Procedure w := ⟨20,8,0,block x,Fin.elim0⟩

/-- Only the selected raw source is read. Its source and its destination may lie in either order. -/
theorem generate (x : Layout) (M : Machine w p r k) (pc : Fin 20 ↪ Fin p)
    (reg : Fin 8 ↪ Fin r) (pub : Fin 0 → Fin k) (exit : Fin p)
    (installed : (block x).Installed M pc reg pub exit) (c : Config w p r) (m : Memory w)
    (entry : c.pc=pc 0) (phaseFit : x.phase<2^w) (word : ℕ → Word w)
    (apart : x.destination+x.count ≤ x.source m ∨ x.source m+w*x.count ≤ x.destination)
    (dstFit : x.destination+x.count < 2^w) (fit : x.source m+w*x.count < 2^w)
    (bits : ∀ i<x.count, ∀ j<w, m (x.source m+w*i+j) =
      (((word (x.destination+i)).val.testBit (w-1-j)).toNat : Word w)) :
    ∃ out, advance M.program (x.count*(5*w+6)+10) c m =
      some (out,fillSegment x.destination x.count word m) ∧ out.pc=exit := by
  let a : Fin 10 → Fin p := (Fin.castAddEmb 10).trans pc
  let b : Fin 10 → Fin p := (Fin.natAddEmb 10).trans pc
  have left_pc (i : Fin 10) : a i=pc (i.castAdd 10) := by
    simp only [a, Function.Embedding.trans_apply, Fin.coe_castAddEmb]
  have right_pc (i : Fin 10) : b i=pc (Fin.natAdd 10 i) := by
    simp only [b, Function.Embedding.trans_apply, Fin.natAddEmb_apply]
  have ha (i) : M.code (a i)=head x a reg (b 0) i := by
    rw [left_pc i]
    simpa only [a,b,block,Fin.addCases_left] using installed (i.castAdd 10)
  have hb (i) : M.code (b i)=PackWordTable.instruction b reg exit i := by
    rw [right_pc i]
    simpa only [a,b,block,Fin.addCases_right] using installed (Fin.natAdd 10 i)
  let c' := ((c.put (a 1) (reg 0) x.phase).put (a 2) (reg 1) (m x.phase)).put (a 3) (reg 2) 1
  let d := ((((c'.put (a 6) (reg 0) (x.source m)).put (a 7) (reg 5) x.destination).put
    (a 8) (reg 6) (x.destination+x.count:ℕ)).put (a 9) (reg 7) w).put (b 0) (reg 2) 1
  have entry' : c.pc=a 0 := entry
  have boot : advance M.program 9 c m = some (d,m) := by
    by_cases h : m x.phase=1 <;>
      simp (config := {decide := true}) [advance,Machine.program,entry',ha,head,Instr.run,
        Config.put,d,c',Layout.source,Fin.val_cast_of_lt phaseFit,h]
  have src : (d.reg (reg 0)).val=x.source m := by
    simp (config := {decide := true}) [d,Config.put,Fin.val_cast_of_lt (show x.source m<2^w by omega)]
  have dst : (d.reg (reg 5)).val=x.destination := by
    simp (config := {decide := true}) [d,Config.put,Fin.val_cast_of_lt (show x.destination<2^w by omega)]
  have last : (d.reg (reg 6)).val=x.destination+x.count := by
    have e : d.reg (reg 6) = ((x.destination+x.count:ℕ) : Word w) := by
      simp (config := {decide := true}) [d,Config.put]
    rw [e,Fin.val_cast_of_lt dstFit]
  have width : d.reg (reg 7)=(w : Word w) := by simp (config := {decide := true}) [d,Config.put]
  obtain ⟨out,run,stop⟩ := PackWordTable.generate_disjoint M b reg exit hb word x.count d m rfl
    (by simp [d]) width (by rw [dst,last]) (by rwa [last,src,dst]) (by rwa [src])
    (by simpa only [src,dst] using bits)
  rw [dst] at run
  exact ⟨out,by simpa only [show 9+(x.count*(5*w+6)+1)=x.count*(5*w+6)+10 by omega]
    using advance_trans boot run,stop⟩

end ThreeFlat.RAM.PackedStageArchive

end OAI

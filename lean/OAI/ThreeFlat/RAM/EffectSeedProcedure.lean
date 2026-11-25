import OAI.ThreeFlat.RAM.EffectScatterAdvance
import OAI.ThreeFlat.RAM.EffectImage
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Native packing and sparse scatter of public address/value seed words -/

namespace ThreeFlat.RAM.EffectSeed
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure ContinuationLink EffectStream
open scoped Fin.CommRing
variable {w : ℕ}

def head {P R K : ℕ} (pc : Fin 3→Fin P) (regs : Fin 5 ↪ Fin R) (pub : Fin 2→Fin K)
    (next : Fin P) : Fin 3→Instr w P R K :=
  ![.publicWord (regs 0) (pub 0) (pc 1),.publicWord (regs 1) (pub 1) (pc 2),.constant (regs 4) 1 next]

def scatterBlock (w : ℕ) : Block w 9 5 2 where
  first := (0 : Fin 3).castAdd 6
  emit pc regs pub out := Fin.addCases (m:=3) (n:=6)
    (head (pc ∘ Fin.castAdd 6) regs pub (pc (Fin.natAdd 3 (0 : Fin 6))))
    (EffectStream.block (pc ∘ Fin.natAdd 3) regs out)

def scatter (w base n : ℕ) : Procedure w :=
  ⟨9,5,2,scatterBlock w,fun i => ((![base,base+2*n] i : ℕ) : Word w)⟩

theorem scatter_spec (base : ℕ) (es : List (Record w)) (room : base+2*es.length < 2^w)
    (away : Safe base es) :
    (scatter w base es.length).Spec (fun m => Loaded m base es)
      (fun m o => o=after m (events es)) (4+6*es.length) := by
  intro P R K M pc regs pub out rom data c m entry loaded
  change Fin 9 ↪ Fin P at pc
  change Fin 5 ↪ Fin R at regs
  change Fin 2 → Fin K at pub
  change (scatterBlock w).Installed M pc regs pub out at rom
  change ∀i : Fin 2,M.publicData (pub i)=((![base,base+2*es.length] i : ℕ):Word w) at data
  let boot : Fin 3→Fin P := pc ∘ Fin.castAdd 6
  let loop : Fin 6→Fin P := pc ∘ Fin.natAdd 3
  have hb (i : Fin 3) : M.code (boot i)=head boot regs pub (loop 0) i := by
    simpa [boot,loop,scatter,scatterBlock] using rom (i.castAdd 6)
  have hl (i : Fin 6) : M.code (loop i)=EffectStream.block loop regs out i := by
    simpa [boot,loop,scatter,scatterBlock] using rom (Fin.natAdd 3 i)
  change c.pc=boot 0 at entry
  let c' := ((c.put (boot 1) (regs 0) (base : Word w)).put (boot 2) (regs 1)
    (base+2*es.length : ℕ)).put (loop 0) (regs 4) 1
  have run : advance M.program 3 c m=some (c',m) := by
    simp [advance,Machine.program,entry,hb,head,Instr.run,c',data,Config.put]
  have cur : (c'.reg (regs 0)).val=base := by
    simp (config := {decide:=true}) [c',Config.put,Fin.val_cast_of_lt (by omega : base<2^w)]
  have stop : (c'.reg (regs 1)).val=base+2*es.length := by
    have value : c'.reg (regs 1)=((base+2*es.length:ℕ):Word w) := by
      simp (config := {decide:=true}) [c',Config.put]
    rw [value,Fin.val_cast_of_lt room]
  have one : c'.reg (regs 4)=1 := by simp [c',Config.put]
  have result := advance_trans run (advance_block M loop regs out hl base es c' m rfl cur stop one loaded away)
  exact ⟨3+(1+6*es.length),by omega,_,_,result,endConfig_pc ..,rfl⟩

def procedure (w src tmp n : ℕ) : Procedure w :=
  (PhysicalInputPhases.packing w src tmp (2*n)).seq (scatter w tmp n)

def Input (src tmp : ℕ) (es : List (Record w)) (m : Memory w) :=
  ∀ i<2*es.length, ∀ j<w, m (src+w*i+j)=
    (((packedWord tmp es (tmp+i)).val.testBit (w-1-j)).toNat : Word w)

theorem seed_spec (src tmp : ℕ) (es : List (Record w))
    (apart : tmp+2*es.length≤ src ∨ src+w*(2*es.length)≤tmp)
    (scratch : tmp+2*es.length<2^w) (source : src+w*(2*es.length)<2^w) (safe : Safe tmp es) :
    (procedure w src tmp es.length).Spec
      (Input src tmp es)
      (fun m o => o=after (fillSegment tmp (2*es.length) (packedWord tmp es) m) (events es))
      ((2*es.length)*(5*w+6)+6+(4+6*es.length)) := by
  have pack : (PhysicalInputPhases.packing w src tmp (2*es.length)).Spec (Input src tmp es)
      (fun m o => o=fillSegment tmp (2*es.length) (packedWord tmp es) m)
      ((2*es.length)*(5*w+6)+6) := by
    intro P R K M pc reg pub out rom params c m init input
    change Fin 15 ↪ Fin P at pc
    change Fin 8 ↪ Fin R at reg
    change Fin 4 → Fin K at pub
    change (PackWordBlock.block w).Installed M pc reg pub out at rom
    obtain ⟨last,corr,atExit⟩ := PackWordBoot.generate_disjoint M (PackWordBlock.headPC pc)
      (PackWordBlock.loopPC pc) reg pub out
      (fun i => by simpa only [PackWordBlock.block,PackWordBlock.headPC,Fin.addCases_left] using rom (i.castAdd 10))
      (fun i => by simpa only [PackWordBlock.block,PackWordBlock.loopPC,Fin.addCases_right] using rom (Fin.natAdd 5 i))
      src tmp (2*es.length) (packedWord tmp es) c m init params apart scratch source input
    exact ⟨_,le_rfl,last,_,corr,atExit,rfl⟩
  intro P R K M pc reg pub out rom params c mem entry input
  obtain ⟨t,ht,last,output,run,land,mid,packed,done⟩ := Procedure.Spec.seq pack
    (scatter_spec tmp es scratch safe) (by rintro m _ rfl; exact loaded_fillSegment tmp es m)
    M pc reg pub out rom params c mem entry input
  change output=after mid (events es) at done
  rw [packed] at done
  exact ⟨t,ht,last,output,run,land,done⟩

end ThreeFlat.RAM.EffectSeed

end OAI

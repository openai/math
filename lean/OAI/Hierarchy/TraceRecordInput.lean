import OAI.ThreeFlat.Diagonal.HistogramRegister
import OAI.ThreeFlat.RAM.PackWordBoot
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Mounting the history prefix for all subsequent physical stages

The scanner reads consecutive bit cells of the shared selector into big-endian
histogram words. Its four public operands locate the raw and packed windows and
set the word width. It writes each packed word once and preserves the remaining memory.
-/

noncomputable section
namespace Hierarchy.TraceAdmission

open ThreeFlat Diagonal Diagonal.HistogramRegister
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.ContinuationLink RAM.PhysicalProcedure
open scoped Classical Fin.CommRing

variable {W : ℕ}

/-- Word number `i` of the actual shared bitstring, before validity testing. -/
def inputWord (raw : ℕ → Bool) (i : ℕ) : Word W :=
  MotifBinaryPacking.word W (fun j => raw (W*i+(W-1-j.val)))

theorem inputWord_digit (raw : ℕ → Bool) (i j : ℕ) (hj : j<W) :
    (inputWord (W:=W) raw i).val.testBit (W-1-j)=raw (W*i+j) := by
  let b : Fin W := ⟨W-1-j,by omega⟩
  have h := congrFun ((MotifBinaryPacking.word W).symm_apply_apply
    (fun z : Fin W => raw (W*i+(W-1-z.val)))) b
  change (inputWord raw i).val.testBit (W-1-j)=raw (W*i+(W-1-(W-1-j))) at h
  simpa only [show W-1-(W-1-j)=j by omega] using h

def inputRows (M K : ℕ) (raw : ℕ → Bool) (first : ℕ) : Words M K W :=
  fun i j => inputWord raw (first+i.val*K+j.val)

theorem raw_stage_bits (M K : ℕ) (raw : ℕ → Bool) (first : ℕ) :
    bitTable (inputRows (W:=W) M K raw first) = fun j => raw (W*first+j.val) := by
  funext j
  obtain ⟨⟨u,b⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective u
  change bitTable _ (address i k b)=raw (W*first+(address i k b).val)
  rw [bitTable_at,address_val]
  change (inputWord (W:=W) raw _).val.testBit (W-1-b.val)=_
  rw [inputWord_digit _ _ _ b.isLt]
  congr 1; ring

/-- The parser's view of a stage agrees with the memory words even when the
input string contains an invalid histogram. -/
theorem raw_stage_prefix (raw : ℕ → Bool) (first M K cap : ℕ)
    (room : W*first+M*K*W≤cap) :
    ((List.ofFn (fun i : Fin cap => raw i.val)).drop (W*first)).take (M*K*W)=
      List.ofFn (bitTable (inputRows (W:=W) M K raw first)) := by
  rw [raw_stage_bits]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]

def inputPacker (W src dst count : ℕ) : Procedure W where
  labels := 15
  registers := 8
  slots := 4
  publicData := fun i => ((![src,dst,dst+count,W] i : ℕ) : Word W)
  block := ⟨(0:Fin 5).castAdd 10,fun pc reg pub exit =>
    let boot := (Fin.castAddEmb 10 : Fin 5 ↪ Fin 15).trans pc
    let loop := (Fin.natAddEmb 5 : Fin 10 ↪ Fin 15).trans pc
    Fin.addCases (m:=5) (n:=10) (motive:=fun _ => Instr W _ _ _)
      (PackWordBoot.header boot (loop 0) reg pub)
      (PackWordTable.instruction loop reg exit)⟩

/-- A fifteen-instruction, eight-register program mounts the whole physical
histogram table; the constant factors here count native RAM steps. -/
theorem inputPacker_run (src dst count : ℕ) (raw : ℕ→Bool)
    (apart : dst+count ≤ src ∨ src+W*count ≤ dst) (dstFit : dst+count<2^W) (srcFit : src+W*count<2^W) :
    (inputPacker W src dst count).Spec
      (fun m => ∀ i<W*count, m (src+i)=((raw i).toNat:Word W))
      (fun m out => out=fillSegment dst count (fun j=>inputWord raw (j-dst)) m)
      (count*(5*W+6)+6) := by
  intro P R K M pc reg pub exit installed data c m entry load
  let boot := (Fin.castAddEmb 10 : Fin 5 ↪ Fin 15).trans pc
  let loop := (Fin.natAddEmb 5 : Fin 10 ↪ Fin 15).trans pc
  have head (i) : M.code (boot i)=PackWordBoot.header boot (loop 0) reg pub i := by
    change M.code (pc (i.castAdd 10))=_
    simpa only [inputPacker,boot,loop,Fin.addCases_left] using installed (i.castAdd 10)
  have body (i) : M.code (loop i)=PackWordTable.instruction loop reg exit i := by
    change M.code (pc (Fin.natAdd 5 i))=_
    simpa only [inputPacker,boot,loop,Fin.addCases_right] using installed (Fin.natAdd 5 i)
  obtain ⟨out,run,stop⟩ := PackWordBoot.generate_disjoint M boot loop reg pub exit head body
    src dst count (fun j => inputWord raw (j-dst)) c m entry data apart dstFit srcFit (by
      intro i hi j hj
      rw [Nat.add_sub_cancel_left,inputWord_digit _ _ _ hj,Nat.add_assoc]
      exact load _ (by have h := Nat.mul_le_mul_left W (Nat.succ_le_of_lt hi); rw [Nat.mul_succ] at h; omega))
  exact ⟨_,le_rfl,out,_,run,stop,rfl⟩

theorem inputPacker_row (raw : ℕ→Bool) (dst count first M K : ℕ) (fit : first+M*K≤count)
    (mem : Memory W) (i : Fin M) (k : Fin K) :
    fillSegment dst count (fun j=>inputWord raw (j-dst)) mem (dst+first+i.val*K+k.val)=
      inputRows M K raw first i k := by
  have h : i.val*K+k.val<M*K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    have := k.isLt
    omega
  simp [fillSegment,inputRows,show dst≤dst+first+i.val*K+k.val by omega,
    show dst+first+i.val*K+k.val<dst+count by omega,
    show dst+first+i.val*K+k.val-dst=first+i.val*K+k.val by omega]


end Hierarchy.TraceAdmission

end
end OAI

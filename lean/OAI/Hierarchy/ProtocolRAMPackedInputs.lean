import OAI.Hierarchy.ProtocolRAMTranslatedKey
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # Word columns for the weighted counter after genuine supergroup remapping -/

namespace Hierarchy.ProtocolRAMPackedInputs

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProtocolRAMGeneratedWrite ProtocolRAMTranslatedKey
open scoped Fin.CommRing

variable {W N w menu gb : ℕ}

def triple : Expr := .op .add (.op .add .row .row) .row
def spreadAddress (out : ℕ) : Expr := .op .add (.lit out) triple
def groupSpread (W scratch out N : ℕ) (packed : Bank) :=
  ProtocolRAMGeneratedWrite.program W scratch (scratch+N) N (spreadAddress out) (.lookup packed .row)

theorem eval_triple (m : Memory W) (i : ℕ) : triple.eval m (i:Word W)=((3*i:ℕ):Word W) := by
  simp only [triple,Expr.eval,RowOp.opcode,BinaryOp.eval,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem spread (scratch out : ℕ) (packed : Bank) (g : Fin N→ℕ) (mem : Memory W)
    (safe : packed.Fits W scratch) (room : out+3*N<2^W) (apart : scratch+2*N ≤ out)
    (groups : ∀i : Fin N,packed.read mem (i.val:Word W)=(g i:Word W)) :
    ∃ after,(groupSpread W scratch out N packed).Exec mem after
      (ProtocolRAMGeneratedWrite.work N (spreadAddress out) (.lookup packed .row)) ∧
      (∀i : Fin N,after (out+3*i.val)=(g i:Word W)) ∧ ∀ a < scratch,after a=mem a := by
  let dst (i : Fin N) := out+3*i.val
  let src (i : Fin N) : Word W := g i
  refine ⟨ProtocolRAMGeneratedWrite.image scratch (scratch+N) (spreadAddress out) (.lookup packed .row) dst src mem,?_,?_,?_⟩
  · apply ProtocolRAMGeneratedWrite.run
    · repeat' constructor
    · exact ⟨safe,trivial⟩
    · omega
    · omega
    · intro i
      change (out:Word W)+triple.eval mem (i.val:Word W)=((out+3*i.val:ℕ):Word W)
      rw [eval_triple,Nat.cast_add]
    · exact groups
    · intro i;dsimp [dst];have := i.isLt;omega
    · intro i j;dsimp [dst];have := i.isLt;omega
    · intro i j;dsimp [dst];have := i.isLt;omega
  · intro i
    refine ProtocolRAMGeneratedWrite.read _ _ _ _ dst src mem ?_ i
    intro j k eq;apply Fin.ext;dsimp [dst] at eq;omega
  · intro a ha
    exact ProtocolRAMGeneratedWrite.frame _ _ _ _ dst src mem _ (fun i=>by dsimp [dst];omega)
      (.inl ha) (.inl (by omega))

def weight (width weights : Bank) : Expr := .lookup weights (.lookup width triple)

def keyWord (width packed bias classes : Bank) : Expr :=
  .op .add (.lookup bias (.lookup packed .row)) (.lookup classes (.lookup width triple))

/-- The one-dimensional public directory stores g*(menu+1); bank reads mask the word
to the directory width. Both width lookups are from the previously mounted report ROM. -/
theorem eval_key (rows : Fin N→ProtocolRAMEmit.Row) (mem : Memory W) (width packed bias classes : Bank)
    (readWidth : ∀i : Fin N,width.read mem ((3*i.val:ℕ):Word W)=((rows i).width:Word W))
    (readGroup : ∀i : Fin N,packed.read mem (i.val:Word W)=((rows i).group:Word W))
    (directory : ∀a : Word W,bias.read mem a=(((a.val%(2^gb))*(menu+1):ℕ):Word W))
    (classData : ∀i : Fin N,classes.read mem ((rows i).width:Word W)=((classOf rows w menu i).val:Word W))
    (i : Fin N) : (keyWord width packed bias classes).eval mem (i.val:Word W)=
      ((rowKey W gb w menu rows i).val:Word W) := by
  change bias.read mem (packed.read mem (i.val:Word W))+
    classes.read mem (width.read mem (triple.eval mem (i.val:Word W)))=_
  rw [eval_triple,readGroup,readWidth,directory,classData]
  change _=(((classOf rows w menu i).val+(menu+1)*(owner W gb (rows i).group).val:ℕ):Word W)
  rw [Nat.mul_comm (menu+1),Nat.add_comm (classOf rows w menu i).val,Nat.cast_add]; rfl

theorem eval_weight (rows : Fin N→ProtocolRAMEmit.Row) (mem : Memory W) (width weights : Bank)
    (readWidth : ∀i : Fin N,width.read mem ((3*i.val:ℕ):Word W)=((rows i).width:Word W))
    (counts : ∀i : Fin N,weights.read mem ((rows i).width:Word W)=(ProtocolRAMReportedPorts.pieces rows w i:Word W))
    (i : Fin N) : (weight width weights).eval mem (i.val:Word W)=(ProtocolRAMReportedPorts.pieces rows w i:Word W) := by
  change weights.read mem (width.read mem (triple.eval mem (i.val:Word W)))=_
  rw [eval_triple,readWidth,counts]

def terms (width packed bias classes weights : Bank) : List Expr := [weight width weights,keyWord width packed bias classes]

theorem columns (out : ℕ) (width packed bias classes weights : Bank) (rows : Fin N→ProtocolRAMEmit.Row) (mem : Memory W)
    (room : out+2*N<2^W)
    (wf : width.Fits W out) (pf : packed.Fits W out) (bf : bias.Fits W out) (cf : classes.Fits W out) (xf : weights.Fits W out)
    (readWidth : ∀i : Fin N,width.read mem ((3*i.val:ℕ):Word W)=((rows i).width:Word W))
    (readGroup : ∀i : Fin N,packed.read mem (i.val:Word W)=((rows i).group:Word W))
    (directory : ∀a : Word W,bias.read mem a=(((a.val%(2^gb))*(menu+1):ℕ):Word W))
    (classData : ∀i : Fin N,classes.read mem ((rows i).width:Word W)=((classOf rows w menu i).val:Word W))
    (counts : ∀i : Fin N,weights.read mem ((rows i).width:Word W)=(ProtocolRAMReportedPorts.pieces rows w i:Word W)) :
    let xs := terms width packed bias classes weights
    let ps := ProbeStage.Native.columns N out xs
    let after := ProtocolRAM.result ps mem
    (ProtocolRAM.program W ps).Exec mem after (ProtocolRAM.clock ps) ∧
    (∀i : Fin N,after (out+i.val)=(ProtocolRAMReportedPorts.pieces rows w i:Word W) ∧
      after (out+N+i.val)=((rowKey W gb w menu rows i).val:Word W)) ∧ (∀ a < out,after a=mem a) ∧
      ProtocolRAM.clock ps≤4+2*(4+N*(2*31+4)) := by
  intro xs ps after
  have readers (x : Expr) (hx : x∈xs) : x.Fits W out := by
    change x∈[weight width weights,keyWord width packed bias classes] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact ⟨xf,wf,⟨trivial,trivial⟩,trivial⟩
    · exact ⟨⟨bf,pf,trivial⟩,cf,wf,⟨trivial,trivial⟩,trivial⟩
  refine ⟨ProbeStage.Native.columns_exec xs mem (ProbeStage.Native.columns_safe xs (le_refl out) readers room),?_,?_,?_⟩
  · intro i
    constructor
    · simpa only [Nat.zero_mul,Nat.add_zero] using (ProbeStage.Native.columns_read xs mem (le_refl out) readers 0
        (by change 0 < 2; decide) i).trans (eval_weight rows mem width weights readWidth counts i)
    · simpa only [Nat.one_mul] using (ProbeStage.Native.columns_read xs mem (le_refl out) readers 1
        (by change 1 < 2; decide) i).trans (eval_key rows mem width packed bias classes readWidth readGroup directory classData i)
  · intro a ha
    exact ProtocolRAM.result_below ps mem a (fun p hp=>ha.trans_le (ProbeStage.Native.columns_below xs p hp))
  · apply ProbeStage.Native.columns_clock N out 31 xs
    intro e he
    change e∈[weight width weights,keyWord width packed bias classes] at he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · change 18 ≤ 31
      decide
    · exact le_rfl


end Hierarchy.ProtocolRAMPackedInputs

end OAI

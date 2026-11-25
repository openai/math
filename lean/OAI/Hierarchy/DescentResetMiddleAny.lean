import OAI.Hierarchy.DescentResetRowsAfterSolver
import OAI.Hierarchy.DescentExteriorRotationWord

namespace OAI
/-! # The measured matrix and field schedule terminates on every previous bit pattern -/
namespace Hierarchy.DescentGLPacked.BankImage.Dated
open DescentGLPacked DescentGL DescentGLNielsen DescentGLControlCode DescentPackedColony.Phase.Arena
open DescentSixParty.PackedFlow DescentSIMDLookup DescentColonies DescentPackedWalsh
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {D H h l b w : ℕ}

def middle (C : Chart) (base solve fresh : ℕ) (counts : Bank) (pair : Fin D→Bank) (H h l w : ℕ) (pos : 0<b) :=
  let d:=h+l
  let n:=(2^d)^d
  let I:=controlImage (h:=h) (l:=l) (w:=w) base pos
  let B:=routes C (((1+D)+d)*H) h l b w
  let T:=DescentExteriorRotationWord.resetSheet d w fresh
  let arg:=DescentExteriorRotationWord.reset (k:=d) ⟨fresh,d*d⟩ ⟨fresh+n,d*d⟩ (fun i=>PhysicalTrajectory.pointer d solve i.val)
  ((I.program.seq B.program).seq (gathered C base solve counts pair H h l w)).seq
    (T.program.seq (scan w (fresh+n+n) 1 arg))

def middleTime (C : Chart) (base solve : ℕ) (counts : Bank) (pair : Fin D→Bank) (H h l w : ℕ) (pos : 0<b) :=
  let d:=h+l
  let n:=(2^d)^d
  let I:=controlImage (h:=h) (l:=l) (w:=w) base pos
  let B:=routes C (((1+D)+d)*H) h l b w
  ((8+10*(I.length+B.length))+gatherFee C base solve counts pair H h l)+((4+10*(n+n))+(20+24*d))

local notation "d" => h+l
local notation "channels" => (1+D)+d

theorem middle_any_footprint (C : Chart) (base solve fresh : ℕ) (counts : Bank) (pair : Fin D→Bank) (positive : 0<b)
    (mem : Memory w) (afterSolve : PhysicalTrajectory.outputBase d solve+2^d≤base)
    (loadLow : counts.Fits w base) (pairLow : ∀i,(pair i).Fits w base)
    (valid : Size C (channels*H) h l b w) (controlEnd : wordEnd base h l≤C.input.base)
    (gap : C.input.base+C.input.size≤C.flags)
    (powerFit : (powers base d).Fits w C.input.base)
    (ofsFit : (cols base d).offsets.Fits w C.input.base)
    (swFit : (cols base d).switches.Fits w C.input.base)
    (planeFit : ∀i : Fin d,(Original.bank (plane base d) h i).Fits w C.input.base)
    (ptrLow : ∀i : Fin d,PhysicalTrajectory.pointer d solve i.val<fresh)
    (space : fresh+(2^d)^d+(2^d)^d+1<2^w) :
    ∃out,(middle C base solve fresh counts pair H h l w positive).Exec mem out (middleTime C base solve counts pair H h l w positive) ∧
      CheapCode (middle C base solve fresh counts pair H h l w positive) ∧
      ∀x,(x<base ∨ C.heap d+(schedule d).length*C.page≤x) →
        (x<fresh ∨ fresh+(2^d)^d+(2^d)^d+1≤x) → out x=mem x := by
  let I:=controlImage (h:=h) (l:=l) (w:=w) base positive
  let B:=routes C (channels*H) h l b w
  let banks:=fieldBanks D h l counts pair (plane base d)
  let cells:=H*2^h
  let n:=(schedule d).length
  let ps:=steps (C.chosen d) (channels*H) (2^h) 0 n
  let gs:=DescentPackedFlowBatch.passes C.input.base cells cells (channelTerm banks) 0 channels
  have first:base≤wordEnd base h l:=by dsimp [wordEnd,plane];omega
  have top:=valid.top
  have controls:=valid.controls
  have start:C.start≤C.heap d:=Nat.le_add_right ..
  have aroom:I.low+I.length<2^w:=by change base+(wordEnd base h l-base)<2^w;omega
  have broom:B.low+B.length<2^w:=by change C.start+(C.heap d-C.start)<2^w;omega
  obtain ⟨install,_,_,installedFrame,installCheap,_⟩:=I.pair B mem (.inl (show wordEnd base h l≤C.start by omega)) aroom broom
  let mid:=B.output (I.output mem)
  have widen {t : Bank} (lo:t.Fits w base) : t.Fits w C.input.base:=⟨lo.1,lo.2.1,lo.2.2.trans (first.trans controlEnd)⟩
  have fits (j) (live : j<channels) : (channelTerm banks j).Fits w C.input.base := by
    let i : Fin channels:=⟨j,live⟩
    suffices ok:(banks i).Fits w C.input.base by simp only [channelTerm,dite_eq_left live,Expr.Fits];exact ⟨ok,trivial⟩
    obtain ⟨(a|t),eq⟩:=finSumFinEquiv.surjective i
    · obtain ⟨(s|q),rfl⟩:=finSumFinEquiv.surjective a
      · simpa [banks,fieldBanks,←eq] using widen loadLow
      · simpa [banks,fieldBanks,←eq] using widen (pairLow q)
    · simpa [banks,fieldBanks,←eq] using planeFit t
  have cellsFit:C.input.base+channels*cells<2^w:=by
    have z:=valid.inputSize
    rw [Nat.mul_assoc] at z
    have narrow:=valid.input.2.2
    dsimp [cells]
    omega
  obtain ⟨gather,_,gatherLow⟩:=DescentPackedFlowBatch.execute C.input.base cells cells channels (channelTerm banks) mid fits cellsFit le_rfl
  let gmem:=result gs mid
  have above (i : Fin d) : PhysicalTrajectory.pointer d solve i.val<base := by
    have hi:=Nat.mul_le_mul_right (3*2^d+1) i.isLt
    rw [Nat.succ_mul] at hi
    dsimp [PhysicalTrajectory.pointer,PhysicalTrajectory.outputBase,DescentGL.RowStageRAM.placed] at afterSolve ⊢
    omega
  have widenAgain {t : Bank} (lo:t.Fits w C.input.base) : t.Fits w C.flags :=
    ⟨lo.1,lo.2.1,lo.2.2.trans ((Nat.le_add_right ..).trans gap)⟩
  have hw:1<2^w:=by have nonzero:0<(powers base d).size:=powerFit.1;omega
  have op:(key base solve d).Fits w C.flags:=DescentExteriorSelectedMatrix.expr_fits _ (widenAgain powerFit) hw d _
    (fun j=>(above j).trans_le ((first.trans controlEnd).trans ((Nat.le_add_right ..).trans gap)))
  have ef:((cols base d).expr (key base solve d)).Fits w C.flags:=⟨widenAgain swFit,op,widenAgain ofsFit,trivial⟩
  have head:C.flags+n<2^w:=controls.trans_lt (((C.page_low (6*n)).trans (Nat.le_add_right ..)).trans_lt valid.top)
  let fm:=image C.flags n ((cols base d).expr (key base solve d)) gmem
  have flags : (scan w C.flags n ((cols base d).expr (key base solve d))).Exec gmem fm _ :=
    scan_exec C.flags n _ gmem ef head
  have run:=execution (C.chosen d) (hardware C valid) fm 0 n (by omega)
  obtain ⟨save,cheapSave,_,saveFrame⟩:=DescentExteriorRotationWord.reset_fresh d fresh (fun i=>PhysicalTrajectory.pointer d solve i.val) (result ps fm) ptrLow space
  have scheduled : ((I.program.seq B.program).seq (gathered C base solve counts pair H h l w)).Exec
      mem (result ps fm) ((8+10*(I.length+B.length))+gatherFee C base solve counts pair H h l) :=
    install.then (gather.then (flags.then run.1))
  refine ⟨_,Procedure.Exec.then scheduled save,
    cheap_seq (cheap_seq installCheap (cheap_seq (@ProtocolRAM.program_cheap _ _) (cheap_seq (@scan_cheap _ _ _ _) run.2))) cheapSave,?_⟩

  intro x oldRegion beforeSave
  apply (saveFrame x beforeSave).trans
  have flagLow : base≤C.flags := first.trans (controlEnd.trans ((Nat.le_add_right ..).trans gap))
  have flagHigh : C.flags≤C.heap d := by omega
  have coverage : channels*cells≤C.input.size := by simpa only [cells,Nat.mul_assoc] using valid.inputSize
  have beforeChart : base≤C.start := by omega
  rcases oldRegion with lo|hi
  · exact (reset_frames C valid _ gmem x (.inl (lo.trans_le flagLow))).trans
      ((gatherLow x (lo.trans_le (first.trans controlEnd))).trans
        (installedFrame x (.inl lo) (.inl (lo.trans_le beforeChart))))
  · have aboveGather : C.input.base+(0+channels)*cells≤x := by
      rw [Nat.zero_add]
      omega
    exact (reset_frames C valid _ gmem x (.inr hi)).trans
      ((DescentPackedFlowBatch.above C.input.base cells cells (channelTerm banks) mid 0 channels x
        le_rfl aboveGather).trans
        (installedFrame x (.inr (show wordEnd base h l≤x by omega)) (.inr (show C.heap d≤x by omega))))

theorem middle_any (C : Chart) (base solve fresh : ℕ) (counts : Bank) (pair : Fin D→Bank) (positive : 0<b)
    (mem : Memory w) (afterSolve : PhysicalTrajectory.outputBase d solve+2^d≤base)
    (loadLow : counts.Fits w base) (pairLow : ∀i,(pair i).Fits w base)
    (valid : Size C (channels*H) h l b w) (controlEnd : wordEnd base h l≤C.input.base)
    (gap : C.input.base+C.input.size≤C.flags)
    (powerFit : (powers base d).Fits w C.input.base)
    (ofsFit : (cols base d).offsets.Fits w C.input.base)
    (swFit : (cols base d).switches.Fits w C.input.base)
    (planeFit : ∀i : Fin d,(Original.bank (plane base d) h i).Fits w C.input.base)
    (ptrLow : ∀i : Fin d,PhysicalTrajectory.pointer d solve i.val<fresh)
    (space : fresh+(2^d)^d+(2^d)^d+1<2^w) :
    ∃out,(middle C base solve fresh counts pair H h l w positive).Exec mem out (middleTime C base solve counts pair H h l w positive) ∧
      CheapCode (middle C base solve fresh counts pair H h l w positive) := by
  obtain ⟨out,ran,cheap,_⟩:=middle_any_footprint C base solve fresh counts pair positive mem afterSolve loadLow pairLow valid
    controlEnd gap powerFit ofsFit swFit planeFit ptrLow space
  exact ⟨out,ran,cheap⟩

theorem middle_any_framed (C : Chart) (base solve fresh : ℕ) (counts : Bank) (pair : Fin D→Bank) (positive : 0<b)
    (mem : Memory w) (afterSolve : PhysicalTrajectory.outputBase d solve+2^d≤base)
    (loadLow : counts.Fits w base) (pairLow : ∀i,(pair i).Fits w base)
    (valid : Size C (channels*H) h l b w) (controlEnd : wordEnd base h l≤C.input.base)
    (gap : C.input.base+C.input.size≤C.flags)
    (powerFit : (powers base d).Fits w C.input.base)
    (ofsFit : (cols base d).offsets.Fits w C.input.base)
    (swFit : (cols base d).switches.Fits w C.input.base)
    (planeFit : ∀i : Fin d,(Original.bank (plane base d) h i).Fits w C.input.base)
    (ptrLow : ∀i : Fin d,PhysicalTrajectory.pointer d solve i.val<fresh)
    (space : fresh+(2^d)^d+(2^d)^d+1<2^w)
    (ordered : C.heap d+(schedule d).length*C.page≤fresh) :
    ∃out,(middle C base solve fresh counts pair H h l w positive).Exec mem out (middleTime C base solve counts pair H h l w positive) ∧
      CheapCode (middle C base solve fresh counts pair H h l w positive) ∧
      ∀x,x<base ∨ fresh+2*((2^d)^d)+1≤x → out x=mem x := by
  obtain ⟨out,ran,cheap,frame⟩:=middle_any_footprint C base solve fresh counts pair positive mem afterSolve loadLow pairLow valid
    controlEnd gap powerFit ofsFit swFit planeFit ptrLow space
  refine ⟨out,ran,cheap,?_⟩
  intro x hx
  have first : base≤wordEnd base h l := by dsimp [wordEnd,plane];omega
  have controls:=valid.controls
  have start : C.start≤C.heap d:=Nat.le_add_right ..
  rcases hx with lo|hi
  · exact frame x (.inl lo) (.inl (by omega))
  · exact frame x (.inr (by omega)) (.inr (by omega))

end
end Hierarchy.DescentGLPacked.BankImage.Dated

end OAI

import OAI.Hierarchy.DescentResetMeasuredChannels
import OAI.Hierarchy.DescentResetDatedControls

namespace OAI
/-! # From true selected basis rows to every remixed reset operand on the same RAM -/
namespace Hierarchy.DescentGLPacked.BankImage.Dated
open DescentGLPacked DescentGL DescentGLNielsen DescentGLControlCode DescentPackedColony.Phase.Arena
open DescentSixParty.PackedFlow DescentSIMDLookup DescentColonies DescentPackedWalsh
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {D H h l b w : ℕ}
def key (base solve : ℕ) (d : ℕ) := DescentExteriorSelectedMatrix.expr (powers base d) d
  (fun i : Fin d=>PhysicalTrajectory.pointer d solve i.val)

local notation "d" => h+l
local notation "channels" => (1+D)+d

def gathered (C : Chart) (base solve : ℕ) (counts : Bank) (pair : Fin D→Bank) (H h l w : ℕ) :=
  let banks:=fieldBanks D h l counts pair (plane base (h+l))
  let rows:=H*2^h
  let n:=(schedule (h+l)).length
  let gs:=DescentPackedFlowBatch.passes C.input.base rows rows (channelTerm banks) 0 ((1+D)+(h+l))
  let ps:=steps (C.chosen (h+l)) (((1+D)+(h+l))*H) (2^h) 0 n
  (program w gs).seq ((scan w C.flags n ((cols base (h+l)).expr (key base solve (h+l)))).seq (program w ps))

def gatherFee (C : Chart) (base solve : ℕ) (counts : Bank) (pair : Fin D→Bank) (H h l : ℕ) :=
  let banks:=fieldBanks D h l counts pair (plane base (h+l))
  let rows:=H*2^h
  let n:=(schedule (h+l)).length
  let gs:=DescentPackedFlowBatch.passes C.input.base rows rows (channelTerm banks) 0 ((1+D)+(h+l))
  let ps:=steps (C.chosen (h+l)) (((1+D)+(h+l))*H) (2^h) 0 n
  clock gs+((4+n*(2*((cols base (h+l)).expr (key base solve (h+l))).work+4))+clock ps)

theorem selected_fields (C : Chart) (base solve : ℕ) (counts : Bank) (pair : Fin D→Bank)
    (loads : Fin H→Block d→Cell b) (flows : Fin D→Fin H→Block d→Cell b)
    (L : DescentGL.Layout d) (mem : Memory w)
    (selected : ∀i : Fin d,mem (PhysicalTrajectory.pointer d solve i.val)=((rowIndex d (rowFunctional L i)).val:Word w))
    (afterSolve : PhysicalTrajectory.outputBase d solve+2^d≤base)
    (loadWords : Dense (h:=h) (l:=l) counts.base loads mem)
    (flowWords : ∀i,Dense (h:=h) (l:=l) (pair i).base (flows i) mem)
    (loadSize : H*2^h≤counts.size) (pairSize : ∀i,H*2^h≤(pair i).size)
    (loadLow : counts.Fits w base) (pairLow : ∀i,(pair i).Fits w base)
    (valid : Size C (channels*H) h l b w) (positive : 0<b)
    (controlEnd : wordEnd base h l≤C.input.base) (gap : C.input.base+C.input.size≤C.flags)
    (powerFit : (powers base d).Fits w C.input.base)
    (ofsFit : (cols base d).offsets.Fits w C.input.base)
    (swFit : (cols base d).switches.Fits w C.input.base)
    (planeFit : ∀i : Fin d,(Original.bank (plane base d) h i).Fits w C.input.base) :
    let A:=controlImage (h:=h) (l:=l) (w:=w) base positive
    let B:=routes C (channels*H) h l b w
    let ps:=gathered C base solve counts pair H h l w
    ∃dst,((A.program.seq B.program).seq ps).Exec mem dst
        ((8+10*(A.length+B.length))+gatherFee C base solve counts pair H h l) ∧
      CheapCode ((A.program.seq B.program).seq ps) ∧
      (∀i,Dense (h:=h) (l:=l) (slice (((C.chosen d).bank (schedule d).length).base) H (2^h) i)
        (fun v x=>Channels.values loads flows positive i v ((rearrange L).symm x)) dst) ∧
      ∀a,a<base ∨ C.heap d+(schedule d).length*C.page≤a→dst a=mem a := by
  let A:=controlImage (h:=h) (l:=l) (w:=w) base positive
  let B:=routes C (channels*H) h l b w
  let mid:=B.output (A.output mem)
  have first : base≤wordEnd base h l := by dsimp [wordEnd,plane];omega
  have small:=valid.top
  have atFlags:=valid.controls
  have place:C.start≤C.heap d:=Nat.le_add_right ..
  have firstSmall:A.low+A.length<2^w:=by change base+(wordEnd base h l-base)<2^w;omega
  have routeSmall:B.low+B.length<2^w:=by change C.start+(C.heap d-C.start)<2^w;omega
  obtain ⟨issued,kept,routesOK,both,cheap,_⟩:=A.pair B mem
    (.inl (show wordEnd base h l≤C.start by omega)) firstSmall routeSmall
  have prior (a : ℕ) (lt : a<base) : mid a=mem a:=both a (.inl lt) (.inl (show a<C.start by omega))
  have above (i : Fin d) : PhysicalTrajectory.pointer d solve i.val<base := by
    have hi:=Nat.mul_le_mul_right (3*2^d+1) i.isLt
    rw [Nat.succ_mul] at hi
    dsimp [PhysicalTrajectory.pointer,PhysicalTrajectory.outputBase,DescentGL.RowStageRAM.placed] at afterSolve ⊢
    omega
  obtain ⟨power,static,planes⟩:=control_reads base positive mid kept
  have keysRoom : keys d≤(powers base d).size := Nat.le_pow_clog (by decide) _
  have keysPositive : 0<keys d := pow_pos (Nat.two_pow_pos _) _
  have hw : 1<2^w := (show 1≤keys d by omega).trans_lt (keysRoom.trans_lt powerFit.2.1)
  have keyWords:=from_rows (cols base d) (powers base d) (fun j=>PhysicalTrajectory.pointer d solve j.val)
    L C.input.base powerFit (Nat.le_pow_clog (by decide) _) hw (fun j=>(above j).trans_le (first.trans controlEnd))
    mid power (fun j=>(prior _ (above j)).trans (selected j)) static
  have preserve {bank : Bank} {X : Fin H→Block d→Cell b} (low : bank.Fits w base) (cover : H*2^h≤bank.size)
      (words : Dense (h:=h) (l:=l) bank.base X mem) : Dense (h:=h) (l:=l) bank.base X mid := by
    intro p
    have less : (row H _ _ p).val < H*2^h :=
      (row H _ _ p).isLt.trans_le (le_of_eq (congrArg (H * ·) (chunk_count h l)))
    exact (prior _ (by have :=low.2.2;omega)).trans (words p)
  have widen {B : Bank} (old : B.Fits w base) : B.Fits w C.input.base :=
    ⟨old.1,old.2.1,old.2.2.trans (first.trans controlEnd)⟩
  obtain ⟨dst,run,cheap',done,frame⟩:=Channels.after_data C valid (cols base d) (rowName d) (key base solve d)
    L ⟨keyWords.1,ofsFit,swFit⟩ (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)
    mid static keyWords.2.2.1 counts pair loads flows (preserve loadLow loadSize loadWords)
    (fun i=>preserve (pairLow i) (pairSize i) (flowWords i)) ⟨widen loadLow,loadSize⟩
    (fun i=>⟨widen (pairLow i),pairSize i⟩) (plane base d) positive planeFit planes gap
    (route_reads C mid routesOK)
  refine ⟨dst,issued.then run,cheap_seq cheap cheap',done,?_⟩
  intro a bounds
  rcases bounds with lo|hi
  · exact (frame a (.inl (lo.trans_le (first.trans controlEnd)))).trans (prior a lo)
  · exact (frame a (.inr hi)).trans (both a (.inr (show wordEnd base h l≤a by omega)) (.inr (show C.heap d≤a by omega)))

end
end Hierarchy.DescentGLPacked.BankImage.Dated

end OAI

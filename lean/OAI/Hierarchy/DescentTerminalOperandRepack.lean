import OAI.Hierarchy.DescentOverlapTariff
import OAI.Hierarchy.DescentTerminalPointerGather
import OAI.Hierarchy.DescentTerminalPassNames

namespace OAI
/-! # One shared table reblocks all previous pointer strips to the terminal host order -/
namespace Hierarchy.DescentTerminalOperandRepack
open DescentSIMDLookup DescentSIMDLookup.Overlap DescentTerminalPointerDigits DescentOrdinaryAtomFieldRAM.ROM
open DescentStaticWordColumn ProtocolRAM DescentPackedZip DescentColonies.SplitRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {n w:ℕ} (root H G M a:ℕ) (source:Fin n→Bank)
local notation "out_" => dest root H G M G a
local notation "R" => rows H G G
local notation "probe" => fun j:Fin n=>body root H G M G a (source j)
local notation "passes_" => Gather.reads out_ R probe
local notation "tab" => tables root H G M G a w
local notation "installed" => seeded root H G M G a
def program (w:ℕ) := (tables root H G M G a w).seq (ProtocolRAM.program w passes_)
def output (m:Memory w) := ProtocolRAM.result passes_ (installed m)
def clocks := (8+10*(out_-root))+ProtocolRAM.clock passes_
def endAddress (n root H G M a:ℕ) :=
  dest root H G M G a+n*rows H G G+2^Nat.clog 2 (rows H G G)
def bank (root H G M a:ℕ) (j:Fin n) := Gather.banks (L:=n) (dest root H G M G a) (rows H G G) j

theorem legal (room:endAddress n root H G M a<2^w) (j:Fin n) :
    (bank root H G M a j).Fits w (endAddress n root H G M a) ∧ R≤(bank root H G M a j).size := by
  have pos:=Nat.two_pow_pos (Nat.clog 2 R)
  have idx:=Nat.mul_le_mul_right R j.isLt.le
  have le:(bank root H G M a j).base+(bank root H G M a j).size≤endAddress n root H G M a:=by
    change out_+j.val*R+2^Nat.clog 2 R≤out_+n*R+2^Nat.clog 2 R
    omega
  exact ⟨⟨pos,((Nat.le_add_left _ _).trans le).trans_lt room,le⟩,Nat.le_pow_clog (by decide) _⟩

variable (m:Memory w) (prior:∀j,(source j).Fits w root) (room:endAddress n root H G M a<2^w)

include prior room in
theorem any :
    (program root H G M a source w).Exec m (output root H G M a source m) (clocks root H G M a source) ∧
    CheapCode (program root H G M a source w) ∧
    (∀v,v<root ∨ endAddress n root H G M a≤v→ output root H G M a source m v=m v) ∧
    ∀j (r:Fin R),output root H G M a source m ((bank root H G M a j).base+r.val)=
      (probe j).eval (installed m) (r.val:Word w) := by
  have origin:root≤out_:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have cap:=Nat.le_pow_clog (by decide : 1<2) R
  have finish_:Overlap.finish root H G M G a<2^w:=by
    change out_+R<_;unfold endAddress at room;omega
  have ends:out_+n*R<2^w:=by unfold endAddress at room;omega
  obtain ⟨mount,pf,df,_,_,frame⟩:=resident root m finish_
  have fits (j): (probe j).Fits w out_:=by
    have sh: (source j).Fits w out_:=⟨(prior j).1,(prior j).2.1,(prior j).2.2.trans origin⟩
    apply fits_total
    intro k
    exact ⟨⟨pf _,trivial⟩,trivial,trivial,df _,⟨pf _,trivial⟩,sh,pf _,trivial⟩
  have read:=Gather.fetch out_ R probe (installed m) fits ends
  have cheap:CheapCode tab:=cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _) (DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _)
  refine ⟨mount.then read.1,cheap_seq cheap read.2.1,?_,read.2.2.1⟩
  intro v away
  have wrote:=read.2.2.2 v (by unfold endAddress at away;rcases away with l|r <;> omega)
  exact wrote.trans (frame v (by unfold endAddress at away;rcases away with l|r <;> omega))

include prior room in
/-- Only the shared lookup setup touches the shifted concatenation table. Each
issued strip reads the original same-index strip, even at incomplete last input groups. -/
theorem issued (positive:0<M) (values:Fin n→Fin H→Fin G→Cell a)
    (size:∀j,rows H G M≤(source j).size)
    (raw:∀j,∀t:Row H G M,m ((source j).base+(row H G M t).val)=((data (values j) t).val:Word w))
    (j:Fin n) (t:Row H G G) :
    output root H G M a source m ((bank root H G M a j).base+(row H G G t).val)=
      ((data (values j) t).val:Word w) := by
  have size_:Overlap.finish root H G M G a<2^w:=by
    have cap := Nat.le_pow_clog (by decide : 1<2) R
    change out_+R<_
    unfold endAddress at room
    omega
  have original:=Overlap.read root (source j) m (values j) positive (prior j) (size j) (raw j) size_ t
  rw [Overlap.result,ProtocolRAMGeneratedWrite.read_image out_ R (probe j) (installed m)
    (row H G G t)] at original
  exact ((any root H G M a source m prior room).2.2.2 j (row H G G t)).trans original

end
end Hierarchy.DescentTerminalOperandRepack

end OAI

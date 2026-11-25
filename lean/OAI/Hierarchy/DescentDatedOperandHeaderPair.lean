import OAI.Hierarchy.DescentDatedOperandOriginalHeads
import OAI.Hierarchy.DescentDatedOperandMeasuredRead

namespace OAI
/-! # The two actual compact-node dictionaries at an ordinary dated operand -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOperandStateBanks ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "g" => v.ticketReadGeometry
local notation "l" => v.resolver
local notation "M" => (l).lanes
local notation "a" => (l).size+2
local notation "b" => v.bornBook.bits
local notation "N" => (l).nodes

def previousAt (floor : ℕ) (j : Fin (l).jobs) (f : Fin 4) : Bank :=
  let (block,_,arg):=(l).index.symm j
  (v.nativeArgs floor).previous block (page (f.castLE (by decide : 4≤7)) arg)
def mouthBankAt (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
    (j : Fin (l).jobs) (f : Fin 3) : Bank :=
  let (block,_,arg):=(l).index.symm j
  v.originMouthBank floor mat.newBlocks (arg.cast (shape.operands.trans mat.newArgs.symm)) f (block.cast shape.blocks)

variable {w : ℕ} (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "base" => v.operandOldHeaderStart floor
local notation "middle" => v.operandMouthHeaderStart floor
local notation "top" => v.operandHeaderEnd floor

theorem header_pair_issued (m : Memory w)
    (prior : Fin (l).jobs → Fin 4 → Values g (a*N))
    (born : Fin (l).jobs → Fin 3 → Values g (b*N))
    (oldRoom : ∀j f,(v.previousAt floor j f).Fits w base ∧ (l).rows≤(v.previousAt floor j f).size)
    (newRoom : ∀j f,(v.mouthBankAt floor A mat shape j f).Fits w base ∧ (l).rows≤(v.mouthBankAt floor A mat shape j f).size)
    (old : ∀j f,Reads (v.previousAt floor j f) (prior j f) M m)
    (new_ : ∀j f,Reads (v.mouthBankAt floor A mat shape j f) (born j f) M m)
    (space : top<2^w) :
    let code:=v.operandHeaderPhase floor w
    Step base top code m ∧
      (∀j f,Held g top (code.image m) (v.oldHeaderAt floor j f)
        (fun h k=>ScalarOperand.take (((l).index.symm j).2.1) (prior j f h k))) ∧
      ∀j f,Held g top (code.image m) (v.mouthAt floor A mat shape j f)
        (fun h k=>ScalarOperand.take (((l).index.symm j).2.1) (born j f h k)) :=by
  intro code
  let one:=previousHeaderPhase a N M base w
  let two:=previousHeaderPhase b N M middle w
  let mid:=one.image m
  have lo:base ≤ middle:=Nat.le_add_right ..
  have hi:middle≤top:=Nat.le_add_right ..
  have first:=ScalarOperand.header_dictionary a N M base m (hi.trans_lt space)
  have second:=ScalarOperand.header_dictionary b N M middle mid space
  have a₁ : Step base middle one m :=
    ⟨lo,first.1,ROM.frame (ScalarOperand.pages a N M) ((a*N)*M) base m⟩
  have a₂ : Step middle top two mid :=
    ⟨hi,second.1,ROM.frame (ScalarOperand.pages b N M) ((b*N)*M) middle mid⟩
  refine ⟨a₁.thenStep a₂,?_,?_⟩
  · intro j f
    have found:=ScalarOperand.header_source base (v.previousAt floor j f) (((l).index.symm j).2.1) middle m
      (prior j f) (oldRoom j f).1 (oldRoom j f).2 (old j f) le_rfl (hi.trans_lt space)
    exact Step.keep g (p:=two) (m:=mid) a₂ (show Held g middle mid (v.oldHeaderAt floor j f) _ from ⟨found.1,found.2⟩)
  · intro j f
    let bank:=v.mouthBankAt floor A mat shape j f
    have held:=newRoom j f
    have inside:bank.Fits w middle:=⟨held.1.1,held.1.2.1,held.1.2.2.trans lo⟩
    have seen : Reads bank (born j f) M mid:=by
      intro row_
      have idx: (row (l).hosts (l).groups M row_).val<bank.size:=(row (l).hosts (l).groups M row_).isLt.trans_le held.2
      have early:bank.base+(row (l).hosts (l).groups M row_).val<base:=(Nat.add_lt_add_left idx _).trans_le held.1.2.2
      exact (a₁.frame _ (.inl early)).trans (new_ j f row_)
    have found:=ScalarOperand.header_source middle bank (((l).index.symm j).2.1) top mid
      (born j f) inside held.2 seen le_rfl space
    exact ⟨found.1,found.2⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

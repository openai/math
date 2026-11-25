import OAI.Hierarchy.DescentTerminalPointerPages

namespace OAI
/-! # Sharing all earlier population, pointer, signed and pin pages for both output families -/
namespace Hierarchy.DescentTerminalPointerDigits.Gather
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {blocks cap N A d w a b : ℕ} (pages : Pages blocks cap A)
    (mem : Memory w) (origin H : ℕ)
    (f : Source cap N A d→Cell a) (g : Source cap N A d→Cell b)
local notation "L" => columns cap N A
local notation "n" => blocks*H
local notation "ps" => dropOff origin blocks H L pages.address
local notation "B" => banks («L»:=L) origin n
local notation "base" => rom origin L n
local notation "shelf" => DescentTerminalPointerFrame.size L d
local notation "a0" => base+shelf
local notation "base7" => a0+n
local notation "a7" => base7+shelf
local notation "warm" => ProtocolRAM.result ps mem
local notation "mid" => DescentTerminalPointerFrame.result base B n f warm
local notation "done" => DescentTerminalPointerFrame.result base7 B n g mid
local notation "p0" => DescentTerminalPointerFrame.program w base B n f
local notation "p7" => DescentTerminalPointerFrame.program w base7 B n g
local notation "work" => ((4+10*shelf)+(4+n*(16+26*L)))
variable (legal : ∀j x,(pages.address (N:=N) j x).Fits origin H w) (off : 2^d<2^w)
    (space : rom origin (columns cap N A) (blocks*H)
      + DescentTerminalPointerFrame.size (columns cap N A) d + blocks*H
      + DescentTerminalPointerFrame.size (columns cap N A) d + blocks*H < 2^w)
include legal off space in
theorem Pages.pair :
    (((ProtocolRAM.program w ps).seq p0).seq p7).Exec mem done ((clock ps+work)+work) ∧
    CheapCode (((ProtocolRAM.program w ps).seq p0).seq p7) ∧
    (∀x (h : Fin H),done (a0+(finProdFinEquiv (x,h)).val)=((f (pages.source mem x h)).val:Word w) ∧
      done (a7+(finProdFinEquiv (x,h)).val)=((g (pages.source mem x h)).val:Word w)) ∧
    (∀j,j<origin ∨ a7+n≤j→done j=mem j) ∧
    clock ps≤4+(L*blocks)*(4+H*18) := by
  have sep : origin+(L*blocks)*H≤base := by
    rw [Nat.mul_assoc]
    exact Nat.le_add_right _ _
  have originBase : origin≤base := (Nat.le_add_right origin ((L*blocks)*H)).trans sep
  have baseNext : base≤base7 := (Nat.le_add_right base shelf).trans (Nat.le_add_right a0 n)
  have nextEnd : base7≤a7+n := (Nat.le_add_right base7 shelf).trans (Nat.le_add_right a7 n)
  have nextFits : base7<2^w := nextEnd.trans_lt space
  have small : origin+(L*blocks)*H<2^w := sep.trans_lt (baseNext.trans_lt nextFits)
  have ok₀ := banks_fit («L»:=L) origin n d off nextFits
  have sourceFits (j : Fin L) : (B j).Fits w base7 :=
    ⟨(ok₀.source j).1,(ok₀.source j).2.1,(ok₀.source j).2.2.trans baseNext⟩
  have ok₁ : DescentTerminalPointerFrame.Room B base7 d n w :=
    ⟨sourceFits,ok₀.length,off,space⟩
  obtain ⟨first,cheap₀,read₀,frame₀,time⟩ := pages.execute mem origin H f legal off nextFits
  obtain ⟨finalRun,cheap₁,frame₁⟩ := DescentTerminalPointerFrame.run base7 B g mid ok₁
  have old := (DescentTerminalPointerFrame.run base B f warm ok₀).2.2
  let raw (r : Fin n) := low (d:=d) B warm r
  have physical (i : Fin n) (j : Fin L) : (mid ((B j).base+i.val)).val%2^d=(raw i j).val := by
    have digitFits : i.val<(B j).size := i.isLt.trans_le (ok₀.length j)
    have inside : (B j).base+i.val<base :=
      (Nat.add_lt_add_left digitFits (B j).base).trans_le (ok₀.source j).2.2
    have saved : mid ((B j).base+i.val)=warm ((B j).base+i.val) := old _ (Or.inl inside)
    change (mid ((B j).base+i.val)).val%2^d=(warm ((B j).base+i.val)).val%2^d
    rw [saved]
  have read₁ := DescentTerminalPointerFrame.read_masked base7 B g mid ok₁ raw physical
  refine ⟨@Procedure.Exec.then w ((ProtocolRAM.program w ps).seq p0) p7 mem mid done
    (clock ps+work) work (@first) (@finalRun),
    @cheap_seq w ((ProtocolRAM.program w ps).seq p0) p7 (@cheap₀) (@cheap₁),?_,?_,time⟩
  · intro x h
    let i : Fin n := finProdFinEquiv (x,h)
    have earlier : a0+i.val<base7 := Nat.add_lt_add_left i.isLt a0
    have kept : done (a0+i.val)=mid (a0+i.val) := frame₁ _ (Or.inl earlier)
    have gathered : raw i=pages.source mem x h := pages.fetched mem origin H legal small x h
    exact ⟨kept.trans (read₀ x h),(read₁ i).trans (congrArg
      (fun row : Source cap N A d => ((g row).val:Word w)) gathered)⟩
  · intro j apart
    rcases apart with before | after
    · have below : j<base7 := before.trans_le (originBase.trans baseNext)
      exact (frame₁ j (Or.inl below)).trans (frame₀ j (Or.inl before))
    · have above : base7≤j := nextEnd.trans after
      exact (frame₁ j (Or.inr after)).trans (frame₀ j (Or.inr above))

end
end Hierarchy.DescentTerminalPointerDigits.Gather

end OAI

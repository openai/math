import OAI.Hierarchy.DescentOrdinaryPriorPad
import OAI.Hierarchy.DescentOrdinaryRefsROM
import OAI.Hierarchy.DescentOrdinaryBornBook
import OAI.Hierarchy.DescentOrdinaryRoleControl
import OAI.Hierarchy.DescentOrdinaryGatherOnly
import OAI.Hierarchy.DescentPreviousOperandLayout

namespace OAI
/-! # Physical directory of an ordinary successor's original operand books -/
namespace Hierarchy.DescentOrdinaryReferenceInputs
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentOperandVectorArena DescentOperandStateBanks DescentPackedColony DescentSIMDLookup
open DescentPackedZip DescentHaloWalkRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (C : DescentOrdinaryRefsROM.Chart)

/-- Fixed addresses. The previous and birth pages are the two real source regions on the
ordinary tape; the one local venue bank is common to all pages and all targets. -/
structure Directory (C : DescentOrdinaryRefsROM.Chart) (L : Layout) where
  previous : DescentDatedPriorOperand.Layout
  tileBase : ℕ
  priorHosts : ℕ
  priorPitch : ℕ
  born : DescentOrdinaryBorn.Chart
  birthStart : ℕ
  population : RoleControl.Layout
  ports : Ports (breadth C.degree)
  venues : Bank
  prevBlocks : previous.blocks=2^C.k
  prevSlots : previous.operands≤L.operands
  birthBlocks : born.blocks=2^C.k
  birthCap : born.cap=C.capacity
  birthArgs : born.args=L.operands
  walks : population.walks=breadth C.degree
  sites : population.sites=L.lows

namespace Directory
variable {C} {L : Layout} (R : Directory C L)
def rootPorts : Ports R.population.walks:= R.walks.symm ▸ R.ports

def refs : References L C.degree C.k C.oldNodes C.capacity :=fun pg low=>
  let fa:=(finProdFinEquiv : Fin 7×Fin L.operands≃Fin L.pageCount).symm pg
  ⟨C.tables,C.gates,R.ports,
    (fun x=>if valid : fa.2.val<R.previous.operands then
      DescentOrdinaryPriorPad.bank R.previous R.priorHosts R.priorPitch R.tileBase
        (Fin.cast R.prevBlocks.symm x) (page fa.1 ⟨fa.2.val,valid⟩)
      else DescentOrdinaryPriorPad.zero R.previous R.priorHosts R.priorPitch R.tileBase),
    (fun x t j=>R.born.bank R.birthStart (Fin.cast R.birthBlocks.symm x) (Fin.cast R.birthCap.symm t) j
      (Fin.cast R.birthArgs.symm fa.2) fa.1),
    C.dictionary,R.population.want R.rootPorts (Fin.cast R.sites.symm low),.lookup R.venues .row,R.population.counts⟩

private theorem zip_fits {T : Tables} {x y : Expr} {a b M upper w : ℕ} (h : Fits T x y a b M upper w) :
    (T.read x y).Fits w upper :=by simp [Tables.read,Expr.Fits,h.left,h.right,h.shift,h.apply]

theorem mask_fits {w : ℕ} (pg : Fin L.pageCount) (low : Fin L.lows) (upper : ℕ)
    (rooms : C.Rooms w upper)
    (want : (R.refs pg low).want.Fits w upper) (venue : (R.refs pg low).addr.Fits w upper)
    (count : (R.refs pg low).counts.Fits w upper) :
    let r:=R.refs pg low
    (masked r.tables r.want r.addr r.counts).Fits w upper :=
  zip_fits (rooms.actors _ _ (zip_fits (rooms.targets _ _ want venue)) count)

private theorem read_fits {H G w : ℕ} (pg : Fin L.pageCount) (low : Fin L.lows) (upper : ℕ)
    (rooms : C.Rooms w upper)
    (oldAccess : ∀b,Accessible R.ports ((R.refs pg low).previous b) H G C.lanes w upper)
    (bornAccess : ∀b t j,Accessible R.ports ((R.refs pg low).birth b t j) H G C.lanes w upper)
    (j : Fin C.nodes) : ((R.refs pg low).read H j).Fits w upper :=by
  let refs_:=R.refs pg low
  have fitOperand (b : Fin (2^C.k)) (slot : Fin (C.oldNodes+C.capacity*6)) (walk : Fin (breadth C.degree)) :
      (operand R.ports refs_.previous refs_.birth C.dictionary H walk b slot).Fits w upper:=by
    obtain ⟨z,rfl⟩:=finSumFinEquiv.surjective slot
    rcases z with z|z
    · simpa only [operand,Equiv.symm_apply_apply,Sum.elim_inl,project] using
        (show (Expr.lookup (C.dictionary z) (peerExpr R.ports (refs_.previous b) H walk)).Fits w upper from
          ⟨(rooms.dictionary z).1,peer_fits R.ports _ upper (oldAccess b) walk⟩)
    · obtain ⟨⟨t,j⟩,rfl⟩:=finProdFinEquiv.surjective z
      simpa only [operand,Equiv.symm_apply_apply,Sum.elim_inr] using peer_fits R.ports _ upper (bornAccess b t j) walk
  exact fitOperand _ _ _

/-- All lookups use the mounted pointer banks even when their contents are arbitrary. -/
theorem expr_fits {H G w : ℕ} (pg : Fin L.pageCount) (low : Fin L.lows) (upper : ℕ)
    (rooms : C.Rooms w upper)
    (oldAccess : ∀b,Accessible R.ports ((R.refs pg low).previous b) H G C.lanes w upper)
    (bornAccess : ∀b t j,Accessible R.ports ((R.refs pg low).birth b t j) H G C.lanes w upper)
    (want : (R.refs pg low).want.Fits w upper) (venue : (R.refs pg low).addr.Fits w upper)
    (count : (R.refs pg low).counts.Fits w upper) :
    ((R.refs pg low).expr H).Fits w upper :=by
  let r:=R.refs pg low
  have target:=rooms.targets _ _ want venue
  have active:=rooms.actors _ _ (zip_fits target) count
  have fieldFits:=rooms.fields (r.read H) (R.read_fits pg low upper rooms oldAccess bornAccess)
  exact zip_fits (rooms.emit _ _ (zip_fits active) (DescentPacking.PackedMatch.Local.Gather.fits C.gates _ upper fieldFits (List.finRange C.nodes)))

/-- The six material bank readings at an actual row plus the two installed tables
determine every operand, including access through a remote old or fresh donor. -/
theorem measured {H G w : ℕ} (pg : Fin L.pageCount) (low : Fin L.lows) (upper : ℕ) (mem : Memory w)
    (V : Values C.degree C.k C.oldNodes C.capacity H G C.bits C.nameBits C.countBits)
    (rooms : C.Rooms w upper) (rom : C.Issued mem)
    (wired : Mounted R.ports (DescentSortedRoster.indexed V.walks) mem G C.lanes)
    (prev : ∀x,Reads ((R.refs pg low).previous x) (V.old x) C.lanes mem)
    (newborn : ∀x t j,Reads ((R.refs pg low).birth x t j) (V.born x t j) C.lanes mem)
    (access : ∀B : Bank,B.Fits w upper→H*chunks G C.lanes≤B.size→Accessible R.ports B H G C.lanes w upper)
    (oldPlace : ∀x,((R.refs pg low).previous x).Fits w upper ∧ H*chunks G C.lanes≤((R.refs pg low).previous x).size)
    (bornPlace : ∀x t j,((R.refs pg low).birth x t j).Fits w upper ∧ H*chunks G C.lanes≤((R.refs pg low).birth x t j).size)
    (want : Source (R.refs pg low).want V.wanted C.lanes mem)
    (venues : Source (R.refs pg low).addr (fun h g=>encode C.nameBits C.actors (V.venues h g)) C.lanes mem)
    (counts : Source (R.refs pg low).counts (fun h g=>encode C.countBits C.donors (V.counts h g)) C.lanes mem)
    (wantFit : (R.refs pg low).want.Fits w upper) (venueFit : (R.refs pg low).addr.Fits w upper)
    (countFit : (R.refs pg low).counts.Fits w upper) :
    Measured (R.refs pg low) V C.newNodes C.lanes upper mem :=by
  let refs_:=R.refs pg low
  have oldAccess x:=access _ (oldPlace x).1 (oldPlace x).2
  have bornAccess x t j:=access _ (bornPlace x t j).1 (bornPlace x t j).2
  have target:=rooms.targets _ _ wantFit venueFit
  have mask:=rooms.actors _ _ (zip_fits target) countFit
  have raws:=rooms.fields (refs_.read H) (R.read_fits pg low upper rooms oldAccess bornAccess)
  have emit:=rooms.emit _ _ (zip_fits mask) (DescentPacking.PackedMatch.Local.Gather.fits C.gates _ upper raws (List.finRange C.nodes))
  exact ⟨wired,prev,newborn,oldAccess,bornAccess,rooms.dictionary,rom.dictionary,want,venues,counts,target,mask,raws,emit,
    rom.targets,rom.actors,rom.fields,rom.emit⟩

end Directory
end
end Hierarchy.DescentOrdinaryReferenceInputs

end OAI

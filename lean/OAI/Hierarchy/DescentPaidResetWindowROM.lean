import OAI.Hierarchy.DescentPaidResetWindow
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Physically reading the reset charges from the posted short stencil and prior census -/
namespace Hierarchy.DescentPaidResidentCount.Reset.WindowRAM
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {u v outBits H G M w base : ℕ} (kernel : Cell u→Cell v→Cell outBits) (zero : kernel 0 0=0)
local notation "pages" => binary kernel M
local notation "aperture" => ((u+v)*M)
local notation "words" => 2*2^aperture
local notation "table" => joined pages aperture base (fun j=>j)

private theorem page_room (j : Fin 2) : (pages j).bits≤aperture := by
  fin_cases j
  · exact Nat.mul_le_mul_right M (Nat.le_add_right ..)
  · rfl

include zero in
/-- One shared two-page table compares every original suffix identifier in its
actual packed word and sums that matching old primary or destination population. -/
theorem binaryFresh (stencil weights : Expr) (bank : Bank) (m : Memory w)
    (sEarly : stencil.Fits w base) (wEarly : weights.Fits w base)
    (raw : Fin H→Fin G→Cell u) (values : Fin H→Fin G→Cell v)
    (staged : Source stencil raw M m)
    (old : Source weights values M m)
    (apart : base+words≤bank.base) (space : bank.base+H*chunks G M<2^w) :
    let mounted:=after pages aperture base m
    let op:=(table).read stencil weights
    let N:=H*chunks G M
    let done:=image bank.base N op mounted
    let program:=(mount pages aperture w base).seq (scan w bank.base N op)
    program.Exec m done ((4+10*words)+(4+N*(2*op.work+4))) ∧
      Reads bank (fun h g=>kernel (raw h g) (values h g)) M done ∧
      (∀i,i<base ∨ bank.base+N≤ i→done i=m i) ∧
      DescentStaticWordColumn.names program=15*(words+1)+(11+4*(stencil.work+weights.work+11)) ∧ CheapCode program := by
  intro mounted op N done program
  have below : bank.base<2^w:=(Nat.le_add_right ..).trans_lt space
  have precedes : base≤bank.base:=(Nat.le_add_right ..).trans apart
  have started := DescentOrdinaryAtomFieldRAM.ROM.run pages aperture base m (apart.trans_lt below)
  have printed := binary_mounted kernel M pages aperture base m (page_room kernel) id (fun _=>rfl)
  have stable:=DescentOrdinaryAtomFieldRAM.ROM.frame pages aperture base m
  have keep {n : ℕ} (e : Expr) (fit : e.Fits w base) (x : Fin H→Fin G→Cell n) (live : Source e x M m) :
      Source e x M mounted := fun j=>(ProtocolRAM.eval_below e _ m mounted fit (fun i hi=>stable i (.inl hi))).trans (live j)
  have bounds : DescentPackedZip.Fits table stencil weights u v M bank.base w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ precedes sEarly,ProtocolRAMGeneratedWrite.fits_mono _ precedes wEarly,
      bank_room pages aperture base _ _ (page_room kernel 0) apart below,bank_room pages aperture base _ _ (page_room kernel 1) apart below,rfl,rfl⟩
  have computed:=read_data table stencil weights bank.base bounds kernel zero mounted printed
    _ _ (keep _ sEarly _ staged) (keep _ wEarly _ old)
  have running : (scan w bank.base N op).Exec mounted done (4+N*(2*op.work+4)) :=
    scan_exec bank.base N op mounted ⟨bounds.apply,bounds.right,bounds.shift,bounds.left⟩ space
  refine ⟨Procedure.Exec.then started.1 running,?_,?_,?_,cheap_seq (cheap pages aperture w base) (@scan_cheap _ _ _ _)⟩
  · intro j
    exact (ProtocolRAMGeneratedWrite.read_image bank.base N op mounted (row H G M j)).trans (computed j)
  · intro i apart'
    have saved:=ProtocolRAMGeneratedWrite.frame_image bank.base N op mounted i (by rcases apart' with low|high <;> omega)
    exact saved.trans (stable i (by rcases apart' with low|high <;> omega))
  · dsimp only [program,op]
    rw [DescentStaticWordColumn.names_seq,started.2,DescentStaticWordColumn.names_scan,DescentPackedZip.work]

end

noncomputable section
variable {a b L root H G M w base : ℕ}
local notation "kernel" => tally a b L root
local notation "pages" => binary kernel M
local notation "aperture" => ((a*L+b*L)*M)
local notation "words" => 2*2^aperture
local notation "table" => joined pages aperture base (fun j=>j)

/-- One shared two-page table compares every original suffix identifier in its
actual packed word and sums that matching old primary or destination population. -/
theorem fresh (stencil weights : Expr) (bank : Bank) (m : Memory w)
    (sEarly : stencil.Fits w base) (wEarly : weights.Fits w base)
    (raw : Fin H→Fin G→Fin L→Cell a) (values : Fin H→Fin G→Fin L→Cell b)
    (staged : Source stencil (fun h g=>encode a _ (raw h g)) M m)
    (old : Source weights (fun h g=>encode b _ (values h g)) M m)
    (apart : base+words≤bank.base) (space : bank.base+H*chunks G M<2^w) :
    let mounted:=after pages aperture base m
    let op:=(table).read stencil weights
    let N:=H*chunks G M
    let done:=image bank.base N op mounted
    let program:=(mount pages aperture w base).seq (scan w bank.base N op)
    program.Exec m done ((4+10*words)+(4+N*(2*op.work+4))) ∧
      Reads bank (fun h g=>kernel (encode a _ (raw h g)) (encode b _ (values h g))) M done ∧
      (∀i,i<base ∨ bank.base+N≤ i→done i=m i) ∧
      DescentStaticWordColumn.names program=15*(words+1)+(11+4*(stencil.work+weights.work+11)) ∧ CheapCode program :=
  binaryFresh kernel (tally_zero ..) stencil weights bank m sEarly wEarly _ _ staged old apart space

end
end Hierarchy.DescentPaidResidentCount.Reset.WindowRAM

end OAI

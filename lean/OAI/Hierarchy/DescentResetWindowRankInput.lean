import OAI.Hierarchy.DescentResetFieldAssembler
import OAI.Hierarchy.DescentResetSignedScan

namespace OAI
/-! # The local weighted-prefix input comes from the mixed header and the returned source ticket -/
namespace Hierarchy.DescentResetSignedScan.RankInput
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentResetFieldAssembler (Meta)
open private DescentPacking.PackedMatch.Local.Gather.encode_zero from OAI.Hierarchy.DescentPackedFieldGather
open scoped Classical Fin.CommRing
noncomputable section
variable {H G X K b M w : ℕ}

def parent (row : Meta) (ticket : ℕ) : Option Parent :=
  if row.live then some ⟨DescentResetFieldAssembler.peer row,row.src,ticket,row.units⟩ else none

def kernel (b : ℕ) (row : Cell (b*7)) (ticket : Cell b) : Cell (b*5) :=
  encode b 5 (literal b (parent (DescentResetFieldAssembler.decode b row) ticket.val))

theorem blank (b : ℕ) : kernel b 0 0=0 := by
  have eqn : DescentResetFieldAssembler.raw b Meta.blank=0:=by
    unfold DescentResetFieldAssembler.raw
    convert DescentPacking.PackedMatch.Local.Gather.encode_zero b 7 using 2
    funext i
    fin_cases i <;> rfl
  have small (i : Fin 7) : DescentResetFieldAssembler.digits Meta.blank i<2^b:=by
    fin_cases i <;> exact Nat.two_pow_pos _
  have dec:=DescentResetFieldAssembler.decode_raw Meta.blank small
  rw [eqn] at dec
  unfold kernel
  rw [dec]
  exact DescentPacking.PackedMatch.Local.Gather.encode_zero b 5

def width (b M : ℕ):=(b*7+b)*M
def endAddress (base b M : ℕ):=base+2*2^(width b M)
def pages (b M : ℕ):=binary (kernel b) M
def tables (base b M : ℕ):=joined (pages b M) (width b M) base id
def expr (base b M : ℕ) (header ticket : Expr):=(tables base b M).read header ticket
def program (base b M w : ℕ):=mount (pages b M) (width b M) w base
def memory (base b M : ℕ) (m : Memory w):=after (pages b M) (width b M) base m

theorem any (base b M : ℕ) (m : Memory w) (space : endAddress base b M<2^w) :
    (program base b M w).Exec m (memory base b M m) (4+10*(2*2^(width b M))) ∧
    (∀z,z<base ∨ endAddress base b M≤z→memory base b M m z=m z) ∧
    DescentStaticWordColumn.names (program base b M w)=15*(2*2^(width b M)+1) ∧ CheapCode (program base b M w) := by
  have mounted := DescentOrdinaryAtomFieldRAM.ROM.run (pages b M) (width b M) base m space
  exact ⟨mounted.1, frame (pages b M) (width b M) base m, mounted.2,
    DescentOrdinaryAtomFieldRAM.ROM.cheap (pages b M) (width b M) w base⟩

theorem room (b M : ℕ) (i : Fin 2) : (pages b M i).bits≤width b M := by
  fin_cases i
  · exact Nat.mul_le_mul_right M (Nat.le_add_right ..)
  · rfl

theorem fits (base : ℕ) (header ticket : Expr)
    (h : header.Fits w base) (t : ticket.Fits w base) (space : endAddress base b M<2^w) :
    DescentPackedZip.Fits (tables base b M) header ticket (b*7) b M (endAddress base b M) w := by
  have inc : base≤endAddress base b M:=Nat.le_add_right ..
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ inc h,ProtocolRAMGeneratedWrite.fits_mono _ inc t,
    bank_room _ _ _ _ _ (room b M _) le_rfl space,bank_room _ _ _ _ _ (room b M _) le_rfl space,rfl,rfl⟩

theorem expr_fits (base : ℕ) (header ticket : Expr)
    (h : header.Fits w base) (t : ticket.Fits w base) (space : endAddress base b M<2^w) :
    (expr base b M header ticket).Fits w (endAddress base b M) := by
  have fit:=fits base header ticket h t space
  simp [expr,Tables.read,Expr.Fits,fit.left,fit.right,fit.shift,fit.apply]

theorem read (base : ℕ) (header ticket : Expr) (m : Memory w) (rows : Fin H→Fin G→Meta)
    (tickets : Fin H→Fin G→Cell b) (h : header.Fits w base) (t : ticket.Fits w base)
    (hs : Source header (fun v g=>DescentResetFieldAssembler.raw b (rows v g)) M m)
    (ts : Source ticket tickets M m) (small : ∀v g i,DescentResetFieldAssembler.digits (rows v g) i<2^b)
    (space : endAddress base b M<2^w) :
    Source (expr base b M header ticket) (fun v g=>encode b 5 (literal b (parent (rows v g) (tickets v g).val))) M
      (memory base b M m) := by
  let done:=memory base b M m
  have stable:=frame (pages b M) (width b M) base m
  have keep {d : ℕ} (op : Expr) (ok : op.Fits w base) (v : Fin H→Fin G→Cell d) (source : Source op v M m) :
      Source op v M done :=fun j=>(ProtocolRAM.eval_below op _ m done ok (fun z hz=>stable z (.inl hz))).trans (source j)
  have table:=binary_mounted (kernel b) M (pages b M) (width b M) base m (room b M) id (fun _=>rfl)
  have result:=read_data _ header ticket (endAddress base b M) (fits base header ticket h t space) (kernel b)
    (blank b) done table _ _ (keep _ h _ hs) (keep _ t _ ts)
  have decoded (v : Fin H) (g : Fin G) :
      DescentResetFieldAssembler.decode b (DescentResetFieldAssembler.raw b (rows v g)) = rows v g :=
    DescentResetFieldAssembler.decode_raw (rows v g) (small v g)
  simpa only [expr, kernel, decoded] using result

end
end Hierarchy.DescentResetSignedScan.RankInput

end OAI

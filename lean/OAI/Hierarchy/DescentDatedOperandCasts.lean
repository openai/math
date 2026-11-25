import OAI.Hierarchy.DescentDatedOldHeaderProgram
import OAI.Hierarchy.DescentRootOrderCast
import OAI.Hierarchy.DescentSignedPrefixInvoice

namespace OAI
/-! # Four physically stored lane conversions shared by all operand lookups -/
namespace Hierarchy.DescentDatedOperandCasts
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (width : Fin 4 → ℕ) (a M : ℕ)

def page (i : Fin 4) : ROM.Page :=
  ⟨width i*M,fun x=>(DescentSIMDLookup.table (M:=M) (DescentRootOrderCast.widen (a:=width i) (b:=a)) x).val⟩
def stop (base : ℕ) :=base+4*2^(a*M)
def phase (base w : ℕ) : NativePhase w :=
  ⟨ROM.mount (page width a M) (a*M) w base,4+10*(4*2^(a*M)),ROM.after (page width a M) (a*M) base,
    ROM.cheap _ _ _ _⟩
def expr (base : ℕ) (i : Fin 4) (src : Expr) : Expr :=
  .lookup (ROM.bank (page width a M) (a*M) base i) src
theorem work (base : ℕ) (i : Fin 4) (src : Expr) : (expr width a M base i src).work=src.work+5 :=rfl

variable {base w H G : ℕ} (size : ∀i,width i≤a) (room : stop a M base<2^w)
include room in
theorem any (m : Memory w) :
    (phase width a M base w).Runs m ∧
      ∀i,i<base ∨ stop a M base ≤ i → (phase width a M base w).image m i=m i :=
  ⟨(ROM.run (page width a M) (a*M) base m room).1,ROM.frame _ _ _ m⟩

include size room in
theorem issued (i : Fin 4) (src : Expr) (m : Memory w) (x : Fin H → Fin G → Cell (width i))
    (held : src.Fits w base) (read : Source src x M m) :
    (expr width a M base i src).Fits w (stop a M base) ∧
      Source (expr width a M base i src) (fun h g=>DescentRootOrderCast.widen (b:=a) (x h g))
        M ((phase width a M base w).image m) :=by
  let t:=ROM.bank (page width a M) (a*M) base i
  let mid:=(phase width a M base w).image m
  have widths:(page width a M i).bits≤a*M:=Nat.mul_le_mul_right _ (size i)
  have geo:t.Fits w (stop a M base):=ROM.bank_room (page width a M) (a*M) base _ i widths le_rfl room
  refine ⟨⟨geo,ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) held⟩,?_⟩
  intro r
  let j:=data x r
  have prev:src.eval mid ((row H G M r).val:Word w)=(j.val:Word w) :=
    (ProtocolRAM.eval_below _ _ m mid held (fun z hz=>(any width a M room m).2 z (.inl hz))).trans (read r)
  have paid:=ROM.read (page width a M) (a*M) base m i widths j
  have step:=DescentIssuedTerminalId.lookup_nat t mid ((row H G M r).val:Word w) src j.val prev j.isLt geo.2.1
  apply step.trans
  change ROM.after (page width a M) (a*M) base m ((ROM.bank (page width a M) (a*M) base i).base+j.val)=_
  simpa only [j,page,DescentRootOrderCast.table_read] using paid

end
end Hierarchy.DescentDatedOperandCasts

end OAI

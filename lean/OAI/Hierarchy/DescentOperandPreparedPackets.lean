import OAI.Hierarchy.DescentOperandRootPull
import OAI.Hierarchy.DescentPreparedRootInputs
import OAI.Hierarchy.DescentIssuedFallbackRoot
import OAI.Hierarchy.DescentPreparedRotorInputs

namespace OAI
/-! # Relocate the actually prepared original root packet at each successor operand row -/
namespace Hierarchy.DescentOperandRootPull
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan DescentFallbackPeriod.Projected
open DescentSixParty.Chronology DescentResetHostSize DescentHostDirectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def defaultRoot (r : ℕ) : Code r:=⟨(0,0),mem_codes (Nat.zero_le r) (by decide)⟩
def fallbackPage (r n : ℕ) : RootPage r (2^n):=(false,.inr (defaultRoot r,none))
def matrixPage (r n : ℕ) : RootPage r (2^n):=(false,.inl (defaultRoot r,.inl false))

private theorem source_cast {A B H w t M : ℕ} (eqn : B=A) (src : Expr) (x : Fin H→Fin A→Cell t)
    (m : Memory w) (holds : Source src x M m) : Source src (fun v (g:Fin B)=>x v (Fin.cast eqn g)) M m := by
  subst B
  exact holds

variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)
    (page : RootPage r (2^n))
local notation "A" => RootTemplates.arena (a.headerEnd b) H (2^c) M r n D
set_option quotPrecheck false
local notation "book" => (b.table page).2
local notation "E" => (b.table page).1

def pageLayout (base ptr receivers groups X after : ℕ) : Layout :=
  ⟨base,ptr,H,receivers,groups,X,(book).field,E,M,after⟩

attribute [local irreducible] Procedure.Exec ProtocolRAM.CheapCode Layout.program Layout.image Layout.clock Layout.src Layout.endAddress
  DescentSIMDLookup.encode DescentPackedZip.Source

set_option Elab.async false in
set_option maxHeartbeats 600000 in
/-- Only published original root words are pulled. The parent directory agrees on each
    compact row, and the physical copy/retile program runs on the later memory itself. -/
theorem pull {receivers groups X after : ℕ} (base ptr : ℕ) (space : a.PreparedFits b) (before current : Memory w)
    (value : Fin H→Fin (2^c)→Fin E→Cell (book).field)
    (prior : ∀i,((book).reads i).Fits w ((A).middle (rootIndex r (2^n) page).val))
    (packed : M*max ((book).field*E) (book).outputBits≤w/2)
    (original : ∀i,Source ((book).reads i) (fun v g=>value v g i) M (a.rootInputState b space before page))
    (kept : ∀z,z<a.preparedEnd b→current z=a.preparedImage b space before z)
    (low : a.preparedEnd b≤base) (owner : Fin receivers→Fin H)
    (ds : groups*X=2^c) (hM : 0<M) (ha : 0<after) (hx : 0<X)
    (directory : DescentResetStemKeyReindex.Directory ptr owner current) (prev : ptr+span receivers≤base)
    (room : (pageLayout (H:=H) (M:=M) b page base ptr receivers groups X after).endAddress<2^w) :
    let L:=pageLayout (H:=H) (M:=M) b page base ptr receivers groups X after
    let src:=a.gatheredOperand b page
    (L.program src w).Exec current (L.image src current) (L.clock src w) ∧ CheapCode (L.program src w) ∧
    (∀j x,(L.src j x).Fits w L.endAddress ∧ Source (L.src j x)
      (fun v g=>value (owner v) (Fin.cast ds (finProdFinEquiv (g,x))) j) after (L.image src current)) ∧
    ∀z,z<base ∨ L.endAddress≤z→L.image src current z=current z := by
  intro L src
  have fromRoot:=a.gathered_source b space before page value prior packed original
  have past:=a.gathered_fits b space page
  have moved : Source src (fun v g=>encode (book).field E (value v g)) M current := by
    unfold Source at fromRoot ⊢
    intro row
    exact (eval_below src _ _ _ past kept).trans (fromRoot row)
  have stored := @source_cast (2^c) (groups*X) H w ((book).field*E) M ds src
    (fun v g => encode (book).field E (value v g)) current moved
  exact @Layout.run L w src current (fun v g => value v (Fin.cast ds g)) owner hM ha hx
    (ProtocolRAMGeneratedWrite.fits_mono src low past) stored directory prev room

end
end Hierarchy.DescentOperandRootPull

end OAI

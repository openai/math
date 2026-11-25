import OAI.Hierarchy.DescentTerminalPreflightRun

namespace OAI
/-! # Address the primitive role and pointer machine from the previous date and the new prior bands -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentSIMDLookup DescentTerminalPrimitiveArena DescentTerminalCombinedRole DescentTerminalPointerDigits ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

variable (x:DescentTerminalPreflightSpace.Spec) (base:ℕ)

/-- The real frozen cohort bin begins immediately after the four sorting subarrays. -/
def frozenRoster : Bank :=
  ⟨DescentTerminalCohortArena.tallyBase base x.frozenBits x.cohortBits x.cohorts x.scalar.shops+4*x.cohorts,Nat.clog 2 x.scalar.shops⟩

variable {args:ℕ} (matrix:ℕ) (pointers:Fin 4→Fin args→Fin x.scalar.blocks→Bank)
    (signed:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)

/-- The selected matrix and four retained fast pointer banks come from the last
dated state. The prior f3 scan and earlier role scan own the other two banks. -/
def pointerPages : Gather.Pages x.scalar.blocks x.cap args where
  population := x.scalar.subrow (x.population base)
  matrix := matrix
  frozen := x.frozenRoster base
  arity := x.scalar.subrow ((x.primitive base)+x.scalar.rows)
  pointers := pointers
  signed j b := signed b j

variable {w:ℕ} (space:x.maskBase base<2^w)
    (mat:matrix+1≤(x.cohortEnd base)) (pe:∀f j b,(pointers f j b).base+(pointers f j b).size≤(x.cohortEnd base))
    (ph:∀f j b,x.scalar.shops≤(pointers f j b).size)
    (se:∀b j,(signed b j).base+(signed b j).size≤(x.cohortEnd base)) (sh:∀b j,x.scalar.shops≤(signed b j).size)

include space mat pe ph se sh in
theorem pointer_fits (nodes:ℕ) (j:Fin (columns x.cap nodes args)) (b:Fin x.scalar.blocks) :
    ((x.pointerPages base matrix pointers signed).address j b).Fits (x.scalar.gather (x.primitive base)) x.scalar.shops w := by
  obtain ⟨pre,po,bk,bc,c1,c2,c3,c4,c5⟩:=x.layers base
  have stop:(x.scalar.gather (x.primitive base))≤x.weights base:=by
    change x.scalar.gather (x.primitive base)≤x.scalar.finish (x.primitive base)
    unfold Shape.finish Shape.widths Shape.number Shape.counting Shape.pointers Shape.«public» Shape.rom;omega
  have startBound:(x.primitive base)≤(x.scalar.gather (x.primitive base)):=by unfold Shape.gather;omega
  have fit (B:Bank) (bound:B.base+B.size≤(x.scalar.gather (x.primitive base))) : B.Fits w (x.scalar.gather (x.primitive base)):=
    ⟨Nat.two_pow_pos _,((Nat.le_add_left B.size B.base).trans bound).trans_lt (by omega),bound⟩
  have frame:=x.prior base
  have reserved:(x.frozenRoster base).base+pad x.scalar.shops≤ (x.primitive base):=by
    have upto:(x.frozenRoster base).base≤(x.cohortEnd base):=by dsimp only [frozenRoster, cohortEnd, DescentTerminalCohortArena.stop]; omega
    have allowance:(x.cohortEnd base)+pad x.scalar.shops≤ (x.primitive base):=by
      unfold primitive DescentTerminalPriorArena.start DescentTerminalPriorArena.actor DescentTerminalPriorArena.actStart
        DescentTerminalPriorArena.pop
      omega
    exact (Nat.add_le_add_right upto _).trans allowance
  have paidEnd:(x.scalar.subrow (x.population base) b).base+(x.scalar.subrow (x.population base) b).size≤(x.scalar.gather (x.primitive base)):=
    x.scalar.old_frame (x.primitive base) (x.population base) _ frame b 3 (by decide)
  have arityEnd:(x.scalar.subrow ((x.primitive base)+x.scalar.rows) b).base+(x.scalar.subrow ((x.primitive base)+x.scalar.rows) b).size≤(x.scalar.gather (x.primitive base)):=
    x.scalar.old_frame (x.primitive base) (x.population base) _ frame b 6 (by decide)
  have ma:(⟨matrix,0⟩ : Bank).Fits w (x.scalar.gather (x.primitive base)):=fit _ (mat.trans (pre.trans startBound))
  unfold Gather.Pages.address
  split
  · exact ⟨fit _ paidEnd,covered x.scalar.shops⟩
  split
  · exact ma
  split
  · exact ⟨fit _ (reserved.trans startBound),covered x.scalar.shops⟩
  split
  · exact ⟨fit _ arityEnd,covered x.scalar.shops⟩
  split
  · exact ⟨fit _ ((pe _ _ _).trans (pre.trans startBound)),ph _ _ _⟩
  · exact ⟨fit _ ((se _ _).trans (pre.trans startBound)),sh _ _⟩

include space in
theorem role_fits (bits:Fin 6→ℕ) (raw:Fin 6→Bank) (advice:ℕ)
    (previous:∀f,(raw f).base+(raw f).size≤(x.cohortEnd base))
    (mounted:advice+DescentTerminalRoleTables.count bits≤(x.cohortEnd base)) :
    (emit (DescentTerminalRoleTables.role bits raw advice)).Fits w (x.primitive base) ∧
      (emit (DescentTerminalRoleTables.arity bits raw advice)).Fits w (x.primitive base) := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩:=x.layers base
  apply DescentTerminalRoleTables.fits bits raw advice (x.primitive base) w
  · intro slot
    have bnd:=previous slot
    exact ⟨Nat.two_pow_pos _,((Nat.le_add_left (raw slot).size (raw slot).base).trans bnd).trans_lt (by omega),bnd.trans a⟩
  · exact mounted.trans a
  · omega

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI

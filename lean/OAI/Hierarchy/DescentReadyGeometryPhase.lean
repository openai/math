import OAI.Hierarchy.DescentResidentDonorPlacement

namespace OAI
/-! # Install the walk and mask literals before running the physical owner and chart publishers -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic.Placement
open DescentPacking.PackedMatch.Local DescentHaloWalkRAM DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentSixParty.Chronology ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (H G M D r p d cap profile w base : ℕ) (adj hub : Bank) (e : Expr)
local notation "L" => layout H G M D (Owners.inputBits r D p d) base adj hub
local notation "printed" => RootTables.length H G M D
def rootsPhase : NativePhase w where
  program:=RootTables.program H G M D w base
  ticks:=4+10*printed
  image:=RootTables.image H G M D base
  cheap:=@DescentStaticWordColumn.cheap _ _ _ _
def issuedPhase : NativePhase w :=
  (rootsPhase H G M D w base).seq (Dynamic.phase L r D p d cap profile H G M w e)

theorem any (geometry : Dynamic.Room L r D p d H G M w e) (m : Memory w) :
    let full:=issuedPhase H G M D r p d cap profile w base adj hub e
    full.Runs m ∧ (∀x,x<base→full.image m x=m x) ∧ RootTables.Present H G M D base (full.image m) := by
  intro full
  have end₀:=geometry.owner_end
  have ran:=geometry.order
  have rootsEnd:base+printed≤(L).ownerBase:=by change _≤first H G M D base;unfold first;omega
  have low : (L).ownerBase ≤ Owners.Board.venue (Owners.inputBits r D p d) M (L).ownerBase (H*chunks G M) :=
    by
      simp only [Owners.Board.venue, Owners.Board.rom, Nat.add_assoc]
      exact Nat.le_add_right _ _
  have span:(L).ranks.endpoints.base+H*breadth D≤(L).rankOut:=
    (Nat.add_le_add_left ran.sizeEnd _).trans ran.endpoints.2.2
  have top:=ran.output
  obtain ⟨setup,programmed,nochange,_⟩:=RootTables.mount H G M D base m (by omega)
  obtain ⟨native,kept⟩:=Dynamic.any L r D p d cap profile H G M w e geometry (RootTables.image H G M D base m)
  exact ⟨setup.then native,fun x h=>(kept x (by omega)).trans (nochange x (.inl h)),
    RootTables.keep H G M D programmed (fun x hx=>kept x (hx.trans_le rootsEnd))⟩

theorem any_frame (geometry : Dynamic.Room L r D p d H G M w e) (m : Memory w) :
    let full:=issuedPhase H G M D r p d cap profile w base adj hub e
    full.Runs m ∧ ∀x,x<base ∨ endAddress H G M D (Owners.inputBits r D p d) base≤x→full.image m x=m x := by
  let full:=issuedPhase H G M D r p d cap profile w base adj hub e
  obtain ⟨run,lower,_⟩:=any H G M D r p d cap profile w base adj hub e geometry m
  obtain ⟨_,fr⟩:=Dynamic.any_frame L r D p d cap profile H G M w e geometry (RootTables.image H G M D base m)
  have rootEnd:base+printed≤(L).ownerBase:=by change _≤first H G M D base;unfold first;omega
  have addr: (L).literal+DonorChartBook.words H G M (breadth D)≤endAddress H G M D (Owners.inputBits r D p d) base:=by
    unfold endAddress layout;dsimp;omega
  have oldEnd : (L).ownerBase ≤ (L).literal := by
    change first H G M D base ≤ bookBase H G M D (Owners.inputBits r D p d) base
    unfold bookBase hubBase rankBase rowEnd Owners.Board.venue Owners.Board.rom
    simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _
  refine ⟨run,?_⟩
  rintro x (lo|hi)
  · exact lower x lo
  · exact (fr x (.inr (addr.trans hi))).trans (DescentStaticWordColumn.frame _ _ _ m x (.inr (by omega)))


end
end Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic.Placement

end OAI

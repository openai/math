import OAI.Hierarchy.DescentOperandPreparedPackets
import OAI.Hierarchy.DescentOperandPreparedPacketPhase

namespace OAI
/-! # Reading both field families from the same physically prepared packet image -/
namespace Hierarchy.DescentOperandRootPull
set_option quotPrecheck false
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan DescentFallbackPeriod.Projected
open DescentSixParty.Chronology DescentResetHostSize DescentHostDirectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
open private Hierarchy.DescentOperandRootPull.source_cast from OAI.Hierarchy.DescentOperandPreparedPackets
noncomputable section
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (book : RootBook n r D (2^r) cap field)

/-- Both extraction stages use the very same root book and actor addresses. -/
def preparedPair (ptr receivers groups blocks after : ℕ) : Pair :=
  ⟨a.headerEnd book,ptr,H,receivers,groups,blocks,field,M,after,D,cap,r,n⟩

local notation "pairAt" => preparedPair a book

/-- The two source operands of a prepared packet fit before its actual gather.
This address claim uses only the root book and the visible parent array. -/
theorem prepared_pair_fits (base ptr receivers groups blocks after : ℕ)
    (space : a.PreparedFits book) (ds : groups*blocks=2^c)
    (low : a.preparedEnd book≤base) (prev : ptr+span receivers≤base)
    (ha : 0<after) (hx : 0<blocks) : (pairAt ptr receivers groups blocks after).Fits w base :=by
  have original (f : Bool) : (pairAt ptr receivers groups blocks after).original f = a.gatheredOperand book ((pairAt ptr receivers groups blocks after).page f) := by
    have shape : (pairAt ptr receivers groups blocks after).groups*(pairAt ptr receivers groups blocks after).blocks=2^c := ds
    simp only [Pair.original,Pair.packed,shape]
    rfl
  exact
    ⟨fun f => (original f).symm ▸ ProtocolRAMGeneratedWrite.fits_mono _ low (a.gathered_fits book space ((pairAt ptr receivers groups blocks after).page f)),
      prev,ha,hx⟩

theorem prepared_pair_read (base ptr receivers groups blocks after : ℕ)
    (space : a.PreparedFits book) (before current : Memory w) (ds : groups*blocks=2^c)
    (fallback : Fin H→Fin (2^c)→Fin ((pairAt ptr receivers groups blocks after).stage 0 false).fields→Cell field)
    (matrix : Fin H→Fin (2^c)→Fin ((pairAt ptr receivers groups blocks after).stage 0 true).fields→Cell field)
    (fromFallback : Source (a.gatheredOperand book (fallbackPage r n))
      (fun v g=>encode field ((pairAt ptr receivers groups blocks after).stage 0 false).fields (fallback v g)) M (a.preparedImage book space before))
    (fromMatrix : Source (a.gatheredOperand book (matrixPage r n))
      (fun v g=>encode field ((pairAt ptr receivers groups blocks after).stage 0 true).fields (matrix v g)) M (a.preparedImage book space before))
    (kept : ∀ z<a.preparedEnd book,current z=a.preparedImage book space before z)
    (low : a.preparedEnd book ≤ base) (owner : Fin receivers→Fin H)
    (hM : 0<M) (ha : 0<after) (hx : 0<blocks)
    (directory : DescentResetStemKeyReindex.Directory ptr owner current) (prev : ptr+span receivers ≤ base)
    (room : (pairAt ptr receivers groups blocks after).endAddress base < 2^w) :
    ((pairAt ptr receivers groups blocks after).program base w).Exec current ((pairAt ptr receivers groups blocks after).image base current) ((pairAt ptr receivers groups blocks after).time base w) ∧
    CheapCode ((pairAt ptr receivers groups blocks after).program base w) ∧
    (∀ i x,((pairAt ptr receivers groups blocks after).src base false i x).Fits w ((pairAt ptr receivers groups blocks after).endAddress base) ∧ Source ((pairAt ptr receivers groups blocks after).src base false i x)
      (fun v g=>fallback (owner v) (Fin.cast ds (finProdFinEquiv (g,x))) i) after ((pairAt ptr receivers groups blocks after).image base current)) ∧
    (∀ i x,((pairAt ptr receivers groups blocks after).src base true i x).Fits w ((pairAt ptr receivers groups blocks after).endAddress base) ∧ Source ((pairAt ptr receivers groups blocks after).src base true i x)
      (fun v g=>matrix (owner v) (Fin.cast ds (finProdFinEquiv (g,x))) i) after ((pairAt ptr receivers groups blocks after).image base current)) ∧
    ∀ z,z<base ∨ (pairAt ptr receivers groups blocks after).endAddress base ≤ z → (pairAt ptr receivers groups blocks after).image base current z=current z := by
  let value : (f : Bool) → Fin H→Fin (2^c)→Fin ((pairAt ptr receivers groups blocks after).stage 0 f).fields→Cell field
    | false => fallback
    | true => matrix
  have original (f : Bool) : (pairAt ptr receivers groups blocks after).original f = a.gatheredOperand book ((pairAt ptr receivers groups blocks after).page f) := by
    have shape : (pairAt ptr receivers groups blocks after).groups*(pairAt ptr receivers groups blocks after).blocks=2^c := ds
    simp only [Pair.original,Pair.packed,shape]
    rfl
  have fromBook (f : Bool) : Source (a.gatheredOperand book ((pairAt ptr receivers groups blocks after).page f))
      (fun v g=>encode field ((pairAt ptr receivers groups blocks after).stage 0 f).fields (value f v g)) M (a.preparedImage book space before) := by
    cases f
    · exact fromFallback
    · exact fromMatrix
  have held : (pairAt ptr receivers groups blocks after).Fits w base :=
    ⟨fun f => (original f).symm ▸ ProtocolRAMGeneratedWrite.fits_mono _ low (a.gathered_fits book space ((pairAt ptr receivers groups blocks after).page f)),
      prev,ha,hx⟩
  have moved (f : Bool) : Source ((pairAt ptr receivers groups blocks after).original f)
      (fun v g=>encode field ((pairAt ptr receivers groups blocks after).stage 0 f).fields (value f v (Fin.cast ds g))) M current := by
    rw [original]
    let packet (v : Fin H) (g : Fin (2^c)) := encode field
      ((pairAt ptr receivers groups blocks after).stage 0 f).fields (value f v g)
    apply Hierarchy.DescentOperandRootPull.source_cast ds (a.gatheredOperand book ((pairAt ptr receivers groups blocks after).page f)) packet current
    intro row
    exact (eval_below _ _ _ current (a.gathered_fits book space ((pairAt ptr receivers groups blocks after).page f)) kept).trans (fromBook f row)
  have read := (pairAt ptr receivers groups blocks after).read base current (fun f v g=>value f v (Fin.cast ds g)) owner held hM moved directory room
  have run := (pairAt ptr receivers groups blocks after).any base current held room
  exact ⟨run.1,run.2.1,read false,read true,run.2.2⟩

end
end Hierarchy.DescentOperandRootPull

end OAI

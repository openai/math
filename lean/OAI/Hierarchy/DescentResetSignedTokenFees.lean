import OAI.Hierarchy.DescentResetSignedTokens
import OAI.Hierarchy.DescentVenueSlabTariff

namespace OAI
/-! Physical work for the signed-page retile, one shared token table and one
lookup per retiled input word. -/
namespace Hierarchy.DescentResetSignedTokens.Layout
open DescentSixParty.Chronology DescentStaticWordColumn ProbeStage.Native ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

def fees (s : Layout) : ℕ :=
  let entries:=2^(s.bits*s.targetLanes)
  DescentVenueSlabs.tariff s.venue+(4+10*entries+7*(15*(entries+1)))+
    (4+s.slots*(4+s.rows*28)+7*(15+s.slots*59))

theorem price (s : Layout) (base w : ℕ) (pages : s.Slot→Bank) (old : 0<s.sourceLanes)
    (next : 0<s.targetLanes) :
    (s.phase base w pages).ticks+7*names (s.phase base w pages).program≤ s.fees := by
  let lut:=s.dictionary base
  let es:=s.readers base
  have len : es.length=s.slots:=by simp [es,readers]
  have bound : ∀e∈es,e.work≤12:=by
    intro e he
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    exact Nat.le_refl 12
  have copied:=DescentVenueSlabs.price s.venue (s.inputs pages) base w old next
  have run:=columns_clock s.rows (s.start base) 12 es bound
  have hardware:=DescentOrdinaryAtomFieldRAM.ScalarOperand.labels_registers es (s.start base) s.rows 12 w bound
  change names (ProtocolRAM.program w (s.passes base))≤15+es.length*59 at hardware
  change ProtocolRAM.clock (s.passes base)≤4+es.length*(4+s.rows*28) at run
  rw [len] at run hardware
  change (DescentVenueSlabs.ticks s.venue (s.inputs pages) base+(4+10*lut.size)+
      ProtocolRAM.clock (s.passes base))+
      7*names (((DescentVenueSlabs.program s.venue (s.inputs pages) base w).seq
        (DescentStaticWordColumn.program w lut.base s.word lut.size)).seq
        (ProtocolRAM.program w (s.passes base)))≤_
  rw [names_seq,names_seq,names_mount]
  change _≤DescentVenueSlabs.tariff s.venue+(4+10*lut.size+7*(15*(lut.size+1)))+
    (4+s.slots*(4+s.rows*28)+7*(15+s.slots*59))
  omega

end
end Hierarchy.DescentResetSignedTokens.Layout

end OAI

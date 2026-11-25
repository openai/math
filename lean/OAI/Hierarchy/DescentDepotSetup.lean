import OAI.Hierarchy.DescentDepotStaticProgram
import OAI.Hierarchy.DescentMaskedLookupBook

namespace OAI
/-! # All public bytes needed by the ordinary donor stage from a single native program -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Setup
open DescentPacking.PackedMatch DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentSixParty.Chronology ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape) (K H J M unit : ℕ)
local notation "page" => DescentSIMDLookup.Book.words (totalBits s) H J M
local notation "rest" => Binary.words s z K H J M unit

def words := page+rest

variable (base B prof C pad scale b seats : ℕ)
local notation "second" => base+page
local notation "step" => Binary.phase s z K H J M unit second B prof C pad scale
local notation "rule" => output s B prof b seats
local notation "raw" => DescentSIMDLookup.Book.install rule H J M
local notation "rawMem" => DescentSIMDLookup.Book.image rule H J M base
local notation "freshBase" => second+Binary.count s*(2*2^(unit*M))

def phase (w : ℕ) : NativePhase w :=
  ⟨(raw w base).seq (step w).program,12+10*words s z K H J M unit,
    fun m=>(step w).image (rawMem m),cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (step w).cheap⟩
local notation "date" => phase s z K H J M unit base B prof C pad scale b seats

theorem mount {w : ℕ} (src top born : Bank) (m : Memory w) (large : 2*totalBits s+1≤unit)
    (room : base+words s z K H J M unit<2^w) :
    let new:=(date w).image m
    let rom:=DescentSIMDLookup.Book.banks base (totalBits s) H J M src
    (date w).Runs m ∧
      (∀i : Cell (totalBits s*M)⊕Fin (H*chunks J M),new (fixedAddr rom i)=fixedWord rule i) ∧
      Binary.Installed s M unit second new ∧
      Fresh.Fixed (H:=H) (G:=J) (M:=M) s z (Fresh.Book.bank s z K H J M freshBase top born) B prof C pad scale new ∧
      ∀x,x<base ∨ base+words s z K H J M unit≤x → new x=m x := by
  intro new rom
  have extent : second+rest<2^w:=by simpa only [words,Nat.add_assoc] using room
  obtain ⟨first,read,old,_⟩:=DescentSIMDLookup.Book.mount rule H J M base src m (by omega)
  obtain ⟨next,installed,fresh,frame⟩:=Binary.mount s z K H J M unit second B prof C pad scale top born (rawMem m) large extent
  refine ⟨?_,DescentSIMDLookup.Book.retain rule H J M base src (rawMem m) new read (fun i hi=>frame i (.inl hi)),
    installed,fresh,?_⟩
  · have time : 12+10*words s z K H J M unit=(4+10*page)+(8+10*rest) := by unfold words;ring
    change ((raw w base).seq (step w).program).Exec m new (12+10*words s z K H J M unit)
    rw [time]
    intro P R labels mach pc reg pub exit dec advice cfg init enter same
    exact Procedure.Exec.then first next mach pc reg pub exit dec advice cfg init enter same
  · intro x away
    unfold words at away
    exact (frame x (by omega)).trans (old x (by omega))

theorem names (w : ℕ) :
    DescentStaticWordColumn.names (date w).program=15*(words s z K H J M unit+3) := by
  simp only [phase,DescentStaticWordColumn.names_seq,DescentSIMDLookup.Book.install,
    DescentStaticWordColumn.names_mount,Binary.names,words]
  ring

theorem capacity (payload : ℕ) (large : 2*totalBits s+1≤unit) (enough : Fresh.laneWidth s z≤unit) :
    words s z K H J (lanes payload unit) unit ≤
      2*(H*chunks J (lanes payload unit))+(2*Binary.count s+3+K)*2^(payload/2) := by
  have a:=DescentSIMDLookup.Book.table_area (a:=totalBits s) H J payload unit (by omega)
  have bnd:=Binary.capacity s z K H J unit payload enough
  unfold words
  nlinarith only [a,bnd]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Setup

end OAI

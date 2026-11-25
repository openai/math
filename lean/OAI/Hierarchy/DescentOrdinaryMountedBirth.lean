import OAI.Hierarchy.DescentOrdinaryMountedInlet
import OAI.Hierarchy.DescentOrdinaryBornHeader

namespace OAI
/-! # The six physical newborn operand rows from the registered matcher chip -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentPackedColony DescentOrdinaryBorn DescentRawCablePanel DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)

def rowsAt {h g a H G b : ℕ} (hh : H=h) (gg : G=g) (bits : a=b)
    (data : Fin h→Fin g→Cell a) (i : Fin H) (j : Fin G) : Cell b :=
  Fin.cast (congrArg (fun n : ℕ=>2^n) bits) (data (Fin.cast hh i) (Fin.cast gg j))

theorem reads_at {h g a H G b M M' w : ℕ} (hh : H=h) (gg : G=g) (bits : a=b) (pitch : M'=M)
    {data : Fin h→Fin g→Cell a} {m : Memory w} {bank : Bank} (read : Reads bank data M m) :
    Reads bank (rowsAt hh gg bits data) M' m :=by
  cases hh
  cases gg
  cases bits
  cases pitch
  exact read

/-- Public equality of the encoder used by the legal donor publication and
the decoder used by the newborn argument book. -/
structure BirthShape : Prop where
  hosts : v.bornBook.hosts=A.clip.venue.hosts
  groups : v.bornBook.groups=A.clip.venue.groups
  width : DepotRAM.outputBits A.clip.venue.socket=v.bornBook.chipBits

variable (S : A.BirthShape v)
def nativeChips (parts : Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DepotRAM.Parts A.clip.venue.socket) :=
  rowsAt S.hosts S.groups S.width (fun h g=>DepotRAM.chip A.clip.venue.socket A.clip.venue.socket.cap
    A.clip.venue.profile v.gadget.b A.clip.venue.slots (parts h g))

theorem mounted_birth (floor : ℕ) {w : ℕ} (m : Memory w)
    (safe : A.Room v floor w) («matching» : A.Match v floor) (space : v.vectorStart floor<2^w)
    (positive : 0<A.clip.panelPitch)
    (parts : Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DepotRAM.Parts A.clip.venue.socket)
    (held : Reads A.venue.panel (fun h g=>DepotRAM.combine A.clip.venue.socket (parts h g)) A.clip.panelPitch m)
    (x t j a f) :
    Reads (v.bornBook.bank (v.birthStart floor) x t j a f)
      (fun h g=>component v.bornBook.bits (pointerAt v.bornBook.demand v.bornBook.grain v.bornBook.scale
        (chipDonor v.bornBook.format (A.nativeChips v S parts h g) (finProdFinEquiv (x,t))) j a.val) f)
      v.bornBook.lanes (A.mountedTape v floor m) :=by
  have size : (A.chip v).rows≤(A.chipBank v floor).size :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  change A.clip.venue.hosts * chunks A.clip.venue.groups A.clip.working ≤ (A.chipBank v floor).size at size
  have rooms : v.bornBook.rows≤(A.chipBank v floor).size:=by
    simpa only [DescentOrdinaryBorn.Chart.rows,S.hosts,S.groups,«matching».bornPitch] using size
  exact v.mount_reads floor (A.chipBank v floor) ((A.inlet v floor w).image m) (A.chip_fits v floor safe «matching»)
    (A.nativeChips v S parts) rooms (reads_at S.hosts S.groups S.width «matching».bornPitch (A.chip_final v floor m safe positive parts held))
    space x t j a f

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI

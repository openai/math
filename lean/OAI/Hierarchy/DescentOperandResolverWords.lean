import OAI.Hierarchy.DescentOrdinaryFragmentImage
import OAI.Hierarchy.DescentPackedMaskedData

namespace OAI
/-! Complete physical successor operands, including zero lanes in the last panel. -/
namespace Hierarchy.DescentPackedOperand.ROM
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section

theorem output_words (base k H G M w : ℕ) (banks : Fin 10→Bank) (x : Fin H→Fin G→Fragment k)
    (up : ∀i,(banks i).Fits w base) (cap : ∀i,H*chunks G M≤(banks i).size)
    (word : M*unit k≤w/2) (space : endAddress base k H G M<2^w) (m : Memory w)
    (src : ∀i (p : Row H G M),m ((banks i).base+(row H G M p).val)=((data (fun h g=>sourceFields (x h g) i) p).val:ℕ)) :
    ∀p : Row H G M, result base k H G M banks m (output base k H G M+(row H G M p).val)=
      ((data (fun h g=>DescentPackedOperand.word (x h g)) p).val:ℕ) := by
  intro p
  let L:=chart base k H G M banks
  let o:=output base k H G M
  let boot:=mounted base k H G M m
  have fits:=room base k H G M w banks up cap word space
  have loaded:=(installed base k H G M w banks x up cap m src space).2
  have stored:=(assemble L x o fits boot loaded).2
  have native:=(ProtocolRAMGeneratedWrite.read_image o (H*chunks G M) (lookup L.remap)
    (prepared L H G M boot) (row H G M p)).trans
      (lookup_read L.remap o fits.route (transition k) (fun h g=>packed (x h g)) _ stored p)
  change image o (H*chunks G M) (lookup L.remap) (prepared L H G M boot) (o+(row H G M p).val) = _
  simpa only [masked_eq_data, transition_read] using native

end
end Hierarchy.DescentPackedOperand.ROM

namespace Hierarchy.DescentOrdinaryLocalFragment
open DescentPackedOperand DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {k H G M w : ℕ}

theorem output_words (base : ℕ) (banks : Fin 10→Bank) (peer old role : Expr)
    (x : Fin H→Fin G→Fragment k) (peerAt oldAt roleAt : Fin H→Fin G→Cell (k+2)) (m : Memory w)
    (within : ∀h g,11*(oldAt h g).val+(roleAt h g).val<2^(k+2))
    (bankFit : ∀i,(banks i).Fits w base) (cap : ∀i,H*chunks G M≤(banks i).size)
    (priorRead : ∀i,Reads (banks i) (fun h g=>sourceFields (x h g) i) M m)
    (peerFit : peer.Fits w base) (oldFit : old.Fits w base) (roleFit : role.Fits w base)
    (peerRead : Source peer peerAt M m) (oldRead : Source old oldAt M m) (roleRead : Source role roleAt M m)
    (room : finish base k M (H*chunks G M)<2^w) (word : M*unit k≤w/2)
    (space : endAddress base k H G M<2^w) :
    let next_:=fun h g=>route (x h g) (peerAt h g) (DescentPackedRawTicket.payload oldAt roleAt within h g)
    ∀p : Row H G M, outputMemory base k H G M banks peer old role m
      (ROM.output (finish base k M (H*chunks G M)) k H G M+(row H G M p).val)=
      ((data (fun h g=>DescentPackedOperand.word (next_ h g)) p).val:ℕ) := by
  intro next_
  let n:=H*chunks G M
  let head:=finish base k M n
  have compiled:=run base banks peer old role x peerAt oldAt roleAt m within bankFit cap priorRead
    peerFit oldFit roleFit peerRead oldRead roleRead room
  exact ROM.output_words head k H G M w (fields base k M n banks) next_
    (fun j=>(ready_fields base banks j n bankFit cap room).1)
    (fun j=>(ready_fields base banks j n bankFit cap room).2) word space _ compiled.2.1

end
end Hierarchy.DescentOrdinaryLocalFragment

end OAI

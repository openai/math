import OAI.Hierarchy.DescentHaloPackedGather
import OAI.Hierarchy.DescentOrdinaryMarkRead

namespace OAI
/-! # Normalized mark reads on the deduplicated original halo -/
namespace Hierarchy.DescentOrdinarySignedMeta.MarkGather
open DescentSIMDLookup DescentSharedCableNames DescentOrdinaryAtomFieldRAM.ROM DescentPackedColony DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

theorem issued {w D cap H G M P : ℕ} (base : ℕ) (ports : Ports P) (prior : Bank)
    (R : Fin H→Fin P→Option (Fin H)) (path : Fin P) (newRole : Bool)
    (panel : Fin H→Fin G→Option (Stage.Live D cap)) (m : Memory w)
    (room : stop base D cap M<2^w) (access : Accessible ports prior H G M w base)
    (routing : Mounted ports (DescentHaloWalkRAM.Gather.select R) m G M)
    (stored : Reads prior (fun v g=>DescentSignedCableCodec.encode (panel v g)) M m) :
    let pg:=pages D cap M
    let bits:=width D cap M
    let dst:=after pg bits base m
    let source:=(lut base D cap M newRole).read (peerExpr ports prior H path) (.lit 0)
    (mount pg bits w base).Exec m dst (4+10*(4*2^bits)) ∧
      source.Fits w (stop base D cap M) ∧ Source source (fun v g=>flag newRole
        ((DescentHaloWalkRAM.Gather.select R v path).bind (fun donor=>panel donor g))) M dst :=
  issued_on base ports prior (DescentHaloWalkRAM.Gather.select R) path newRole panel m room access routing stored

end
end Hierarchy.DescentOrdinarySignedMeta.MarkGather

end OAI

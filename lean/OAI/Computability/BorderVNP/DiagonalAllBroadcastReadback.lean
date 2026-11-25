import OAI.Computability.BorderVNP.DiagonalNativeRouteInverse
import OAI.Computability.BorderVNP.RoutingISASignedPrepAllBroadcasts

/-! # Physical exterior and raw cube prefix of each reconstructed positive preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge) (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (S : SourceReports ar owners)
    (L : RawBroadcast ar → WireLayout (R+1) r link) (fixed : Block (R+1)) (header : RawBroadcast ar → List Bool)
    (pin : Fin d → Bool)

variable (pub : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → Arg → Word w)
    (mac : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → Bank w) (mem : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → Memory w)

variable (allowed : RawBroadcast ar → Prop)
    (checked : ∀ c : RawBroadcast ar, BroadcastPreparations ar id L header pub mac reg mem c → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners,
      allowed (routeBroadcast ar owners q).val)
    (frames : ∀ c : CheckedBroadcast ar, allowed c.val → PreparationFrame G (L c.val) ar (decodedBroadcast ar c.val)
      (header c.val) pin (pub c.val) (mac c.val) (reg c.val) (mem c.val))
    (builders : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).Builders fixed id owners)
    (source : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a))

local notation3 (prettyPrint := false) "joint" => allBroadcastPreparedEquiv G ar owners id S L fixed header pin
  pub mac reg mem allowed checked honest frames builders source

/-- Reconstructing a complete native preparation uses exactly the true
least-coordinate declaration of its routed cube assignment. -/
theorem allBroadcastPreparedEquiv_cube
    (q : {v : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners // S.pins v}) (reports : S.actual q.val) :
    ((joint).symm ⟨q,reports⟩).1 = (routeBroadcast ar owners q.val).val := rfl

set_option maxHeartbeats 60000 in
/-- Reconstructing a complete native preparation fills its whole physical
exterior with the original pin-induced data and the route assignment's
own shared words. The report values cannot change any of those wires. -/
theorem allBroadcastPreparedEquiv_exterior
    (q : {v : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners // S.pins v}) (reports : S.actual q.val) :
    let c := routeBroadcast ar owners q.val
    let f := frames c (honest q.val)
    ((joint).symm ⟨q,reports⟩).2.1.val = cubeExterior G (L c.val) f.tab f.row f.dataDir f.privatePlacement
      f.livePlacement f.guess f.rows (Scatter.Assignment.Routed.encode owners q.val).shared (header c.val) f.length := by
  intro c f
  exact PreparationFrame.sourceEquiv_exterior (G := G) (L := L c.val) (ar := ar)
    (decl := decodedBroadcast ar c.val) (header := header c.val) (pin := pin) (pub := pub c.val)
    (mac := mac c.val) (reg := reg c.val) (mem := mem c.val) (id := id) (owners := owners)
    fixed S f (builders c (honest q.val)) (source c (honest q.val))
    ⟨⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩,q.property⟩ reports

end TeamContraction

end BorderVNP
end Computability
end OAI

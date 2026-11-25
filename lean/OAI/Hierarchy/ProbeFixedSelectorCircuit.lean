import OAI.Hierarchy.ProbeSelectorShelf
import OAI.Hierarchy.ProbeBroadcastSignedSite

namespace OAI
/-! # Data-independent signed site wiring reads the real exposed counter bank -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Routing Diagonal MotifOuterTerms MotifBinaryPacking TraceCircuit
open scoped Classical BigOperators

variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B] {k r : ℕ}
  [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}

/-- The three networks in this coefficient depend on the batch size,
alphabet, tree and single-copy matrices. All changing counter data enter
as pins. The low bits of one real incident wire deliver the selector word. -/
theorem Packet.fixed_signed_site (P : Packet F edge req) (rt : Fin k) (G : PortGraph (Fin k) B)
    (h : Histogram (Fin P.terms) r) (i : Fin k) (p : (portGraph k).Port i)
    (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1)
    (x : State (P.inputWidths r) i) (z : State (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits)) i) :
    let q:=G.chordWidths (fun _=>r*P.selectorBits)
    let yz:=splitPortState (P.outputWidths h) q i z
    let c:=BroadcastPins.candidate q i p yz.2 (r*P.selectorBits)
    let digits:=Nat.clog 2 (r+1)
    let «public»:=SelectorShelf.bits h digits
    let privateWord:=(blocks r P.selectorBits).symm ((word _).symm c)
    P.broadcastMatrix rt r G h i x z=
      TypedWiring.value (BroadcastPins.network F q i p fit) (BroadcastPins.read q i yz.2) *
      ((SelectorShelf.network F (NativeHistogram.alphabet_pos P) r P.selectorBits digits).eval
         (SelectorShelf.pins privateWord «public») *
       TypedWiring.value (SiteHardware.typedSite P i r) (P.rawSiteView h i c x yz.1)) := by
  intro q yz c digits «public» privateWord
  have room : r<2^digits := Nat.lt_of_succ_le (Nat.le_pow_clog (by decide : 1<2) _)
  have code:=SelectorShelf.fixed_target (F:=F) (NativeHistogram.alphabet_pos P) privateWord h room
  change (SelectorShelf.network _ _ _ _ _).eval (SelectorShelf.pins privateWord «public»)=_ at code
  rw [code]
  simpa only [privateWord,Equiv.apply_symm_apply] using P.physical_signed_site rt G h i p fit x z

/-- The total trivalent size of all three physical components, including
the counter checker whenever its field values vary with the branch. -/
theorem Packet.fixed_signed_cost (P : Packet F edge req) (G : PortGraph (Fin k) B)
    (i : Fin k) (p : (portGraph k).Port i)
    (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1) :
    let q:=G.chordWidths (fun _=>r*P.selectorBits)
    let letters:=P.terms
    let code:=P.selectorBits
    let d:=SiteHardware.widthCap (SiteHardware.socketWidth (P.width • demandWidths edge req)
      (fun h=>optionWidths edge (P.count h)) i)
    let sockets:=Fintype.card (SiteHardware.Sockets i)
    let eqn:=BroadcastPins.network F q i p fit
    let hist:=SelectorShelf.network F (NativeHistogram.alphabet_pos P) r code (Nat.clog 2 (r+1))
    let data:=SiteHardware.typedSite P i r
    eqn.cells+eqn.internal+(hist.cells+hist.internal)+(data.cells+data.internal) ≤
      Fintype.card ((portGraph k).Port i)*(Fintype.card B*(r*code))+
      ((r*(2^(code+letters)*(code+letters+1))+r*letters+r*2^(code+letters)+
          128000*letters*(r+1)*(Nat.log 2 (r+1)+2)^3)+letters*r+letters*((r+1)*Nat.clog 2 (r+1)))+
      (r*(2^(code+(sockets*d+sockets*d))*((code+(sockets*d+sockets*d))+2))+2*(sockets*(r*d))+
          128000*sockets*(r*d+1)*(Nat.log 2 (r*d+1)+2)^3) := by
  exact Nat.add_le_add (Nat.add_le_add (BroadcastPins.per_copy (F:=F) G i p fit)
    (SelectorShelf.cost (F:=F) (r:=r) (b:=P.selectorBits) (d:=Nat.clog 2 (r+1))
      (NativeHistogram.alphabet_pos P))) (P.site_cost i r)

end Hierarchy.Probe
end

end OAI

import OAI.Hierarchy.ProbeFixedSelectorCircuit

namespace OAI
/-! # The signed packet, count checker and broadcast comparison in one trivalent net -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Routing Diagonal MotifOuterTerms MotifBinaryPacking TraceCircuit MotifSelectorChecks
open scoped Classical BigOperators

namespace SiteHardware
variable {F : Type*} [CommRing F] {a b : ℕ}

private def pairCells (L : BitNetwork F a) (R : BitNetwork F b) : Bool → Component F 0 (a+b)
  | true => ⟨_,L,fun i=>.pin (i.castAdd b)⟩
  | false => ⟨_,R,fun j=>.pin (Fin.natAdd a j)⟩

def consecutive (L : BitNetwork F a) (R : BitNetwork F b) : BitNetwork F (a+b) :=
  BitNetwork.glue (fun i=>(pairCells L R i).net) (fun i=>(pairCells L R i).wire)

theorem consecutive_eval (L : BitNetwork F a) (R : BitNetwork F b) (x : Fin a→Bool) (y : Fin b→Bool) :
    (consecutive L R).eval (Fin.append x y)=L.eval x*R.eval y := by
  simp [consecutive,BitNetwork.glue_eval,pairCells,BitSource.read,-Fin.natAdd_eq_addNat]

omit [CommRing F] in
theorem consecutive_cost (L : BitNetwork F a) (R : BitNetwork F b) :
    (consecutive L R).cells+(consecutive L R).internal=L.cells+L.internal+(R.cells+R.internal) := by
  simp only [consecutive,BitNetwork.glue_cells,BitNetwork.glue_internal,Fintype.sum_bool,pairCells]
  omega
end SiteHardware

variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B] {k r : ℕ}
  [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}

def Packet.terminal (P : Packet F edge req) (G : PortGraph (Fin k) B) (i : Fin k)
    (p : (portGraph k).Port i) (room : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1) :=
  SiteHardware.consecutive (BroadcastPins.network F (G.chordWidths (fun _=>r*P.selectorBits)) i p room)
    (SiteHardware.consecutive (SelectorShelf.network F (NativeHistogram.alphabet_pos P) r P.selectorBits (Nat.clog 2 (r+1)))
      (SiteHardware.typedSite P i r))

theorem Packet.terminal_eval (P : Packet F edge req) (rt : Fin k) (G : PortGraph (Fin k) B)
    (h : Histogram (Fin P.terms) r) (i : Fin k) (p : (portGraph k).Port i)
    (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1)
    (x : State (P.inputWidths r) i) (z : State (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits)) i) :
    let q:=G.chordWidths (fun _=>r*P.selectorBits)
    let yz:=splitPortState (P.outputWidths h) q i z
    let c:=BroadcastPins.candidate q i p yz.2 (r*P.selectorBits)
    let digits:=Nat.clog 2 (r+1)
    let privateWord:=(blocks r P.selectorBits).symm ((word _).symm c)
    let v:=Fin.append (BroadcastPins.read q i yz.2 ∘ (Fintype.equivFin _).symm)
      (Fin.append (SelectorShelf.pins privateWord (SelectorShelf.bits h digits))
        (P.rawSiteView h i c x yz.1 ∘ (Fintype.equivFin _).symm))
    (P.terminal G i p fit).eval v=P.broadcastMatrix rt r G h i x z := by
  intro q yz c digits privateWord v
  rw [P.fixed_signed_site rt G h i p fit x z]
  simp only [v,terminal,SiteHardware.consecutive_eval]; rfl

theorem Packet.terminal_cost (P : Packet F edge req) (G : PortGraph (Fin k) B) (i : Fin k) (p : (portGraph k).Port i)
    (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1) :
    (P.terminal G i p fit).cells+(P.terminal G i p fit).internal=
      (let N:=BroadcastPins.network F (G.chordWidths (fun _=>r*P.selectorBits)) i p fit;N.cells+N.internal)+
      (let N:=SelectorShelf.network F (NativeHistogram.alphabet_pos P) r P.selectorBits (Nat.clog 2 (r+1));N.cells+N.internal)+
      (let N:=SiteHardware.typedSite P i r;N.cells+N.internal) := by
  simp only [terminal,SiteHardware.consecutive_cost,Nat.add_assoc]

end Hierarchy.Probe
end

end OAI

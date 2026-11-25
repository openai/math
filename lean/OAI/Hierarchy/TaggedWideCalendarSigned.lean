import OAI.Hierarchy.ProbeSignedTerminalFeed
import OAI.Hierarchy.ProbeAwayPartyBits

namespace OAI
/-! # The signed circuit on a retained party's two packed socket banks -/

noncomputable section
namespace Hierarchy.Probe.SiteHardware
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal MotifOuterTerms MotifBinaryPacking TraceCircuit
open scoped Classical BigOperators
variable {F V E A B : Type} [Field F] [Fintype V] [Fintype E] [Fintype A] [Fintype B]
    {k r cap : ℕ} [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}
    (P : Packet F edge req) (G : PortGraph (Fin k) B) (i : Fin k) (p : (portGraph k).Port i)
local notation "q" => G.chordWidths (fun _=>r*P.selectorBits)
variable (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1)
    (meterPin : Fin P.terms→Fin (Nat.clog 2 (r+1))→V⊕Bool)
    (socket : Sockets i→Fin cap→V⊕Bool)

private def literal (u : V⊕Bool) : BitSource 0 (Fintype.card V) :=
  Sum.elim (fun v=>.pin (Fintype.equivFin _ v)) .constant u

private theorem literal_read (u : V⊕Bool) (v : V→Bool) (empty : Fin 0→Bool) :
    (literal u).read empty (v ∘ (Fintype.equivFin _).symm)=Sum.elim v id u := by
  cases u <;>simp [literal,BitSource.read]

private def tapWire (tap : Open i cap (Fintype.card V)) : BitSource 0 (Fintype.card V) :=
  match tap with
  | .hidden h =>
    let b:=finProdFinEquiv.symm h
    literal (socket ((Fintype.equivFin _).symm b.1) b.2)
  | .pin j => .pin j
  | .constant bit => .constant bit

local notation "counter" => fun a j=>Sum.map (Fintype.equivFin V) id (meterPin a j)

/-- Every input of the three constituent factors is a literal bank or counter read.
The socket-numbering conventions are the same ones used by the fixed packet terminal. -/
def signedProgram : BitNetwork F (Fintype.card V) :=
  BitNetwork.glue (fun _ : Unit=>P.terminal G i p fit)
    (fun _ j=>tapWire i socket (P.terminalFeed G i p fit counter j))

theorem signedProgram_cost :
    (signedProgram P G i p fit meterPin socket).cells+(signedProgram P G i p fit meterPin socket).internal=
      (P.terminal G i p fit).cells+(P.terminal G i p fit).internal := by
  simp [signedProgram,BitNetwork.glue_cells,BitNetwork.glue_internal]

theorem signedProgram_value (rt : Fin k) (h : Histogram (Fin P.terms) r) (v : V→Bool)
    (a : State (P.inputWidths r) i) (z : State (P.outputWidths h+q) i)
    (capacity : ∀s : (portGraph k).Port i,q s.val.1+r*widthCap (localWidth P i)≤cap)
    (meter : ∀t j,Sum.elim v id (meterPin t j)=SelectorShelf.bits h _ t j)
    (before : ∀t j,Sum.elim v id (socket (.inl t) j)=(a t).val.testBit j.val)
    (middle : ∀t j,Sum.elim v id (socket (.inr t) j)=(z t).val.testBit j.val) :
    TypedWiring.value (signedProgram P G i p fit meterPin socket) v=P.broadcastMatrix rt r G h i a z := by
  let env:=v ∘ (Fintype.equivFin V).symm
  have counts (t j) : Sum.elim env id (counter t j)=SelectorShelf.bits h _ t j := by
    cases e:meterPin t j <;> simpa [env,e] using meter t j
  rw [TypedWiring.value,signedProgram,BitNetwork.glue_eval,Fintype.sum_unique,Fintype.prod_unique]
  refine Eq.trans (congrArg (P.terminal G i p fit).eval ?_)
    (P.terminalFeed_value G i p rt h fit counter env a z capacity counts)
  funext j
  cases e : P.terminalFeed (cap:=cap) G i p fit counter j with
  | pin u => rfl
  | constant b => rfl
  | hidden u =>
    obtain ⟨⟨s,d⟩,rfl⟩:=finProdFinEquiv.surjective u
    obtain ⟨s,rfl⟩:=(Fintype.equivFin (Sockets i)).surjective s
    simp only [tapWire,Equiv.symm_apply_apply,halves,blocks_at,BitSource.read]
    cases s with
    | inl t => cases addr : socket (.inl t) d <;> simpa [literal,addr] using before t d
    | inr t => cases addr : socket (.inr t) d <;> simpa [literal,addr] using middle t d

end Hierarchy.Probe.SiteHardware

namespace Hierarchy.WireTelescope.ChosenPackets.Placed
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open Probe AdaptiveProbe
open scoped Classical BigOperators
variable {F : Type} [Field F] {S r : ℕ} (P : Placed F S)
    (h : Histogram (Fin P.data.terms) r) (i : Fin P.sites)

theorem placedInput : placeWidths P.place (P.data.inputWidths r)=P.wants r := by
  let : Nonempty (Fin S) := ⟨P.place P.root⟩
  exact physical_demand (edge:=P.edge) (req:=P.wanted) P.place P.data.width r

theorem placedOutput :
    placeWidths P.place (P.data.outputWidths h+P.graph.chordWidths (fun _=>r*P.data.selectorBits))=P.offers h := by
  let : Nonempty (Fin S) := ⟨P.place P.root⟩
  rw [map_add]
  exact congrArg (fun u=>u+placeWidths P.place (P.graph.chordWidths (fun _=>r*P.data.selectorBits)))
    (physical_histogram_width P.data h P.place)

omit [Field F] in
private theorem transported_entry {U V U' V' : Widths S} (hu : U=U') (hv : V=V')
    (M : SiteMatrix (State U) (State V) F) (M' : SiteMatrix (State U') (State V') F)
    (same : HEq M M') (s : Fin S) (x : State U' s) (y : State V' s) :
    M' s x y=M s (cast (congrArg (fun W=>State W s) hu.symm) x) (cast (congrArg (fun W=>State W s) hv.symm) y) := by
  subst U'; subst V'; cases same; rfl

/-- The unique local party above its physical site contributes exactly its signed
coefficient with the actual oriented physical state reads on both sides. -/
theorem signed_at (x : State (P.wants r) (P.place i)) (y : State (P.offers h) (P.place i)) :
    P.signed r h (P.place i) x y=P.data.broadcastMatrix P.root r P.graph h i
      (PhysicalMatrix.read P.place _ i (cast (congrArg (fun W=>State W (P.place i)) (P.placedInput (r:=r)).symm) x))
      (PhysicalMatrix.read P.place _ i (cast (congrArg (fun W=>State W (P.place i)) (P.placedOutput h).symm) y)) := by
  let M:=P.data.broadcastMatrix P.root r P.graph h
  have eqn : HEq (PhysicalMatrix.matrix P.place M) (P.signed r h) := by
    apply HEq.symm
    unfold Placed.signed PhysicalMatrix.packetMatrix
    first | exact cast_heq _ _
  rw [transported_entry (P.placedInput (r:=r)) (P.placedOutput h) _ _ eqn]
  let : Unique {t // P.place t=P.place i} :=
    {default:=⟨i,rfl⟩,uniq:=fun t=>Subtype.ext (P.place.injective t.property)}
  rw [PhysicalMatrix.matrix,Fintype.prod_unique]
  rfl

end Hierarchy.WireTelescope.ChosenPackets.Placed
end

end OAI

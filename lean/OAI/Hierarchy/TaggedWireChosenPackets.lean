import OAI.Hierarchy.TaggedWirePlacedBroadcast
import OAI.Hierarchy.TaggedWireNativePassMatrix
import OAI.Hierarchy.TaggedWireChosenTape

namespace OAI
/-! # The actual histogram choice is the signed operator's branch index -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open Probe AdaptiveProbe
open scoped BigOperators Classical

variable {F : Type} [Field F] {S : ℕ}

/-- The genuine typed finite role/demand/tree populations of the menu. Their
distinct indices remain separate even when their physical endpoints coincide. -/
structure Placed (F : Type) [Field F] (S : ℕ) where
  sites : ℕ
  [nonemptySites : Nonempty (Fin sites)]
  Edges : Type
  Requests : Type
  Tree : Type
  [edgesFinite : Fintype Edges]
  [requestsFinite : Fintype Requests]
  [treeFinite : Fintype Tree]
  edge : Edges→Chord sites
  wanted : Requests→Edges
  data : Packet F edge wanted
  place : Fin sites ↪ Fin S
  root : Fin sites
  graph : PortGraph (Fin sites) Tree
  connected : BroadcastConnected graph

attribute [instance] Placed.nonemptySites Placed.edgesFinite Placed.requestsFinite Placed.treeFinite

namespace Placed
variable (P : Placed F S)
def wants (copies : ℕ) := optionWidths (fun a=>physicalChord P.place (P.edge (P.wanted a))) (fun _=>copies*P.data.width)
def offers {copies : ℕ} (c : Histogram (Fin P.data.terms) copies) :=
  optionWidths (fun a=>physicalChord P.place (P.edge a)) (histWidth P.data.count c)+
    placeWidths P.place (P.graph.chordWidths (fun _=>copies*P.data.selectorBits))
def signed (copies : ℕ) (c : Histogram (Fin P.data.terms) copies) :
    SiteMatrix (State (P.wants copies)) (State (P.offers c)) F := by
  letI : Nonempty (Fin P.sites):=⟨P.root⟩
  exact PhysicalMatrix.packetMatrix P.data P.place P.root copies P.graph c

theorem signed_sum (copies : ℕ) (x : ∀s,State (P.wants copies) s) :
    (raw F (P.wants copies)).coeff x=∑c,SiteMatrix.act (P.signed copies c) (raw F (P.offers c)).coeff x := by
  let : Nonempty (Fin P.sites):=⟨P.root⟩
  exact PhysicalMatrix.packetMatrix_action P.data P.place P.root copies P.graph P.connected x
end Placed

/-- Each native candidate either chose an actual menu packet, or has zero
copies. In the latter case its padded counters have just one possible value. -/
inductive Row (F : Type) [Field F] (S : ℕ) : ℕ→ℕ→Type 1
  | skipped (letters : ℕ) : Row F S letters 0
  | packet (P : Placed F S) (copies : ℕ) : Row F S P.data.terms copies

namespace Row
def input {H r : ℕ} : Row F S H r→Widths S
  | .skipped _=>0
  | .packet P m=>P.wants m
def output {H r : ℕ} : (v : Row F S H r)→Histogram (Fin H) r→Widths S
  | .skipped _,_=>0
  | .packet P _,j=>P.offers j
def entry {H r : ℕ} (v : Row F S H r) (j : Histogram (Fin H) r) : SiteMatrix (State v.input) (State (v.output j)) F := by
  cases v with
  | skipped h=>exact SiteMatrix.identity (State 0)
  | packet P r=>exact P.signed r j

theorem sum {H r : ℕ} (v : Row F S H r) (x : ∀s,State v.input s) :
    (raw F v.input).coeff x=∑j,SiteMatrix.act (v.entry j) (raw F (v.output j)).coeff x := by
  cases v with
  | packet P r=>exact P.signed_sum r x
  | skipped H=>
    let zero : Histogram (Fin H) 0 := ⟨fun _=>0,by simp⟩
    let : Unique (Histogram (Fin H) 0) := ⟨⟨zero⟩,fun c=>Subtype.ext (funext fun i=>Fin.ext (by
      change (c.val i).val=0
      have bound := (c.val i).isLt
      omega))⟩
    simp only [Fintype.sum_unique]
    exact (SiteMatrix.act_id (B:=State (0 : Widths S)) (raw F (0 : Widths S)).coeff x).symm
end Row

variable {n : ℕ} (letters copies : Fin n→ℕ)
variable (batch : ∀i,Row F S (letters i) (copies i))

/-- In particular, dormant and padding rows add exactly one summand while
active candidates use their original rectangular tape's genuine histogram. -/
theorem pass_action (rest : Widths S) (x : ∀s,State (rest+∑i,(batch i).input) s) :
    (raw F (rest+∑i,(batch i).input)).coeff x=
      ∑c : BallChoices letters copies,SiteMatrix.act (PassMatrix.matrix (fun i j=>(batch i).entry j) rest c)
        (raw F (rest+∑i,(batch i).output (c i))).coeff x :=
  PassMatrix.action (fun i j=>(batch i).entry j) (fun i=>(batch i).sum) rest x

end Hierarchy.WireTelescope.ChosenPackets

end
end OAI

import OAI.Hierarchy.TaggedWireEarnedTender
import OAI.Hierarchy.TaggedWirePacketOffsite
import OAI.Hierarchy.TaggedWirePacketPostAway

namespace OAI
/-! # The selected two-radius installation at sites outside its actual participant set -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing
variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball : Type} [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
local notation "G" => Commodity (Fin (2^h)) (Stages h d) k
local notation "shift" => Fintype.card G
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K} {pad : Chord K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
local notation "roles" => ColumnWires.ends (horizontal n) extra
local notation "own" => Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)
local notation "enum" => treeFirst R T
local notation "order" => (Fintype.equivFin ((i : Fin (Fintype.card U)) × Fin (menuLen (enum i)))).symm

namespace EarnedInstall
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)

local notation "old" => retained (b:=b) addr
local notation "fwd" => Fin.natAdd shift
local notation "pr" => primaryRow (b:=b) old fwd g.index
local notation "ma" => (fun c j=>fwd (g.mate c j))
local notation "tr" => (fun j:T=>fwd (g.index (treeRole n k j)))
local notation "walk" => Sum.elim (links (horizontal n) extra place u pr ma) (fun j:T=>[tr j]) ∘ enum

variable {F J : Type} [Field F] [Fintype J] (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (req : J → ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)
    (rt : Fin (Fintype.card (TreeSite n k))) (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (Strip.horizontal n) extra e)) req)
    (copies : ℕ)
local notation "row" => Row.packet (stripPacket labels roles req place u rt P) copies

variable (pad : Chord K)
local notation "phys" => installedRows π endRow name pad
local notation "chosen" => g.tender labels req rt P copies pad
open scoped BigOperators

variable (hist : Histogram (Fin P.terms) copies) (s : Fin K) (outside : ∀x,place (u,x)≠s)
include outside in
theorem avoids (r : U) :
    ((chosen).source r).1.1≠s ∧ ((chosen).source r).1.2≠s ∧
    ∀e∈(chosen).install.route r,(phys e).1.1≠s ∧ (phys e).1.2≠s := by
  cases r with
  | inl r=>
    have direct:=reported_away place roles r s outside
    exact ⟨direct.1,direct.2,links_away phys (horizontal n) extra place u pr ma (g.faces pad).1 (g.faces pad).2.1 s outside r⟩
  | inr j=>
    have direct:=reported_away place (treeEnds n k) j s outside
    refine ⟨direct.1,direct.2,?_⟩
    intro e inside
    change e∈[tr j] at inside
    have eq:=List.mem_singleton.mp inside
    rw [eq,(g.faces pad).2.2 j]
    exact direct

include outside in
theorem tender_away :
    ∀a b,Installs.transport ((chosen).shape hist) rfl
      ((chosen).install.operator (F:=F) (chosen).order ((chosen).bits hist) (chosen).ordinal) s a b=1 := by
  apply (chosen).install_off_site hist s
  · exact paths_length (horizontal n) extra place u pr ma tr
  · intro r _
    exact g.avoids labels req rt P copies pad s outside r

include outside in
theorem post_away : Subsingleton (State ((chosen).post hist) s) :=
  (chosen).post_off_site hist s (fun r _=>(g.avoids labels req rt P copies pad s outside r).2.2)

end EarnedInstall
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI

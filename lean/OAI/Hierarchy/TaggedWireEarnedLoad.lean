import OAI.Hierarchy.TaggedWireEarnedTender
import OAI.Hierarchy.TaggedWireStripLoads

namespace OAI
/-! # The catalogued multiplicity of each edge in the very same physical routing -/
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
local notation "phys" => installedRows π endRow name pad
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
local notation "chosen" => g.tender labels req rt P copies pad
open scoped BigOperators

theorem tender_load (hist : Histogram (Fin P.terms) copies) (v : Fin (shift+b.rows)) :
    (chosen).install.load ((chosen).bits hist) v =
      (∑r : R,if pr r=v then histWidth P.count hist r else 0)+
      (∑r : R,match r with
        | .catalyst c j => if ma c j=v then histWidth P.count hist r else 0
        | _ => 0)+
      (∑j : T,if tr j=v then copies*P.selectorBits else 0) := by
  have parts := stream_load extra place u b old fwd g.index g.mate
    (histWidth P.count hist) (fun _=>copies*P.selectorBits) v
  refine Eq.trans ?_ (parts.trans ?_)
  · first
    | rfl
  · apply congrArg₂ Nat.add
    · apply congrArg₂ Nat.add
      · apply Finset.sum_congr (Finset.ext (fun _=>by simp))
        intro r _
        by_cases hv : pr r=v <;> simp only [hv,ite_eq_left,ite_eq_right,not_false_eq_true]
      · apply Finset.sum_congr (Finset.ext (fun _=>by simp))
        intro r _
        cases r with
        | catalyst c j => by_cases hv : ma c j=v <;> simp [hv]
        | _ => rfl
    · apply Finset.sum_congr (Finset.ext (fun _=>by simp))
      intro j _
      by_cases hv : tr j=v <;> simp [hv]

end EarnedInstall
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI

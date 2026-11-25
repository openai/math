import OAI.Hierarchy.TaggedWireStripPacketReads
import OAI.Hierarchy.TaggedWirePacketBanks

namespace OAI
/-! # Source-bank fit propagates through the physical ballot menu for one or two radii -/
noncomputable section
namespace Hierarchy.WireTelescope.StripPaths
open LinearAlgebra.SpectralBooks ChordGraph Probe AdaptiveProbe AdaptiveProbe.Strip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM Calendar.CatalogueRows PacketTurns
variable {n k K N Rn W out : ℕ} {A B Ball : Type}
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
variable (extra : A⊕B→DistinctPair (TreeSite n k)) (site : TreeSite n k→Expr) (mounted : ∀x,(site x).Fits W out)
include mounted

theorem face_resident (p : DistinctPair X) (b : Bool) : (face site p b).Fits W out := by
  cases b <;> exact ⟨mounted _,mounted _,mounted _,mounted _⟩

theorem routed_resident (pr : R→Expr) (ma : C→Fin k→Expr) (tr : T→Expr)
    (primary : ∀r,(pr r).Fits W out) (mate : ∀c j,(ma c j).Fits W out) (tree : ∀t,(tr t).Fits W out)
    (r : U) (j : ℕ) : (routedWord extra site pr ma tr r j).Fits W out := by
  rcases r with r|t
  · cases r with
    | catalyst c a=>
      change (orderedWord _ _ (decide (j≠0)) _ _).Fits W out
      cases decide (j≠0) <;> exact ⟨mounted _,mounted _,by first | exact primary _ | exact mate _ _,
        by first | exact primary _ | exact mate _ _⟩
    | radius c a z=>exact primary (.radius c a z)
    | cross c a l r=>exact primary (.cross c a l r)
    | horizontal f l=>exact primary (.horizontal f l)
    | extra e=>exact primary (.extra e)
  · exact tree t

theorem inputs_resident (place : Ball×X↪Fin K) (u : Ball) (pr : R→Fin N) (ma : C→Fin k→Fin N)
    (tr : T→Fin N) (enum : Fin Rn≃U) (primary : R→Expr) (mate : C→Fin k→Expr) (tree : T→Expr) (qty : U→Expr)
    (primaryOk : ∀r,(primary r).Fits W out) (mateOk : ∀c j,(mate c j).Fits W out)
    (treeOk : ∀t,(tree t).Fits W out) (qtyOk : ∀r,(qty r).Fits W out) :
    (packetInputs extra place u pr ma tr enum site primary mate tree qty).Resident W out := by
  refine ⟨fun i b=>face_resident site mounted _ b,fun i=>qtyOk _,?_,?_⟩
  · intro i j;exact routed_resident extra site mounted _ _ _ primaryOk mateOk treeOk _ _
  · intro i j b
    exact routed_resident extra site mounted _ _ _ (fun _=>face_resident site mounted _ b)
      (fun _ _=>face_resident site mounted _ b) (fun _=>face_resident site mounted _ b) _ _

end Hierarchy.WireTelescope.StripPaths

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope StripPaths PacketTurns
open LinearAlgebra.SpectralBooks ChordGraph
variable {h d k K n Rn native out : ℕ} {S : PurchaseSampler} {A B Ball : Type} [Fintype A] [Fintype B]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T

omit [Fintype A] [Fintype B] in
theorem StripPorts.packet_resident (p : StripPorts S h d k C (Fin n) B) (b : Board) (shift : ℕ)
    (extra : A⊕B→DistinctPair X) (place : Ball×X↪Fin K) (u : Ball)
    (pr : R→Fin (shift+b.rows)) (ma : C→Fin k→Fin (shift+b.rows)) (tr : T→Fin (shift+b.rows))
    (enum : Fin Rn≃U) (site : X→Expr) (stored : A→Expr) (qty : U→Expr)
    (src : ∀r : R,(p.primary b r).Fits native out) (sites : ∀x,(site x).Fits native out)
    (stock : ∀a,(stored a).Fits native out) (sizes : ∀r,(qty r).Fits native out) :
    (packetInputs extra place u pr ma tr enum site (readPrimary stored shift (p.primary b))
      (emitterMate (A:=A) p b shift) (emitterTree (A:=A) p b shift) qty).Resident native out := by
  apply WireTelescope.StripPaths.inputs_resident extra site sites place u pr ma tr enum _ _ _ qty
  · intro r
    cases r with
    | catalyst c j=>exact ⟨trivial,src (.catalyst c j)⟩
    | radius c j b=>exact ⟨trivial,src (.radius c j b)⟩
    | cross c j b l=>exact ⟨trivial,src (.cross c j b l)⟩
    | horizontal c j=>exact ⟨trivial,src (.horizontal c j)⟩
    | extra e=>cases e with
      | inl a=>exact stock a
      | inr b=>exact ⟨trivial,src (.extra (.inr b))⟩
  · intro c j;exact ⟨trivial,src (.radius c j true)⟩
  · intro j;exact ⟨trivial,src (treeRole n k j)⟩
  · exact sizes

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI

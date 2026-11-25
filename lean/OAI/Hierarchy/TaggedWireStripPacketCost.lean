import OAI.Hierarchy.TaggedWireStripPacketReads
import OAI.Hierarchy.TaggedWirePacketFieldCost
import OAI.Hierarchy.ProtocolRAMStripNativeCost

namespace OAI
/-! # Instruction work of the actual primary/mate inputs feeding the selected candidate -/

noncomputable section
namespace Hierarchy.WireTelescope.StripPaths
open LinearAlgebra.SpectralBooks ChordGraph Probe AdaptiveProbe AdaptiveProbe.Strip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM Calendar.CatalogueRows PacketTurns

variable {n k K N Rn : ℕ} {A B Ball : Type}
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
variable (extra : A⊕B→DistinctPair (TreeSite n k)) (site : TreeSite n k→Expr)

theorem ordered_work (a b : Expr) (right : Bool) (x y : Expr) :
    (orderedWord a b right x y).work=a.work+b.work+x.work+y.work+1 := by
  cases right <;> simp [orderedWord,Expr.work]; omega

theorem face_work (b : ℕ) (mounted : ∀x,(site x).work≤b) (p : DistinctPair X) (side : Bool) :
    (face site p side).work≤4*b+1 := by
  rw [face,ordered_work];have l:=mounted p.left;have r:=mounted p.right;omega

theorem routed_work (pr : R→Expr) (ma : C→Fin k→Expr) (tr : T→Expr) (b d : ℕ)
    (mounted : ∀x,(site x).work≤b) (primary : ∀r,(pr r).work≤d) (mate : ∀c j,(ma c j).work≤d)
    (tree : ∀t,(tr t).work≤d) (r : U) (j : ℕ) :
    (routedWord extra site pr ma tr r j).work≤2*b+2*d+1 := by
  have single : d ≤ 2*b+2*d+1 := by omega
  rcases r with r|t
  · change (hopWord (horizontal n) extra site pr ma r j).work ≤ 2*b+2*d+1
    cases r with
    | catalyst c a=>
      let ep:=ColumnWires.ends (horizontal n) extra (.catalyst c a)
      change (orderedWord (site ep.left) (site ep.right) _ (pr (.catalyst c a)) (ma c a)).work≤_
      rw [ordered_work]
      have l:=mounted ep.left;have r:=mounted ep.right;have p:=primary (.catalyst c a);have q:=mate c a;omega
    | radius c a z=>exact (primary (.radius c a z)).trans single
    | cross c a l r=>exact (primary (.cross c a l r)).trans single
    | horizontal f l=>exact (primary (.horizontal f l)).trans single
    | extra e=>exact (primary (.extra e)).trans single
  · exact (tree t).trans single

theorem inputs_bound (place : Ball×X↪Fin K) (u : Ball) (pr : R→Fin N) (ma : C→Fin k→Fin N) (tr : T→Fin N)
    (enum : Fin Rn≃U) (primary : R→Expr) (mate : C→Fin k→Expr) (tree : T→Expr) (qty : U→Expr) (b : ℕ)
    (mounted : ∀x,(site x).work≤b) (prFit : ∀r,(primary r).work≤b) (maFit : ∀c j,(mate c j).work≤b)
    (trFit : ∀t,(tree t).work≤b) (qtyFit : ∀r,(qty r).work≤b) :
    (packetInputs extra place u pr ma tr enum site primary mate tree qty).Bound (10*b+3) := by
  have faceCap : 4*b+1 ≤ 10*b+3 := by omega
  have qtyCap : b ≤ 10*b+3 := by omega
  have edgeCap : 2*b+2*b+1 ≤ 10*b+3 := by omega
  refine ⟨?_,?_,?_,?_⟩
  · intro i s
    exact (face_work site b mounted _ s).trans faceCap
  · intro i
    exact (qtyFit (enum i)).trans qtyCap
  · intro i j
    exact (routed_work extra site primary mate tree b b mounted prFit maFit trFit (enum i) j.val).trans edgeCap
  · intro i j s
    let ends := ColumnWires.ends (horizontal n) extra
    have cap : 2*b+2*(4*b+1)+1 ≤ 10*b+3 := by omega
    exact (routed_work extra site (fun r=>face site (ends (firstRole r)) s)
      (fun c a=>face site (ends (.radius c a true)) s)
      (fun t=>face site (treeEnds n k t) s) b (4*b+1) mounted
      (fun r=>face_work site b mounted (ends (firstRole r)) s)
      (fun c a=>face_work site b mounted (ends (.radius c a true)) s)
      (fun t=>face_work site b mounted (treeEnds n k t) s) (enum i) j.val).trans cap

end Hierarchy.WireTelescope.StripPaths

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope StripPaths PacketTurns
open LinearAlgebra.SpectralBooks ChordGraph
variable {h d k K n Rn : ℕ} {S : PurchaseSampler} {A B Ball : Type} [Fintype A] [Fintype B]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T

omit [Fintype A] [Fintype B] in
theorem StripPorts.packet_bound (p : StripPorts S h d k C (Fin n) B) (b : Board) (shift : ℕ)
    (extra : A⊕B→DistinctPair X) (place : Ball×X↪Fin K) (u : Ball)
    (pr : R→Fin (shift+b.rows)) (ma : C→Fin k→Fin (shift+b.rows)) (tr : T→Fin (shift+b.rows))
    (enum : Fin Rn≃U) (site : X→Expr) (stored : A→Expr) (qty : U→Expr) (maxWork : ℕ)
    (blocks : ∀c,(p.column c).work≤ maxWork) (horiz : ∀i l,(p.horizontal i l).work≤ maxWork)
    (birth : ∀i,(p.probe i).work≤ maxWork) (mounted : ∀x,(site x).work≤ maxWork)
    (stock : ∀a,(stored a).work≤ maxWork) (quantity : ∀i,(qty i).work≤ maxWork) :
    (packetInputs extra place u pr ma tr enum site (readPrimary stored shift (p.primary b))
      (emitterMate (A:=A) p b shift) (emitterTree (A:=A) p b shift) qty).Bound (10*(6*maxWork+17)+3) := by
  let cap:=6*maxWork+17
  have le : maxWork≤cap := by dsimp [cap];omega
  have paid (r : R) : (PacketScan.add (.lit shift) (p.primary b r)).work ≤ cap := by
    have budget:=p.primary_work b maxWork maxWork maxWork blocks horiz birth r
    simp only [PacketScan.add,Expr.work]
    dsimp [cap];omega
  apply inputs_bound extra site place u pr ma tr enum _ _ _ qty cap
  · exact fun x=>(mounted x).trans le
  · intro r
    cases r with
    | catalyst c a=>exact paid (.catalyst c a)
    | radius c j side=>exact paid (.radius c j side)
    | cross c a l r=>exact paid (.cross c a l r)
    | horizontal f l=>exact paid (.horizontal f l)
    | extra e=>cases e with
      | inl a=>exact (stock a).trans le
      | inr x=>exact paid (.extra (.inr x))
  · intro c j
    have budget:=p.mate_work b maxWork blocks (.catalyst c j : R)
    simp only [emitterMate,PacketScan.add,Expr.work,cap];omega
  · intro j
    exact paid (treeRole n k j)
  · exact fun x=>(quantity x).trans le

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI

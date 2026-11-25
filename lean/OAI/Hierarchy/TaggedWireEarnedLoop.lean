import OAI.Hierarchy.TaggedWireEarnedCoordinate

namespace OAI
/-! # An elected native packet installs zero width on every self-loop -/
noncomputable section
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
local notation "G" => Commodity (Fin (2^h)) (Stages h d) k
local notation "shift" => Fintype.card G
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K} {pad : Chord K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
local notation "roles" => ColumnWires.ends (horizontal n) extra

namespace EarnedInstall
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)

variable {F J : Type} [Field F] [Fintype J] (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (req : J → ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)
    (rt : Fin (Fintype.card (TreeSite n k))) (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (Strip.horizontal n) extra e)) req)
    (copies : ℕ)

variable (pad : Chord K)
local notation "chosen" => g.tender labels req rt P copies pad
open scoped BigOperators

variable (hist : Histogram (Fin P.terms) copies)
local notation "amt" => histWidth P.count hist

omit [Fintype A] [Fintype B] [Fintype Ball] in
private theorem distinct_sites (x : DistinctPair X) {ends : Site h d k × Site h d k}
    (faces : Faces (Prod.map g.col id) x ends) : ends.1≠ends.2 := by
  have apart : (Prod.map g.col id) x.left≠(Prod.map g.col id) x.right := by
    intro equal
    have same : place (u,x.left)=place (u,x.right) :=
      (g.mapped _).trans ((congrArg name equal).trans (g.mapped _).symm)
    exact x.apart (congrArg Prod.snd (place.injective same))
  rcases faces with left|right
  · simpa only [left] using apart
  · simpa only [right] using apart.symm

omit [Fintype Ball] [Fintype A] [Fintype B] in
theorem primary_endpoints_ne (r : R) (paid : paidRole r) :
    (endRow (g.index r)).1 ≠ (endRow (g.index r)).2 := by
  exact g.distinct_sites _ (p.primary_faces b m reg g.lookup g.loaded g.wide π
    (horizontal n) extra g.col g.placed.1 endRow g.core g.placed.2.choose_spec.choose_spec.2.2.1 g.placed.2.choose_spec.choose_spec.2.2.2 r (g.index r) (g.placed.2.choose_spec.choose_spec.1 r paid))

omit [Fintype Ball] [Fintype A] [Fintype B] in
theorem mate_endpoints_ne (c : C) (j : Fin k) :
    (endRow (g.mate c j)).1 ≠ (endRow (g.mate c j)).2 := by
  exact g.distinct_sites _ (p.mate_faces b m reg g.lookup g.loaded g.wide π
    (horizontal n) extra g.col g.placed.1 endRow g.core (.catalyst c j:R) (g.mate c j) (g.placed.2.choose_spec.choose_spec.2.1 c j))

/-- Even if a dormant public catalogue row is a self-loop, every part of a
successful installation misses it, including selector bits and the second
radial hop of a catalyst. -/
theorem tender_loop_zero (e : Fin b.rows) (loop : (endRow e).1=(endRow e).2) :
    (chosen).install.load ((chosen).bits hist) (paidRow (g:=shift) e)=0 := by
  classical
  have primary (r : R) : ¬(paidRole r ∧ g.index r=e) := by
    rintro ⟨on,same⟩
    exact g.primary_endpoints_ne r on (by rw [same]; exact loop)
  have opposite (c : C) (j : Fin k) : g.mate c j≠e := by
    intro same
    exact g.mate_endpoints_ne c j (by rw [same]; exact loop)
  have tree (t : T) : g.index (treeRole n k t)≠e := by
    have on : paidRole (treeRole n k t:R) := by rcases t with s|⟨c,j,side⟩ <;> trivial
    exact fun same=>primary _ ⟨on,same⟩
  rw [g.tender_paid labels req rt P copies pad hist e]
  simp only [primary,tree,ite_false,Finset.sum_const_zero,Nat.add_zero,Nat.zero_add]
  apply Finset.sum_eq_zero
  intro r _
  cases r <;> simp [opposite]

end EarnedInstall
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI

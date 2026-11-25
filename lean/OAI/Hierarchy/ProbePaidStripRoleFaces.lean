import OAI.Hierarchy.ProtocolRAMStripEdgeIDs
import OAI.Hierarchy.ProbeStripBroadcastTree

namespace OAI
/-! # Original reporter endpoints of each admitted native catalogue role -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.CoreBoard AdaptiveProbe Strip
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Fin.CommRing Classical

variable {h d k K w : ℕ} {S : PurchaseSampler} {C H A B Ball : Type}
variable [Fintype C] [Fintype H] [Fintype A] [Fintype B]
local notation "R" => ColumnWires.Role C H (A⊕B) k
local notation "Ports" => StripPorts S h d k C H B

def directRole : R → R
  | .catalyst c j => .radius c j false
  | p => p

def secondRole : R → R
  | .catalyst c j => .radius c j true
  | p => p

/-- The word on the actual row describes these two named sites, with
either orientation permitted in the immutable original edge directory. -/
def Faces {X V : Type*} (site : X→V) (p : DistinctPair X) (ends : V×V) :=
  ends=(site p.left,site p.right) ∨ ends=(site p.right,site p.left)

theorem Faces.sorted {X V : Type} (embed : V↪Fin K) (site : X→V) (p : DistinctPair X)
    (pair : V×V) (apart : pair.1≠pair.2) (diff : site p.left≠site p.right)
    (truePair : Faces site p pair) :
    Probe.orderedEnds (embed pair.1) (embed pair.2) (embed.injective.ne apart)=
      Probe.orderedEnds (embed (site p.left)) (embed (site p.right)) (embed.injective.ne diff) := by
  rcases truePair with rfl|rfl
  · rfl
  · exact Probe.orderedEnds_comm _ _ _

omit [Fintype C] [Fintype H] [Fintype A] [Fintype B] in
/-- Resolve a paid physical ID back to its genuine pair of sockets. The
geometry-specific data are the CT horizontal incidences and the retained
original probe. Radius, catalyst, diagonal and dummy cases are discharged by
the shared immutable core directory itself. -/
theorem StripPorts.primary_faces (p : Ports) (b : Board) (m : Memory w) (reg : Word w)
    (order : Fin b.coreRows≃Edges S h d k) (loaded : CoreLookup.Loaded p.directory order m)
    (wide : b.rows<2^w) (π : Equiv.Perm (Fin (2^h)))
    (horizontal : H→DistinctPair C) (extra : A⊕B→DistinctPair (ColumnSite C k))
    (col : C → Columns h d) (column : ∀c,((p.column c).eval m reg).val=((Fintype.equivFin _) (col c)).val)
    (endRow : Fin b.rows→Site h d k × Site h d k)
    (core : ∀f,endRow (b.coreIndex (order.symm f))=CoreBoard.ends π f)
    (hor : ∀f l (v : Fin b.rows),((b.coreOnly (p.horizontal f l)).eval m reg).val=v.val →
      Faces (Prod.map col id) (ColumnWires.ends horizontal extra (.horizontal f l)) (endRow v))
    (birth : ∀j (v : Fin b.rows),((p.probe j).eval m reg).val=v.val →
      Faces (Prod.map col id) (extra (.inr j)) (endRow v))
    (role : R) (v : Fin b.rows) (read : ((p.primary b role).eval m reg).val=v.val) :
    Faces (Prod.map col id) (ColumnWires.ends horizontal extra (directRole role)) (endRow v) := by
  have coreAt (f : Edges S h d k) (fetched : (p.primary b role).eval m reg=((order.symm f).val:Word w)) :
      endRow v=CoreBoard.ends π f := by
    have fits : (order.symm f).val<2^w := (b.coreIndex (order.symm f)).isLt.trans wide
    have idRow : v=b.coreIndex (order.symm f) :=
      Fin.ext (read.symm.trans ((congrArg Fin.val fetched).trans (Fin.val_cast_of_lt fits)))
    exact idRow ▸ core f
  cases role with
  | catalyst c j =>
    rw [coreAt _ (p.catalyst_hops (A:=A) b order m loaded wide c (col c) j reg (column c)).1]
    exact Or.inl rfl
  | radius c j side =>
    rw [coreAt _ (p.radius_read (A:=A) b order m loaded c (col c) j side reg wide (column c))]
    exact Or.inl rfl
  | cross c axes s t =>
    rw [coreAt _ (p.cross_read (A:=A) b order m loaded c (col c) axes s t reg wide (column c))]
    exact cross_edges (S:=S) (col c) axes s t
  | horizontal f l => exact hor f l v read
  | extra j =>
    cases j with
    | inl i =>
      have impossible : b.rows=v.val := by
        simpa [StripPorts.primary,Expr.eval,Fin.val_cast_of_lt wide] using read
      omega
    | inr j => exact birth j v read

omit [Fintype C] [Fintype H] [Fintype A] [Fintype B] in
/-- The second paid catalyst hop reaches the other original radius.
All other roles read the out-of-range sentinel. -/
theorem StripPorts.mate_faces (p : Ports) (b : Board) (m : Memory w) (reg : Word w)
    (order : Fin b.coreRows≃Edges S h d k) (loaded : CoreLookup.Loaded p.directory order m)
    (wide : b.rows<2^w) (π : Equiv.Perm (Fin (2^h)))
    (horizontal : H→DistinctPair C) (extra : A⊕B→DistinctPair (ColumnSite C k))
    (col : C → Columns h d) (column : ∀c,((p.column c).eval m reg).val=((Fintype.equivFin _) (col c)).val)
    (endRow : Fin b.rows→Site h d k × Site h d k)
    (core : ∀f,endRow (b.coreIndex (order.symm f))=CoreBoard.ends π f)
    (role : R) (v : Fin b.rows) (read : ((p.mate b role).eval m reg).val=v.val) :
    Faces (Prod.map col id) (ColumnWires.ends horizontal extra (secondRole role)) (endRow v) := by
  cases role with
  | catalyst c j =>
    let f : Edges S h d k := .inl (.inl (col c,j,true))
    have fetched : (p.mate b (.catalyst (E:=A⊕B) c j)).eval m reg=((order.symm f).val:Word w) :=
      (p.catalyst_hops (A:=A) b order m loaded wide c (col c) j reg (column c)).2
    have fits : (order.symm f).val<2^w := (b.coreIndex (order.symm f)).isLt.trans wide
    have idRow : v=b.coreIndex (order.symm f) :=
      Fin.ext (read.symm.trans ((congrArg Fin.val fetched).trans (Fin.val_cast_of_lt fits)))
    rw [idRow,core]
    exact Or.inl rfl
  | radius _ _ _ | cross _ _ _ _ | horizontal _ _ | extra _ =>
    have impossible : b.rows=v.val := by simpa [StripPorts.mate,Expr.eval,Fin.val_cast_of_lt wide] using read
    omega

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI

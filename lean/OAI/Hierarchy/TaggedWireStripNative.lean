import OAI.Hierarchy.TaggedWirePacketFaces
import OAI.Hierarchy.TaggedWireInstalls

namespace OAI
/-! # The signed strip installation on the original paid and virtual stock directories -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators
variable {h d k K n w N : ℕ} {S : PurchaseSampler} {A B Ball : Type}
    [Fintype A] [Fintype B]
local notation "C" => TreeColumn n
local notation "R" => ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k
local notation "PortSpec" => StripPorts S h d k (TreeColumn n) (Fin n) B
variable (extra : A⊕B→DistinctPair (TreeSite n k))
    (place : Ball×TreeSite n k↪Fin K) (u : Ball)
    (phys : Fin N→Chord K)

/-- The exact axis, horizontal and purchase incidences are read from the
same candidate row that supplies the native signed histogram. `lookup` is
the CT catalogue lookup, `hor` is a real payload/chain incidence, and
`birth` is the earlier acquired probe. `old` points to native held stock. -/
def StripPorts.install (p : PortSpec) (b : Board) (m : Memory w) (reg : Word w)
    (lookup : Fin b.coreRows≃Edges S h d k) (loaded : CoreLookup.Loaded p.directory lookup m)
    (wide : b.rows<2^w) (π : Equiv.Perm (Fin (2^h)))
    (col : C → Columns h d) (column : ∀c,((p.column c).eval m reg).val=((Fintype.equivFin _) (col c)).val)
    (row : Fin b.rows→Site h d k×Site h d k)
    (core : ∀f,row (b.coreIndex (lookup.symm f))=CoreBoard.ends π f)
    (hor : ∀f l (v : Fin b.rows),((b.coreOnly (p.horizontal f l)).eval m reg).val=v.val →
      Faces (Prod.map col id) (ColumnWires.ends (Strip.horizontal n) extra (.horizontal f l)) (row v))
    (birth : ∀j (v : Fin b.rows),((p.probe j).eval m reg).val=v.val →
      Faces (Prod.map col id) (extra (.inr j)) (row v))
    (name : Site h d k↪Fin K) (fits : ∀x,place (u,x)=name (Prod.map col id x))
    (old : A→Fin N) (new : Fin b.rows→Fin N) (idx : R→Fin b.rows) (mate : C→Fin k→Fin b.rows)
    (stock : ∀a,phys (old a)=reportedRole place (ColumnWires.ends (Strip.horizontal n) extra) u (.extra (.inl a)))
    (idxRead : ∀r,paidRole r→((p.primary b r).eval m reg).val=(idx r).val)
    (mateRead : ∀c j,((p.mate b (.catalyst c j : R)).eval m reg).val=(mate c j).val)
    (real : ∀v,∀ne:(row v).1≠(row v).2,phys (new v)=Probe.orderedEnds
      (name (row v).1) (name (row v).2) (name.injective.ne ne)) :
    ChosenPackets.Installs (Sum.elim (reportedRole place (ColumnWires.ends (Strip.horizontal n) extra) u)
      (reportedRole place (treeEnds n k) u)) phys := by
  let pr:=primaryRow (b:=b) old new idx
  let ma:=fun c j=>new (mate c j)
  let tr:=fun j:TreeLink n k=>new (idx (treeRole n k j))
  refine ⟨Sum.elim (StripPaths.links (Strip.horizontal n) extra place u pr ma) (fun j=>[tr j]),?_⟩
  obtain ⟨first,second,tree⟩:=p.install_faces extra place u phys b m reg lookup loaded wide π col column row
    core hor birth name fits old new idx mate stock idxRead mateRead real
  rintro (r|j)
  · exact StripPaths.path phys (Strip.horizontal n) extra place u pr ma first second r
  · exact StripPaths.tree_path phys u place tr tree j

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI

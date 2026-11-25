import OAI.Hierarchy.ProbePaidStripRoleFaces
import OAI.Hierarchy.TaggedWireStripPaths

namespace OAI
/-! # The actual geometric faces of every selected stock, paid, and selector row -/
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

/-- The role class excluded from the paid-edge array has a retained inventory
slot. All other primary occurrences are original native purchased/core IDs. -/
def paidRole : R→Prop
  | .extra (.inl _)=>False
  | _=>True

def primaryRow {b : Board} (old : A→Fin N) (new : Fin b.rows→Fin N) (idx : R→Fin b.rows) : R→Fin N
  | .extra (.inl a)=>old a
  | r=>new (idx r)

private theorem from_faces {V X : Type} {i : Fin N} (name : V↪Fin K) (site : X→V) (z : DistinctPair X)
    (ends : V×V) (inside : Faces site z ends)
    (actual : ∀neq:ends.1≠ends.2,phys i=Probe.orderedEnds (name ends.1) (name ends.2) (name.injective.ne neq))
    (f : X→Fin K) (fitted : ∀x,f x=name (site x)) (separate : f z.left≠f z.right) :
    phys i=Probe.orderedEnds (f z.left) (f z.right) separate := by
  have distinct : site z.left≠site z.right :=
    fun eq=>separate ((fitted _).trans ((congrArg name eq).trans (fitted _).symm))
  have apart : ends.1≠ends.2 := by rcases inside with eq|eq <;> rw [eq] <;> first | exact distinct | exact distinct.symm
  have same : f = fun x => name (site x) := funext fitted
  subst f
  exact (actual apart).trans (inside.sorted name site z ends apart distinct)

omit [Fintype A] [Fintype B] in
theorem StripPorts.install_faces (p : PortSpec) (b : Board) (m : Memory w) (reg : Word w)
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
    (∀r,phys (primaryRow (b:=b) old new idx r)=
      reportedRole place (ColumnWires.ends (Strip.horizontal n) extra) u (StripPaths.firstRole r)) ∧
    (∀c j,phys (new (mate c j))=reportedRole place (ColumnWires.ends (Strip.horizontal n) extra) u (.radius c j true)) ∧
    (∀j,phys (new (idx (treeRole n k j)))=reportedRole place (treeEnds n k) u j) := by
  let pr:=primaryRow (b:=b) old new idx
  let ma:=fun c j=>new (mate c j)
  have first (r : R) : phys (pr r)=reportedRole place (ColumnWires.ends (Strip.horizontal n) extra) u
      (StripPaths.firstRole r) := by
    have native (rr : R) (hr : paidRole rr) : phys (new (idx rr))=
        reportedRole place (ColumnWires.ends (Strip.horizontal n) extra) u (directRole rr) := by
      apply from_faces phys name (Prod.map col id) _ (row (idx rr))
        (p.primary_faces b m reg lookup loaded wide π (Strip.horizontal n) extra col column row core hor birth rr _ (idxRead rr hr))
        (real (idx rr)) (fun x=>place (u,x)) fits
    cases r with
    | catalyst c j=>exact native (.catalyst c j) trivial
    | radius c j side=>exact native (.radius c j side) trivial
    | cross c a l r=>exact native (.cross c a l r) trivial
    | horizontal f l=>exact native (.horizontal f l) trivial
    | extra ab=>cases ab with
      | inl a=>exact stock a
      | inr a=>exact native (.extra (.inr a)) trivial
  have second (c : C) (j : Fin k) : phys (ma c j)=
      reportedRole place (ColumnWires.ends (Strip.horizontal n) extra) u (.radius c j true) := by
    apply from_faces phys name (Prod.map col id) _ (row (mate c j))
      (p.mate_faces b m reg lookup loaded wide π (Strip.horizontal n) extra col column row core
        (.catalyst c j) _ (mateRead c j)) (real (mate c j)) (fun x=>place (u,x)) fits
  let tr:=fun j:TreeLink n k=>new (idx (treeRole n k j))
  have tree (j : TreeLink n k) : phys (tr j)=reportedRole place (treeEnds n k) u j := by
    rw [show reportedRole place (treeEnds n k) u j=
      reportedRole place (ColumnWires.ends (Strip.horizontal n) extra) u (treeRole n k j) by
        unfold reportedRole; simp only [tree_role_ends]]
    rcases j with i|⟨c,axis,side⟩
    · exact first (.horizontal i none)
    · exact first (.radius c axis side)
  exact ⟨first,second,tree⟩

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI

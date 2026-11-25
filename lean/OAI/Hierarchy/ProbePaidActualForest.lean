import OAI.Hierarchy.ProbePaidStripTree
import OAI.Hierarchy.ProbePaidPayloadHoriz
import OAI.Hierarchy.ProbePaidTreeArchive

namespace OAI
/-! # Checking tree congestion against original core-edge IDs at the permanent checkout -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip StockCommit Probe
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Fin.CommRing Classical

variable {h d k n w Srows : ℕ} {S : PurchaseSampler} {Extra Ball : Type}
local notation "Link" => TreeLink n k
local notation "Ports" => StripPorts S h d k (TreeColumn n) (Fin n) Extra

/-- Only live IDs are ever compared with this map. The assigned value
on the unused suffix and on loops is immaterial to the numeric row load. -/
private def coreWitness (b : Board) (π : Equiv.Perm (Fin (2^h)))
    (order : Fin b.coreRows≃Edges S h d k) (site : Site h d k ↪ Fin Srows)
    (fallback : Chord Srows) (row : Fin b.rows) : Chord Srows :=
  if low : row.val<b.coreRows then
    let pair:=CoreBoard.ends π (order ⟨row.val,low⟩)
    if ne : pair.1≠pair.2 then orderedEnds (site pair.1) (site pair.2) (site.injective.ne ne) else fallback
  else fallback

/-- Only two kinds of real lookup are used by the true tree header:
the original horizontal strip hop and the original center-to-sign radius. -/
theorem originalTree_faces (p : Ports) (b : Board) (π : Equiv.Perm (Fin (2^h)))
    (order : Fin b.coreRows≃Edges S h d k) (m : Memory w) (row : Word w)
    (loaded : CoreLookup.Loaded p.directory order m) (wide : b.rows<2^w)
    (col : TreeColumn n → Columns h d)
    (readCol : ∀c,((p.column c).eval m row).val=((Fintype.equivFin _) (col c)).val)
    (horizontal : ∀e,∃f : Edges S h d k,
      (p.horizontal e none).eval m row=((order.symm f).val:Word w) ∧
        HorizontalFaces col (Strip.horizontal n e) none (CoreBoard.ends π f)) (l : Link) :
    ∃f : Edges S h d k,(treeTerm p b l).eval m row=((order.symm f).val:Word w) ∧
      Faces (Prod.map col id) (treeEnds n k l) (CoreBoard.ends π f) := by
  rcases l with e|⟨c,j,side⟩
  · obtain ⟨f, hit, face⟩ := horizontal e
    exact ⟨f, b.coreOnly_read (p.horizontal e none) m row (order.symm f) wide hit, face⟩
  · let f : Edges S h d k:=.inl (.inl (col c,j,side))
    let key : Fin (CoreLookup.positions h d) :=
      ⟨_, ((Fintype.equivFin _) (col c)).isLt.trans_le (Nat.le_max_left _ _)⟩
    have hit := loaded.read (CoreLookup.radius j side) (p.column c) row key (readCol c) f
      (CoreLookup.resolve_radius (col c) j side)
    exact ⟨f, b.coreOnly_read (p.radiusAt c j side) m row (order.symm f) wide hit, Or.inl rfl⟩

/-- Original core numeric ID collisions imply the same sorted pair of
actual global vertices. Neither a new geometry oracle nor a table bounded
by the number of candidate rows is needed. -/
theorem actual_forest_from_reads (p : Ports) (b : Board) (a : Area) (m : Memory w) (pos : 0<b.coreRows)
    (order : Fin b.coreRows≃Edges S h d k) (π : Equiv.Perm (Fin (2^h)))
    (sites : Site h d k ↪ Fin Srows) (fallback : Chord Srows) (e : Fin b.rows)
    (atRow : Ball ↪ Fin a.rows) (place : Ball×TreeSite n k ↪ Fin Srows)
    (col : Ball→TreeColumn n → Columns h d) (party : ∀u x,place (u,x)=sites (Prod.map (col u) id x))
    (loaded : CoreLookup.Loaded p.directory order m)
    (readCol : ∀u c,((p.column c).eval m ((atRow u).val:Word w)).val=((Fintype.equivFin _) (col u c)).val)
    (horizontal : ∀u f,∃g : Edges S h d k,
      (p.horizontal f none).eval m ((atRow u).val:Word w)=((order.symm g).val:Word w) ∧
        HorizontalFaces (col u) (Strip.horizontal n f) none (CoreBoard.ends π g))
    (t : Traversals) (head : t.Reads m (fun j : Fin a.rows=>broadcastWalk p b m j.val pos)) (wide : b.rows<2^w)
    (copies maxBits : ℕ) (size : maxBits<2^w) (copySize : copies<2^w)
    (bounded : ∀j : Fin a.rows,(m (a.broadcast+j.val)).val≤ maxBits)
    (full : copies*maxBits<2^w)
    (live : ∀j : Fin a.rows,0<(m (a.broadcast+j.val)).val → ∃u,atRow u=j) :
    (PaidWidths.paidBroadcast a t.positions t.owner t.parity t.edge t.sourceRow copies maxBits).load m e ≤
      (n+(n+1)*(k*2))*(copies*maxBits) := by
  have active (u : Ball) (l : Link) := originalTree_faces p b π order m ((atRow u).val:Word w) loaded wide
    (col u) (readCol u) (horizontal u) l
  let f (u : Ball) (l : Link):Edges S h d k:=Classical.choose (active u l)
  have spec (u : Ball) (l : Link) := Classical.choose_spec (active u l)
  let target (u : Ball) (l : Link):Fin b.coreRows:=order.symm (f u l)
  apply stripTree_paid_bound p b a t m pos e head
    atRow place (coreWitness b π order sites fallback) target _ _ copies maxBits size copySize bounded full live
  · intro u l
    exact (congrArg Fin.val (spec u l).1).trans (Fin.val_cast_of_lt ((b.coreIndex (target u l)).isLt.trans wide))
  · intro u l
    have localNe : Prod.map (col u) id (treeEnds n k l).left ≠ Prod.map (col u) id (treeEnds n k l).right := by
      intro eqn
      have hh:place (u,(treeEnds n k l).left)=place (u,(treeEnds n k l).right):=
        (party u _).trans ((congrArg sites eqn).trans (party u _).symm)
      exact (treeEnds n k l).apart (congrArg Prod.snd (place.injective hh))
    have face : Faces (Prod.map (col u) id) (treeEnds n k l) (CoreBoard.ends π (f u l)):=(spec u l).2
    have nonloop : (CoreBoard.ends π (f u l)).1≠(CoreBoard.ends π (f u l)).2 := by
      rcases face with hit|hit
      · simpa only [hit] using localNe
      · simpa only [hit] using Ne.symm localNe
    have sort:=Faces.sorted sites (Prod.map (col u) id) (treeEnds n k l) _ nonloop localNe face
    have low : (b.coreIndex (target u l)).val < b.coreRows := (target u l).isLt
    have decoded (hrow : (b.coreIndex (target u l)).val < b.coreRows) :
        order ⟨(b.coreIndex (target u l)).val, hrow⟩ = f u l :=
      order.apply_symm_apply (f u l)
    unfold coreWitness
    rw [dite_eq_left low]
    dsimp only
    simp only [decoded, dite_eq_left nonloop, reportedRole, party]
    exact sort

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI

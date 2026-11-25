import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementPairRecovery

/-! # Transport of the canonical cut pairing to another map presentation -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.PatchRecord.Partition

variable {A V E W D J L : Type} {K : ℕ}
  [Fintype V] [Fintype E] [DecidableEq V] [Fintype W] [Fintype D] [DecidableEq W]
  (P : Partition V J K) (Q : Partition W L K) (M : RootedMap V E) (H : RootedMap W D)
  (f : M.Iso H) (occ : J ≃ L) (parts : ∀ v, Q.part (f.vertex v) = occ (P.part v))

/-- Changing presentation preserves cut wires, even if several cut wires
join the same two occurrences. -/
def cutEquiv : M.graph.CrossEdge P.part ≃ H.graph.CrossEdge Q.part :=
  f.edge.subtypeEquiv (by
    intro e
    change (P.part (M.graph.vertex e false) ≠ P.part (M.graph.vertex e true)) ↔
      Q.part (H.graph.vertex (f.edge e) false) ≠ Q.part (H.graph.vertex (f.edge e) true)
    rw [← f.incidence, ← f.incidence, parts, parts, occ.injective.ne_iff])

variable (z : V → A) (z' : W → A) (name : V ↪ ℕ) (name' : W ↪ ℕ)
  (readName : A → ℕ) (hn : ∀ w, readName (z' w) = name' w) (hl : ∀ v, z' (f.vertex v) = z v)
  (saved : ∀ j, P.record M z name j = Q.record H z' name' (occ j))

private theorem castStub_properties {R S : PatchRecord K A} (eq : R = S) (s : R.shape.Stub) :
    S.label (castStub eq s).val.1 = R.label s.val.1 ∧
      (castStub eq s).val.2.val = s.val.2.val := by subst S; exact ⟨rfl,rfl⟩

include saved hn hl in
theorem oldDart_iso (j : J) (s : (P.record M z name j).shape.Stub) :
    Q.oldDart H z' name' (occ j) (castStub (saved j) s).val =
      (f.edge.prodCongr (Equiv.refl Bool)) (P.oldDart M z name j s.val) := by
  let u := castStub (saved j) s
  let v := P.vertexAt name j s.val.1
  let w := Q.vertexAt name' (occ j) u.val.1
  have h := castStub_properties (saved j) s
  have hlabel : z' w = z v := h.1
  have hsite : w = f.vertex v := name'.injective (((hn w).symm.trans
    (congrArg readName (hlabel.trans (hl v).symm))).trans (hn _))
  let p := P.oldDart M z name j s.val
  apply dart_ext H
  · exact (actual_owner H _ u.val).trans (hsite.trans ((congrArg f.vertex
      (actual_owner M _ s.val).symm).trans (f.incidence p.1 p.2)))
  · exact (actual_slot H _ u.val).trans (h.2.trans ((actual_slot M _ s.val).symm.trans (f.number p.1 p.2)))

include saved hn hl in
/-- The extracted, directed pairing is natural for a change of numbered map
presentation, retaining the vertex-stub names determined by full labels. -/
theorem pairing_iso (e : (P.pairing M z name).Wire) (b : Bool) :
    Equiv.sigmaCongr occ (fun j => castStub (saved j)) ((P.pairing M z name).ends (e,b)) =
      (Q.pairing H z' name').ends (cutEquiv P Q M H f occ parts e,b) := by
  apply (Q.cutDarts H z' name').eq_symm_apply.mpr
  let a := (P.pairing M z name).ends (e,b)
  let u := castStub (saved a.1) a.2
  have hd := oldDart_iso P Q M H f occ z z' name name' readName hn hl saved a.1 a.2
  have he := P.stubDart M z name (e,b)
  have h := (Q.cutDarts_read H z' name' (occ a.1) u).trans (hd.trans
    (congrArg (f.edge.prodCongr (Equiv.refl Bool)) he))
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun q : D × Bool => q.2) h)

end PortGraph.PatchRecord.Partition

end

end SpectralBooks
end LinearAlgebra
end OAI

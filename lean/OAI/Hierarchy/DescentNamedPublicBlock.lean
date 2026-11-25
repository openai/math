import OAI.Hierarchy.DescentCableBlockNumber
import OAI.Hierarchy.DescentIssuedCommonChart
import OAI.Hierarchy.DescentOrdinaryNamedModel

namespace OAI
/-! A public block's edge and low ordinal through the native cable cut followed by
the actual tape permutation. Its location is observed directly on the WordBook used by the recipe. -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentKernelHistory
open scoped Classical
noncomputable section
open private pieceRef coarse from OAI.Hierarchy.DescentBundleSplit
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {B : BitDescription W}

/-- The public value of an occupied field of the final recipe is unique across
two presentations of its prior argument. This identifies the chosen issued book
with the canonical cut-and-renamed one at every genuine public read. -/
theorem WordBook.occupied_public_eq {Tag₁ Tag₂ Tag₃ X Y Z : Type}
    {r : Recipe Tag₁ X} {s : Recipe Tag₂ Y} {t : Recipe Tag₃ Z}
    (left : WordBook r s) (right : WordBook r t) (node : r.Node) (arg : Fin (r.arity node))
    (w₁ : Y) (w₂ : Z)
    (read₁ : s.operand (left.node node) (arg.cast (left.length node))=.inl w₁)
    (read₂ : t.operand (right.node node) (arg.cast (right.length node))=.inl w₂) :
    left.publicWord w₁=right.publicWord w₂ :=
  Sum.inl.inj ((left.publicHit node arg w₁ read₁).symm.trans (right.publicHit node arg w₂ read₂))

variable (hp : 0<p) (sh : WorldShape p R B) (count : W.graph.Edge→ℕ) (q : ℕ)
    (cut : ∀e∈W.core,W.graph.width e=count e*q) (pos : 0<q) (unit : p∣q)
variable (sites : Equiv.Perm W.graph.Site)
    (edges : Equiv.Perm (W.pieces q count cut).graph.Edge)

omit [Field F] in
theorem renamed_cable (v : (W.pieces q count cut).graph.Site) (b : BlockRef p (boundaryWidth (W.pieces q count cut).graph (sites.symm v))) :
    ((namedMap (W.pieces q count cut) sites edges v).map b).cableNumber (PhysicalRename.world (W.pieces q count cut) sites edges).graph v=
      (b.cableNumber (W.pieces q count cut).graph (sites.symm v)).map (fun x=>(edges x.1,x.2)) := by
  rcases b with ⟨e|a,j,fit⟩ <;> rfl

/-- The target is the globally renamed edge selected by the high part of the
block number and its low part remains the payload index in that edge. -/
theorem named_split_block (v : W.graph.Site) (edge : Incident W.graph (sites.symm v))
    (chunk : ℕ) (bounded : (chunk+1)*p≤W.graph.width edge.val) (mark : edge.val∈W.core) :
    let grain:=q/p
    let chosen:=((SiteBooks.trans hp (SiteBooks.rename hp (sh.pieces count q cut hp pos unit) sites edges) (SiteBooks.split hp sh count q cut pos unit)).atSite v).publicWord ⟨.inl edge,chunk,bounded⟩
    ∃j : Fin (count edge.val),j.val=chunk/grain ∧
      chosen.cableNumber (PhysicalRename.world (W.pieces q count cut) sites edges).graph v=some (edges (.inr ⟨⟨edge.val,mark⟩,j⟩),chunk%grain) := by
  intro grain chosen
  have scaled : q=grain*p := (Nat.div_mul_cancel unit).symm
  have gt : 0<grain := Nat.div_pos (Nat.le_of_dvd pos unit) hp
  let j:=coarse hp gt scaled (cut edge.val mark) chunk bounded
  refine ⟨j,rfl,?_⟩
  change ((namedMap (W.pieces q count cut) sites edges v).map
    ((pieceMap W.graph W.core count q cut hp gt scaled (sites.symm v)).map ⟨.inl edge,chunk,bounded⟩)).cableNumber _ _=_
  refine (renamed_cable (W:=W) count q cut sites edges v
    ((pieceMap W.graph W.core count q cut hp gt scaled (sites.symm v)).map ⟨.inl edge,chunk,bounded⟩)).trans ?_
  simp only [pieceMap,pieceRef,dite_eq_left mark,BlockRef.cableNumber,j]
  rfl

theorem named_unsplit_block (v : W.graph.Site) (edge : Incident W.graph (sites.symm v))
    (chunk : ℕ) (bounded : (chunk+1)*p≤W.graph.width edge.val) (outer : edge.val∉W.core) :
    let chosen:=((SiteBooks.trans hp (SiteBooks.rename hp (sh.pieces count q cut hp pos unit) sites edges) (SiteBooks.split hp sh count q cut pos unit)).atSite v).publicWord ⟨.inl edge,chunk,bounded⟩
    chosen.cableNumber (PhysicalRename.world (W.pieces q count cut) sites edges).graph v=some (edges (.inl ⟨edge.val,outer⟩),chunk) := by
  have scaled : q=(q/p)*p := (Nat.div_mul_cancel unit).symm
  have gt : 0<q/p := Nat.div_pos (Nat.le_of_dvd pos unit) hp
  change ((namedMap (W.pieces q count cut) sites edges v).map
    ((pieceMap W.graph W.core count q cut hp gt scaled (sites.symm v)).map ⟨.inl edge,chunk,bounded⟩)).cableNumber _ _=_
  refine (renamed_cable (W:=W) count q cut sites edges v
    ((pieceMap W.graph W.core count q cut hp gt scaled (sites.symm v)).map ⟨.inl edge,chunk,bounded⟩)).trans ?_
  simp only [pieceMap,pieceRef,dite_eq_right outer,BlockRef.cableNumber]
  rfl

end
end Hierarchy.DescentBundleHistory

end OAI

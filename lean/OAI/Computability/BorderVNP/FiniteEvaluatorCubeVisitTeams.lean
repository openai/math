import OAI.Computability.BorderVNP.FiniteEvaluatorCubeVisits
import OAI.Computability.BorderVNP.FiniteDiagonalCubeTerms
import OAI.Computability.BorderVNP.DiagonalTallyPacketRecipe

/-! # The full cube product from actual ordered team vertex lists -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeVisits

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.VertexIndex
open FiniteDiagonal
open scoped Classical BigOperators
open private ordered_nodup from OAI.Computability.BorderVNP.FiniteEvaluatorCubeVisits

variable {n d : ℕ} {Team : Type*} [DecidableEq Team]

/-- The row appended at a true square-table ordinal when the team owns the first symbol. -/
noncomputable def teamRow (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin d → Team) (t : Team) (q : Fin (d*d)) :
    List (Packet n d blocks × Vertex (n+1)) :=
  let v := TeamRows.pairAt d q
  if owner v.1=t then orderedRow axis blocks v.1 v.2 else []

/-- The exact list of vertices written by the team scan in successive directed row order. -/
noncomputable def teamList (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin d → Team) (t : Team) :
    List (Packet n d blocks × Vertex (n+1)) :=
  (List.finRange (d*d)).flatMap (teamRow axis blocks owner t)

theorem mem_teamRow (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin d → Team) (t : Team) (q : Fin (d*d))
    (pv : Packet n d blocks × Vertex (n+1)) :
    pv ∈ teamRow axis blocks owner t q ↔ key axis pv=TeamRows.pairAt d q ∧ owner (TeamRows.pairAt d q).1=t := by
  by_cases h : owner (TeamRows.pairAt d q).1=t <;> simp [teamRow,h,mem_orderedRow]

/-- The list is exhaustive on the true grouping-symbol ownership fiber. -/
theorem mem_teamList (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin d → Team) (t : Team)
    (pv : Packet n d blocks × Vertex (n+1)) :
    pv ∈ teamList axis blocks owner t ↔ owner (vertexLabel pv.1 pv.2 axis)=t := by
  simp only [teamList,List.mem_flatMap,List.mem_finRange,true_and,mem_teamRow]
  constructor
  · rintro ⟨q,keyEq,who⟩
    rwa [← keyEq,key_fst] at who
  · intro who
    let q := finProdFinEquiv (key axis pv)
    have keyEq : key axis pv=TeamRows.pairAt d q := (finProdFinEquiv.symm_apply_apply (key axis pv)).symm
    exact ⟨q,keyEq,by rwa [← keyEq,key_fst]⟩

/-- A packet vertex cannot reappear in a different directed row or at a different
dense rank in the same row. This includes the co-located case. -/
theorem teamList_nodup (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin d → Team) (t : Team) :
    (teamList axis blocks owner t).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun q _ => ?_,(List.nodup_finRange (d*d)).imp ?_⟩
  · by_cases h : owner (TeamRows.pairAt d q).1=t
    · simpa only [teamRow,h,ite_true] using ordered_nodup axis blocks (TeamRows.pairAt d q).1 (TeamRows.pairAt d q).2
    · simp [teamRow,h]
  · intro q r ne
    exact List.disjoint_left.mpr fun pv hq hr => ne (finProdFinEquiv.symm.injective
      (((mem_teamRow ..).mp hq).1.symm.trans ((mem_teamRow ..).mp hr).1))

/-- The emitted ordinal is a bijective numbering of the true owned vertex fiber. -/
noncomputable def teamEquiv (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin d → Team) (t : Team) :
    Fin (teamList axis blocks owner t).length ≃ {pv : Packet n d blocks × Vertex (n+1) // owner (vertexLabel pv.1 pv.2 axis)=t} := by
  let xs := teamList axis blocks owner t
  let f (j : Fin xs.length) : {pv : Packet n d blocks × Vertex (n+1) // owner (vertexLabel pv.1 pv.2 axis)=t} :=
    ⟨xs.get j,(mem_teamList ..).mp (List.get_mem xs j)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact (teamList_nodup axis blocks owner t).injective_get (congrArg Subtype.val h)
  · intro pv
    obtain ⟨j,hj⟩ := List.get_of_mem ((mem_teamList axis blocks owner t pv.val).mpr pv.property)
    exact ⟨j,Subtype.ext hj⟩

/-- Product over the genuine distributed directory, preserving every field entry
at the packet and vertex reached by its true native scan ordinal. -/
theorem team_product [Fintype Team] {R : Type*} [CommMonoid R]
    (axis : Fin (n+1)) (blocks : ℕ) (owner : Fin d → Team) (val : Packet n d blocks × Vertex (n+1) → R) :
    (∏ t : Team, ∏ j : Fin (teamList axis blocks owner t).length, val ((teamList axis blocks owner t).get j)) =
      ∏ pv : Packet n d blocks × Vertex (n+1), val pv := by
  refine Eq.trans (Finset.prod_congr rfl (fun t _ => (teamEquiv axis blocks owner t).prod_comp (fun pv => val pv.val))) ?_
  exact Fintype.prod_fiberwise (fun pv : Packet n d blocks × Vertex (n+1) => owner (vertexLabel pv.1 pv.2 axis)) val

variable {b h K s D blocks : ℕ} {F Sing : Type*} [CommRing F] [Fintype Team]

/-- The scalar actually stored for each owned visit at a fully assigned post-cube term. -/
def selected (entry : TableEntry n b h K s → F) (a : CubeTerm (Packet n d blocks) Sing n b h K s D)
    (pv : Packet n d blocks × Vertex (n+1)) : F :=
  entry (Tally.packetEntry D b s (a.2.2.1 pv.1) pv.2 (a.2.1 pv.1) (a.2.2.2 pv.1))

/-- On the actual selected cube term, the native team products are exactly all the
selected vertex-table factors. The axis and owner can be the public greedy allocation
computed from this term's selectors. -/
theorem cube_product (axis : Fin (n+1)) (owner : Fin d → Team) (entry : TableEntry n b h K s → F)
    (a : CubeTerm (Packet n d blocks) Sing n b h K s D) :
    (∏ t : Team, ∏ j : Fin (teamList axis blocks owner t).length, selected entry a ((teamList axis blocks owner t).get j)) =
      cubeTermWeight (fun _ => entry) (fun _ _ => 1) a := by
  rw [team_product,Fintype.prod_prod_type]
  simp only [cubeTermWeight,one_mul]
  rfl

end FiniteEvaluator.CubeVisits

end BorderVNP
end Computability
end OAI

import OAI.Hierarchy.DescentPackedSeedHeader
import OAI.Hierarchy.DescentBundleSeed

namespace OAI
/-! # Immutable operand names in the genuine seed bit-recipe -/
namespace Hierarchy.DescentPackedSeed
open DescentSeedRoot DescentInitialHost DescentKernelHistory DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty
open ThreeFlat Routing Catalyst Diagonal
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k n R s : ℕ} (X : Approximation F k n)
variable (c : (initialGroup X R s).Choice)
local notation "W" => (initialGroup X R s).state c

def liftLeg (j : Fin R) (v : Vertex X) : LocalBoundary X v→Boundary (W).graph ⟨j,v⟩
  | .inl e=>.inl ⟨⟨j,e.val⟩,e.property.imp (congrArg (Sigma.mk j)) (congrArg (Sigma.mk j))⟩
  | .inr p=>.inr ⟨⟨j,p.val⟩,congrArg (Sigma.mk j) p.property⟩

theorem recipe_arity (j : Fin R) (v : Vertex X) (u : (initialRecipe X R s c ⟨j,v⟩).Node) :
    (initialRecipe X R s c ⟨j,v⟩).arity u=legArity X v := by
  cases v with
  | inl site =>
    change seedArity (hubbed X.network.copyGraph) (.inl site) = legArity X (.inl site)
    exact @Fintype.card_congr _ _ _ _ (Equiv.refl (LocalBoundary X (.inl site)))
  | inr pin => rfl

theorem operand_leg (j : Fin R) (v : Vertex X) (u : (initialRecipe X R s c ⟨j,v⟩).Node)
    (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u)) :
    (initialRecipe X R s c ⟨j,v⟩).operand u i=
      .inl (liftLeg X c j v (leg X v (Fin.cast (recipe_arity X c j v u) i))) := by
  cases v with
  | inl site =>
    have transport {T : Type} (a b : Fintype T) (h : @Fintype.card T a = @Fintype.card T b)
        (k : Fin (@Fintype.card T a)) :
        (@Fintype.equivFin T a).symm k = (@Fintype.equivFin T b).symm (Fin.cast h k) := by
      cases Subsingleton.elim a b
      rfl
    let e := boundaryIndex (hubbed X.network.copyGraph) (.inl site)
    have same : e.symm i = leg X (.inl site) (Fin.cast (recipe_arity X c j (.inl site) u) i) :=
      transport _ _ _ i
    rw [← same]; first
    | rfl
    | let world := fun a : Fin R =>
        ((Histories.seedInternal (markedInput X) s
          (Sum.elim (fun _ : X.network.copyGraph.Site => true) (fun _ => false))).state (c a)).toWorld
      change Sum.inl (blockBoundary world j (Sum.inl site : Vertex X) (e.symm i)) =
        Sum.inl (liftLeg X c j (.inl site) (e.symm i))
      cases e.symm i <;> rfl
  | inr pin=>
    change Sum.inl _=Sum.inl _
    apply congrArg Sum.inl
    fin_cases i <;> rfl

/-- The immutable static row, shared by all copies, gives the code of the
very operand of this node. The short index selects one of its three saved
words. The hidden case cannot occur at any seed vertex. -/
theorem operand_read (w : ℕ) (sel : Select X R s→Bool) (j : Fin R) (v : Vertex X)
    (u : (initialRecipe X R s c ⟨j,v⟩).Node) (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u)) :
    let ar:=recipe_arity X c j v u
    let i3:=Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i
    let e:=leg X v (Fin.cast ar i)
    initialMemory (headerWords X R s w) (base X w sel) (shapeCell X (.inl v) (legColumn i3)).val=
      (legCode X v e:Computability.VPVNP.BurstRAM.Word w) ∧ (initialRecipe X R s c ⟨j,v⟩).operand u i=.inl (liftLeg X c j v e) := by
  dsimp only
  refine ⟨?_,operand_leg X c j v u i⟩
  rw [leg_at]
  have hi : i.val<legArity X v := (recipe_arity X c j v u) ▸ i.isLt
  have h3 : (Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i).val < legArity X v := hi
  simp only [legWord, dite_eq_left h3]
  have sameIndex :
      (⟨(Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i).val,h3⟩ : Fin (legArity X v)) =
        Fin.cast (recipe_arity X c j v u) i := Fin.ext rfl
  exact congrArg (fun a : Fin (legArity X v) => (legCode X v (leg X v a) : Computability.VPVNP.BurstRAM.Word w))
    sameIndex

variable {p : ℕ} (hp : 0<p) (multiple : p∣s)

theorem operand_window (j : Fin R) (v : Vertex X) (u i g) :
    let shape:=initialShape X R s c ⟨j,v⟩ hp multiple
    let part:=shape.chunk u i g
    part.start=0 ∧ part.stride=1 ∧ part.count=1 ∧
      ∀h : Fin part.count,∃b : BlockRef p (boundaryWidth (W).graph ⟨j,v⟩),
        part.get h=.inl b ∧ b.block=g.val ∧
        b.port=liftLeg X c j v (leg X v (Fin.cast (recipe_arity X c j v u) i)) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro h
  cases v with
  | inl v=>
    refine ⟨_,rfl,rfl,?_⟩
    exact Sum.inl.inj (operand_leg X c j (.inl v) u i)
  | inr pin=>fin_cases i <;> exact ⟨_,rfl,rfl,rfl⟩

omit [Field F] in
theorem decode_leg (v : Vertex X) (a : LocalBoundary X v) :
    (legCode X v a-1)/3=Sum.elim (fun e=>index e.val) (fun p=>p.val.val) a ∧
    (legCode X v a-1)%3=Sum.elim (fun e=>if source X.network.copyGraph e.val=v then 0 else 1) (fun _=>2) a := by
  cases a with
  | inl e=>by_cases he : source X.network.copyGraph e.val=v <;> simp [legCode,he]; omega
  | inr p=>simp [legCode]; omega

omit [Field F] in
theorem code_room (v : Vertex X) (a : LocalBoundary X v) :
    legCode X v a<3*(Fintype.card (Cable X)+Fintype.card (Port n X.width))+3 := by
  cases a with
  | inl e=>
    have h : index e.val<Fintype.card (Cable X):=((Fintype.equivFin _) e.val).isLt
    simp only [legCode]
    split <;> omega
  | inr pin=>
    have h:=pin.val.isLt
    simp only [legCode]
    omega

theorem operand_digits (w : ℕ) (sel : Select X R s→Bool)
    (room : 3*(Fintype.card (Cable X)+Fintype.card (Port n X.width))+3≤2^w)
    (j : Fin R) (v : Vertex X) (u : (initialRecipe X R s c ⟨j,v⟩).Node)
    (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u)) :
    let name:=leg X v (Fin.cast (recipe_arity X c j v u) i)
    let stored:=initialMemory (headerWords X R s w) (base X w sel)
      (shapeCell X (.inl v) (legColumn (Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i))).val
    0<stored.val ∧ (stored.val-1)/3=Sum.elim (fun e=>index e.val) (fun pin=>pin.val.val) name ∧
      (stored.val-1)%3=Sum.elim (fun e=>if source X.network.copyGraph e.val=v then 0 else 1) (fun _=>2) name := by
  dsimp only
  rw [(operand_read X c w sel j v u i).1,Fin.val_cast_of_lt ((code_room X v _).trans_le room)]
  refine ⟨?_,decode_leg X v _⟩
  cases leg X v (Fin.cast (recipe_arity X c j v u) i) <;> simp [legCode]

end
end Hierarchy.DescentPackedSeed

end OAI

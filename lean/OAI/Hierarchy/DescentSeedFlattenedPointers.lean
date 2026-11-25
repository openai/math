import OAI.Hierarchy.DescentPackedSeedLegs
import OAI.Hierarchy.DescentBundleTerminal
import OAI.Hierarchy.DescentLivePrivateWords
import OAI.Hierarchy.DescentSeedRectangleOrder

namespace OAI
/-! # Physical order of all aligned seed chunks in the flattened initial recipe -/
namespace Hierarchy.DescentPackedSeed
open DescentKernelHistory DescentInitialHost DescentBundleHistory DescentSeedRoot DescentSixParty
open Computability.BorderVNP.Crossing Catalyst
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k n R s p : ℕ} (X : Approximation F k n)
    (c : (initialGroup X R s).Choice) (hp : 0<p) (multiple : p∣s)
    (j : Fin R) (v : Vertex X)
local notation "r" => initialRecipe X R s c ⟨j,v⟩
local notation "sh" => initialShape X R s c ⟨j,v⟩ hp multiple

variable (u : (initialRecipe X R s c ⟨j,v⟩).Node)
include hp in
def flatSeedRef (i : Fin ((r).arity u)) (t : Fin (s/p)) :
    BlockRef p (boundaryWidth ((initialGroup X R s).state c).graph ⟨j,v⟩) where
  port:=liftLeg X c j v (leg X v (Fin.cast (recipe_arity X c j v u) i))
  block:=t.val
  fits:=by
    rw [initial_width X R s c ⟨j,v⟩]
    exact (Nat.le_div_iff_mul_le hp).mp (Nat.succ_le_of_lt t.isLt)

private theorem singleton_names {α : Type} (b : Slice p α) (one : b.count=1) (z : α)
    (read : ∀h,b.get h=z) : b.names=[z] :=by
  calc
    b.names = List.ofFn (fun _ : Fin b.count => z) := congrArg List.ofFn (funext read)
    _ = [z] := by simp [one]

theorem seed_keys :
    (sh).keys u=List.ofFn (fun z : Fin ((r).arity u*(s/p))=>
      let ij : Fin ((r).arity u)×Fin (s/p):=finProdFinEquiv.symm z
      Sum.inl (flatSeedRef X c hp j v u ij.1 ij.2)) :=by
  let key (i : Fin ((r).arity u)) (t : Fin (s/p)) :=
    Sum.inl (β := BlockRef p ((BitDescription.initial X R s c).recipe ⟨j,v⟩).hiddenWidth)
      (flatSeedRef X c hp j v u i t)
  change (sh).keys u = List.ofFn (fun z : Fin ((r).arity u*(s/p)) =>
    let ij : Fin ((r).arity u) × Fin (s/p) := finProdFinEquiv.symm z
    key ij.1 ij.2)
  rw [← Rectangle.flattened key]
  unfold Shape.keys Shape.rows
  rw [List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  change (List.ofFn ((sh).chunk u i)).flatMap Slice.names = List.ofFn (key i)
  have groups := initial_groups X R s c ⟨j,v⟩ hp multiple u i
  rw [List.flatMap_def,List.map_ofFn]
  change (List.ofFn (fun a => ((sh).chunk u i a).names)).flatten = List.ofFn (key i)
  rw [List.ofFn_congr groups (fun a => ((sh).chunk u i a).names)]
  have set : ∀t : Fin (s/p),
      (((sh).chunk u i (Fin.cast groups.symm t)).names)=
        [key i t] :=by
    intro t
    let a:=Fin.cast groups.symm t
    obtain ⟨_,_,one,read⟩:=operand_window X c hp multiple j v u i a
    apply singleton_names _ one
    intro z
    obtain ⟨e,found,block,face⟩:=read z
    rw [found]
    change Sum.inl e = Sum.inl (flatSeedRef X c hp j v u i t)
    apply congrArg Sum.inl
    rcases e with ⟨port,offset,fit⟩
    dsimp only at block face
    subst port
    subst offset
    rfl
  simp only [set]
  simpa only [List.map_ofFn,Function.comp_def] using Rectangle.singleton_flat (List.ofFn (key i))

theorem seed_key_at (i : Fin ((r).arity u)) (t : Fin (s/p)) :
    ((sh).keys u)[(finProdFinEquiv (i,t)).val]?=some (Sum.inl (flatSeedRef X c hp j v u i t)) :=by
  rw [seed_keys X c hp multiple j v u]
  have atIndex {α : Type} {m : ℕ} (f : Fin m → α) (z : Fin m) :
      (List.ofFn f)[z.val]? = some (f z) := by
    rw [List.getElem?_ofFn, dite_eq_left z.isLt]
  rw [atIndex _ (finProdFinEquiv (i,t))]
  simp only [Equiv.symm_apply_apply]

theorem seed_active_at (i : Fin ((r).arity u)) (t : Fin (s/p))
    (idx : Fin (((sh).recipe hp).arity u)) (eqn : idx.val=(finProdFinEquiv (i,t)).val) :
    ((sh).recipe hp).activePort u idx=.inl (flatSeedRef X c hp j v u i t) :=by
  have hit : idx.val < ((sh).keys u).length := idx.isLt
  have key : ((sh).keys u)[idx.val]? = some (.inl (flatSeedRef X c hp j v u i t)) := by
    simpa only [eqn] using seed_key_at X c hp multiple j v u i t
  have atKey := Option.some.inj ((List.getElem?_eq_getElem hit).symm.trans key)
  have physical : ((sh).recipe hp).operand u idx=.inl (flatSeedRef X c hp j v u i t):=by
    change (((sh).keys u)[idx.val]).map id _=_
    rw [atKey]; rfl
  have readback := (((sh).recipe hp).activePort_read u idx).trans physical
  cases h : ((sh).recipe hp).activePort u idx with
  | inl b =>
    rw [h] at readback
    exact congrArg Sum.inl (Sum.inl.inj readback)
  | inr a =>
    rw [h] at readback
    cases readback

end
end Hierarchy.DescentPackedSeed

end OAI

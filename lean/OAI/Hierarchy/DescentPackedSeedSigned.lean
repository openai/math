import OAI.Hierarchy.DescentSeedOperandStamp
import OAI.Hierarchy.DescentSeedSiteOrdinals
import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentPackedSeedLegs
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! Read-only local names for the three original operand sockets at each seed vertex. -/
namespace Hierarchy.DescentPackedSeed.Signed
open DescentSeedRoot DescentInitialHost DescentKernelHistory DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty
open ThreeFlat Routing Catalyst Diagonal
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k n R s : ℕ} (X : Approximation F k n)
local notation "N" => X.network.copyGraph

variable (c : (initialGroup X R s).Choice)
local notation "W" => (initialGroup X R s).state c

theorem physical {w : ℕ} (at₀ : ℕ) (m : Memory w)
    (j : Fin R) (v : Vertex X) (u : (initialRecipe X R s c ⟨j,v⟩).Node)
    (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u)) (f : Fin 2) :
    let a:=Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i
    let p:=leg X v (Fin.cast (recipe_arity X c j v u) i)
    image X at₀ m (at₀+(address X (v,a,f)).val)=
      ((p.elim (fun e=>if f=0 then seedPeer X v e.val else seedParallel X v e.val) (fun _=>0)):Computability.VPVNP.BurstRAM.Word w) := by
  dsimp only
  rw [read_leg]
  have used : i.val<legArity X v := (recipe_arity X c j v u) ▸ i.isLt
  have live : (Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i).val < legArity X v := used
  simp only [fields, dite_eq_left live]
  have sameIndex :
      (⟨(Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i).val, live⟩ : Fin (legArity X v)) =
        Fin.cast (recipe_arity X c j v u) i := Fin.ext rfl
  rw [sameIndex]
  cases leg X v (Fin.cast (recipe_arity X c j v u) i) with
  | inl e =>
    by_cases first : f = 0 <;> simp [first]
  | inr pin => rfl

/-- Both the original orientation/global ID and the two new local fields are in the same real memory. -/
theorem read_original {w : ℕ} (sel : Select X R s → Bool) (at₀ : ℕ)
    (separate : publicWords X≤at₀)
    (room : 3*(Fintype.card (Cable X)+Fintype.card (Port n X.width))+3≤2^w)
    (j : Fin R) (v : Vertex X) (u : (initialRecipe X R s c ⟨j,v⟩).Node)
    (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u)) :
    let a:=Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i
    let p:=leg X v (Fin.cast (recipe_arity X c j v u) i)
    let m:=Computability.VPVNP.RAMMemory.initialMemory (headerWords X R s w) (base X w sel)
    let stored:=image X at₀ m (shapeCell X (.inl v) (legColumn a)).val
    0<stored.val ∧ (stored.val-1)/3=p.elim (fun e=>index e.val) (seedPort X) ∧
      (stored.val-1)%3=p.elim (fun e=>if source N e.val=v then 0 else 1) (fun _=>2) ∧
      ∀f,image X at₀ m (at₀+(address X (v,a,f)).val)=
        ((p.elim (fun e=>if f=0 then seedPeer X v e.val else seedParallel X v e.val) (fun _=>0)):Computability.VPVNP.BurstRAM.Word w) := by
  dsimp only
  rw [frame X _ _ _ (Or.inl ((shapeCell X (.inl v) _).isLt.trans_le separate))]
  have first:=operand_digits X c w sel room j v u i
  exact ⟨first.1,first.2.1,first.2.2,physical X c at₀ _ j v u i⟩

theorem seed_pin {w : ℕ} (at₀ : ℕ) (m : Memory w)
    (j : Fin R) (v : Vertex X) (u : (initialRecipe X R s c ⟨j,v⟩).Node)
    (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u))
    (pin : {t : Fin (Fintype.card (Port n X.width)) // Sum.inr t=v})
    (atPin : leg X v (Fin.cast (recipe_arity X c j v u) i)=.inr pin) :
    let a:=Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i
    (initialRecipe X R s c ⟨j,v⟩).operand u i=.inl (liftLeg X c j v (.inr pin)) ∧
    ∀f,image X at₀ m (at₀+(address X (v,a,f)).val)=(localPort X pin).val := by
  refine ⟨(operand_leg X c j v u i).trans (by rw [atPin]),?_⟩
  intro f
  simpa only [atPin, Sum.elim_inr, localPort, Fin.val_zero, Nat.cast_zero] using
    physical X c at₀ m j v u i f

end
end Hierarchy.DescentPackedSeed.Signed

end OAI

import OAI.ThreeFlat.Routing.TypedWiring
import Mathlib.Data.Fin.VecNotation
import Init.Data.BitVec.Bitblast

namespace OAI
/-! # Checking addition in the block routing planner -/

namespace ThreeFlat.Routing.AddWords

open scoped BigOperators Classical
noncomputable section

abbrev Pin (w : ℕ) := Fin 3 × Fin w

private def valid {w : ℕ} (g : Option (Fin w)) (v : Fin 5 → Bool) : Prop :=
  match g with
  | none => v 0 = false
  | some _ => v 3 = Bool.atLeastTwo (v 0) (v 1) (v 2) ∧ v 4 = (v 0 ^^ (v 1 ^^ v 2))

private def wire {w : ℕ} : Option (Fin w) → Fin 5 → Pin w ⊕ Fin (w+1)
  | none => fun _ => .inr 0
  | some i => ![.inl (0,i),.inl (1,i),.inr i.castSucc,.inr i.succ,.inl (2,i)]

def network (K : Type*) [Zero K] [One K] (w : ℕ) : BitNetwork K (Fintype.card (Pin w)) :=
  TypedWiring.glue (fun g : Option (Fin w) =>
    TypedWiring.localTable (fun v => if valid g v then (1 : K) else 0)) wire

def pins {w : ℕ} (x y z : BitVec w) (p : Pin w) : Bool :=
  (![x,y,z] p.1).getLsbD p.2.val

private theorem valid_iff {w : ℕ} (x y z : BitVec w) (h : Fin (w+1) → Bool) :
    (∀ g : Option (Fin w), valid g (fun i => Sum.elim (pins x y z) h (wire g i))) ↔
      h = (fun i => BitVec.carry i.val x y false) ∧ z = x+y := by
  have step (i : Fin w) :
      valid (some i) (fun j => Sum.elim (pins x y z) h (wire (some i) j)) ↔
        h i.succ = Bool.atLeastTwo (x.getLsbD i.val) (y.getLsbD i.val) (h i.castSucc) ∧
        z.getLsbD i.val = (x.getLsbD i.val ^^ (y.getLsbD i.val ^^ h i.castSucc)) := by rfl
  constructor
  · intro hv
    have hcarry : h = (fun i => BitVec.carry i.val x y false) := by
      funext i
      induction i using Fin.induction with
      | zero => simpa only [Fin.val_zero,BitVec.carry_zero,valid,wire,Sum.elim_inr] using hv none
      | succ i ih => rw [(step i).mp (hv (some i)) |>.1, ih, Fin.val_succ, BitVec.carry_succ]; rfl
    refine ⟨hcarry,BitVec.eq_of_getLsbD_eq_iff.mpr ?_⟩
    intro i hi
    rw [BitVec.getLsbD_add hi]
    simpa only [hcarry,Fin.val_castSucc] using ((step ⟨i,hi⟩).mp (hv _)).2
  · rintro ⟨rfl,rfl⟩ (_ | i)
    · exact BitVec.carry_zero
    · exact (step i).mpr ⟨BitVec.carry_succ _ _ _ _,BitVec.getLsbD_add i.isLt _ _⟩

/-- Only the true carry sequence survives summation. -/
theorem network_eval (K : Type*) [CommSemiring K] {w : ℕ} (x y z : BitVec w) :
    TypedWiring.value (network K w) (pins x y z) = if z = x+y then 1 else 0 := by
  simp only [network,TypedWiring.glue_value,TypedWiring.localTable_value,Fintype.prod_boole,valid_iff]
  by_cases good : z=x+y
  · simp [good]
  · simp [good]

/-- The local five-bit full-adder truth tables have fixed size. -/
theorem network_size (K : Type*) [Zero K] [One K] (w : ℕ) :
    (network K w).cells + (network K w).internal ≤ 500*(w+1) := by
  simp [network,TypedWiring.localTable,TableCompiler.localTableNetwork_cells,
    TableCompiler.localTableNetwork_internal]
  omega

end
end ThreeFlat.Routing.AddWords

end OAI

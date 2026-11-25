import OAI.Hierarchy.DescentSeedOperandStamp
import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentPackedSeedSigned

namespace OAI
/-! # The previous pointer shelf for the original copied seed graph -/
namespace Hierarchy.DescentOperandStateBanks.Seed
open DescentPackedSeed DescentPackedSeed.Signed DescentSeedRoot DescentInitialHost DescentKernelHistory DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty ThreeFlat Routing Catalyst Diagonal
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [_root_.Field F] {k n R s w : ℕ} (X : Approximation F k n)
omit [_root_.Field F] in
theorem port_injective {v : Vertex X} :
    Function.Injective (fun _ : {j : Fin (Fintype.card (Port n X.width)) // Sum.inr j=v} => (0:ℕ)) := by
  intro a b _
  apply Subtype.ext
  exact Sum.inr.inj (a.property.trans b.property.symm)

/-- Every live copy reads its public kind and both local cable names from this
one original-vertex chart. The literal immutable selector tape supplies the
absolute exterior pin. The operand shelf stores the unique exterior slot at
its current site and the aligned p-word digit. -/
def field (base : ℕ) (v : Vertex X) (i : Fin 3) (g : ℕ) (mem : Memory w) : Field → Computability.VPVNP.BurstRAM.Word w :=
  ![mem (base+Signed.size X+(order X (v,i)).val),mem (base+(Signed.address X (v,i,0)).val),
    mem (base+(Signed.address X (v,i,1)).val),(g:Computability.VPVNP.BurstRAM.Word w),0,1,1]

variable (c : (initialGroup X R s).Choice)
local notation "W" => (initialGroup X R s).state c

theorem retained (base : ℕ) (m : Memory w) (j : Fin R) (v : Vertex X)
    (u : (initialRecipe X R s c ⟨j,v⟩).Node) (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u))
    (g : ℕ) (f : Field) :
    let ordinal:=Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i
    let leg₀:=leg X v (Fin.cast (recipe_arity X c j v u) i)
    field X base v ordinal g (image X base m) f =
      ((original X v leg₀ g).fields ⟨0,1,1⟩ f : Computability.VPVNP.BurstRAM.Word w) := by
  intro ordinal leg₀
  have ok : ordinal.val<legArity X v := (recipe_arity X c j v u) ▸ i.isLt
  have tag : image X base m (base+Signed.size X+(order X (v,ordinal)).val) =
      (leg₀.elim (fun _=>(1:ℕ)) (fun _=>2) : Computability.VPVNP.BurstRAM.Word w) := by
    unfold image
    rw [DescentStaticWordColumn.read _ _ _ _ (order X (v,ordinal)).isLt]
    have slot : data X (order X (v,ordinal)).val = kind X v ordinal := by
      rw [data, dite_eq_left (order X (v,ordinal)).isLt]
      exact congrArg (fun t : Vertex X × Fin 3 => kind X t.1 t.2)
        ((order X).symm_apply_apply (v,ordinal))
    rw [slot, kind, dite_eq_left ok]
    have indexed : leg X v ⟨ordinal.val,ok⟩ = leg₀ := rfl
    rw [indexed]
    cases leg₀ <;> simp
  have pairRead (q : Fin 2) : image X base m (base+(Signed.address X (v,ordinal,q)).val)=
      ((leg₀.elim (fun e=>if q=0 then Signed.seedPeer X v e.val else Signed.seedParallel X v e.val) (fun _=>0)):Computability.VPVNP.BurstRAM.Word w) := by
    have early: (Signed.address X (v,ordinal,q)).val<Signed.size X:=(Signed.address X _).isLt
    exact (DescentStaticWordColumn.frame (base+Signed.size X) (count X) (data X)
      (Signed.image X base m) (base+(Signed.address X (v,ordinal,q)).val) (.inl (by omega))).trans
        (Signed.physical X c base m j v u i q)
  have first:=pairRead 0
  have last:=pairRead 1
  cases e : leg₀ <;> fin_cases f <;> simp [field,original,Pointer.fields,Pointer.header,e] at tag first last ⊢ <;>
    first | assumption

/-- The copy number distinguishes exterior operands when the next host
receives several earlier copies of the same slab. The signed cable serial
occupies this field on interior operands. -/
def withStamp (raw : Field → Computability.VPVNP.BurstRAM.Word w) (copy : Computability.VPVNP.BurstRAM.Word w) (f : Field) : Computability.VPVNP.BurstRAM.Word w :=
  if f=2 ∧ raw 0=2 then copy else raw f

theorem stamped (wide : 2<2^w) (base : ℕ) (m : Memory w) (j : Fin R) (v : Vertex X)
    (u : (initialRecipe X R s c ⟨j,v⟩).Node) (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u))
    (g : ℕ) (f : Field) :
    let ordinal:=Fin.castLE (initial_arity X R s c ⟨j,v⟩ u) i
    let leg₀:=leg X v (Fin.cast (recipe_arity X c j v u) i)
    withStamp (field X base v ordinal g (image X base m)) (j.val:Computability.VPVNP.BurstRAM.Word w) f =
      ((originalAt X v leg₀ j.val g).fields ⟨0,1,1⟩ f : Computability.VPVNP.BurstRAM.Word w) := by
  intro ordinal leg₀
  have decoded (t : Field) : field X base v ordinal g (image X base m) t =
      ((original X v leg₀ g).fields ⟨0,1,1⟩ t : Computability.VPVNP.BurstRAM.Word w) :=
    retained X c base m j v u i g t
  have tags : (1:Computability.VPVNP.BurstRAM.Word w) ≠ 2 := by
    intro h
    have eqn:=congrArg Fin.val h
    change 1%2^w=2%2^w at eqn
    rw [Nat.mod_eq_of_lt (by omega : 1<2^w),Nat.mod_eq_of_lt wide] at eqn
    omega
  unfold withStamp
  rw [decoded 0,decoded f]
  cases e : leg₀ <;> fin_cases f <;>
    simp [originalAt,original,Pointer.fields,Pointer.header,tags]

theorem aligned {p : ℕ} (hp : 0< p) (multiple : p∣s) (j : Fin R) (v : Vertex X) (u i g) :
    let sh:=initialShape X R s c ⟨j,v⟩ hp multiple
    let interval:=sh.chunk u i g
    interval.start=0 ∧ interval.stride=1 ∧ interval.count=1 ∧
      ∀h : Fin interval.count,∃b : BlockRef p (boundaryWidth (W).graph ⟨j,v⟩),
        interval.get h=.inl b ∧ b.block=g.val ∧
        b.port=liftLeg X c j v (leg X v (Fin.cast (recipe_arity X c j v u) i)) :=
  operand_window X c hp multiple j v u i g

end
end Hierarchy.DescentOperandStateBanks.Seed

end OAI

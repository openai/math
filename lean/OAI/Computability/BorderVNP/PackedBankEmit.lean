import OAI.Computability.BorderVNP.PackedBankJoint

/-! # Joint word output of the complete fixed seed-bank packet collection

One frame prepares the shared arithmetic, then emits each site's tagged record
sequence. The gate budget is linear in the seed count, quadratic in word width,
and independent of the matched multiplicity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open CellSparse Word Crossing Shortening.StaticRows ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)

/-- One actual packet word of one fixed seed site. -/
noncomputable abbrev Output := Σ v : TemplateSite e, Fin (BankPacket.tape (rows e first v)).length

/-- Arithmetic expression for an emitted packet word. -/
noncomputable def expr (z : Output e first) : WidthExpr (Operands e z.1) :=
  (BankPacket.tape (rows e first z.1))[z.2]

/-- Number of arithmetic expression nodes of the final serialization phase. -/
noncomputable def nodes := ∑ z : Output e first, (expr e first z).nodes

/-- The actual merged-ID, relocated records of a single seed site at these public fields. -/
noncomputable def emitted (raw : Raw e → ℕ) (v : TemplateSite e) : List Record :=
  (rows e first v).map (BankPacket.RecordCode.read (fun i => word e raw (pin e v i)))

/-- The tagged numerical word is exactly its word in the serialized sparse record list. -/
theorem expr_packet (raw : Raw e → ℕ) (z : Output e first) :
    (expr e first z).eval (fun i => word e raw (pin e z.1 i)) =
      (Packet.fieldList Packet.record (emitted e first raw z.1))[z.2.val]?.getD 0 := by
  unfold emitted
  rw [← BankPacket.tape_eval]
  simp [expr]

/-- One shared Boolean circuit produces every flat tagged packet word at every
paid seed site. The input consists of the matched size and guessed histogram
together with the earlier pass's concrete address columns. -/
theorem exists_packetFrame {S σ : Type*} [Fintype S] [Fintype σ] (w : ℕ)
    (source : Frame σ (S × Raw e × Fin w)) :
    ∃ f : Frame σ (S × Output e first × Fin w),
      f.size ≤ source.size + 3 + Fintype.card S *
        ((BankCircuit.headerNodes D e.count m + PaidBox.nodeBound e + nodes e first) * (100*(w+1)^2)) ∧
      ∀ x s, let raw := fun i => value (fun j => source.eval x (s,i,j))
        Fits e w raw → ∀ z : Output e first,
          (expr e first z).Fits w (fun i => word e raw (pin e z.1 i)) →
          value (fun j => f.eval x (s,z,j)) =
            (Packet.fieldList Packet.record (emitted e first raw z.1))[z.2.val]?.getD 0 := by
  classical
  obtain ⟨pre,hpre,pe⟩ := exists_prepare e w source
  let leaf (t : S × Output e first) := ((expr e first t.2).frame w).subst
    (Frame.initial (fun i : Operands e t.2.1 × Fin w => (t.1,pin e t.2.1 i.1,i.2)))
  obtain ⟨joint,hj,he⟩ := Crossing.exists_parallelFrames leaf
  let select (i : S × Output e first × Fin w) : Σ _ : S × Output e first, Fin w := ⟨(i.1,i.2.1),i.2.2⟩
  refine ⟨(joint.select select).subst pre, ?_, ?_⟩
  · have hl (t : S × Output e first) : (leaf t).size ≤ (expr e first t.2).nodes * (100*(w+1)^2) := by
      simp only [leaf,Frame.subst_size,Frame.initial_size,zero_add]
      exact (expr e first t.2).frame_size w
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
    have htotal : (∑ i : S × Output e first, (expr e first i.2).nodes * (100*(w+1)^2)) =
        Fintype.card S * (nodes e first * (100*(w+1)^2)) := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,
        nodes,← Finset.sum_mul,Nat.mul_assoc]
    rw [htotal] at hsum
    simp only [Frame.subst_size,Frame.select_size,Nat.add_mul,Nat.mul_add] at hpre ⊢
    omega
  · intro x s raw hfit z hword
    let input := fun i : Operands e z.1 × Fin w => pre.eval x (s,pin e z.1 i.1,i.2)
    have hinput : (fun i => value (fun j => input (i,j))) = (fun i => word e raw (pin e z.1 i)) :=
      funext fun i => pe x s hfit (pin e z.1 i)
    have hvalue : (fun j => ((joint.select select).subst pre).eval x (s,z,j)) =
        ((expr e first z).frame w).eval input := by
      funext j
      simp [select,he,leaf,input]
      congr 1
      funext k
      simp
    have hsafe : (expr e first z).Fits w (fun i => value (fun j => input (i,j))) := hinput.symm ▸ hword
    rw [hvalue,(expr e first z).frame_value w input hsafe,hinput,expr_packet]

end Packing.BankJoint

end BorderVNP
end Computability
end OAI

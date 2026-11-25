import OAI.Computability.BorderVNP.PackedInheritedLayerCircuit

/-! # Freezing the nine scalar words of an inherited sparse tie

The row is emitted with site-local addresses. Its two address positions are
tagged for the eventual cell prefix. Other positions carry their final values.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open CellSparse ParseBatchSort VPVNP.VerifierNetwork Word
open scoped Classical

/-- Static relocation tags of an inherited record in the physical packet ABI. -/
def kind : Fin 9 → Kind := ![.plain,.plain,.plain,.bitAddress,.plain,.plain,.bitAddress,.plain,.plain]

private def add (a b : WidthExpr Arg) := WidthExpr.binary .add a b

/-- Scalar expression of each field of the compact one-copy interval command. -/
def field : Fin 9 → WidthExpr Arg :=
  ![.const 1,.const 1,.field .width,add (.field .work) (add (.field .oldBase) (.field .clip)),
    .const 0,.const 1,add (.field .extent) (.field .newBase),.const 0,.const 1]

/-- A local absolute-address tie read from the actual public operands. -/
def command (x : Arg → ℕ) : Record :=
  .equal 1 (x .width) ⟨x .work+(x .oldBase+x .clip),0,1⟩ ⟨x .extent+x .newBase,0,1⟩

/-- The nine emitted fields and their tags are exactly the annotated canonical record. -/
theorem fields_command (x : Arg → ℕ) :
    List.ofFn (fun i => (kind i,(field i).eval x)) = marked (command x) := rfl

private theorem field_nodes (i : Fin 9) : (field i).nodes ≤ 5 := by fin_cases i <;> decide

/-- A single local arithmetic pass adds the old and successor starts to their actual
staging prefixes. It preserves the computed owner and enable bit. -/
theorem emit {R σ : Type*} [Fintype R] [Fintype σ] (d w : ℕ)
    (src : Frame σ (R × Column d w)) :
    ∃ f : Frame σ (R × (Unit ⊕ (Fin d ⊕ Fin 9 × Fin w))),
      f.size ≤ src.size + 1 + Fintype.card R * (4500*(w+1)^2) ∧
      (∀ x r, f.eval x (r,.inl ()) = src.eval x (r,.inl ())) ∧
      (∀ x r j, f.eval x (r,.inr (.inl j)) = src.eval x (r,.inr (.inl j))) ∧
      ∀ (x : σ → Bool) (r : R),
        let vals := fun a => value (fun j => src.eval x (r,.inr (.inr (a,j))))
        1 < 2^w → vals .work + (vals .oldBase + vals .clip) < 2^w →
        vals .extent + vals .newBase < 2^w →
        List.ofFn (fun i => (kind i,value (fun j => f.eval x (r,.inr (.inr (i,j)))))) = marked (command vals) := by
  let leaf (q : R × Fin 9) : Frame (R × Column d w) (Fin w) :=
    ((field q.2).frame w).subst (Frame.initial fun i : Arg × Fin w => (q.1,.inr (.inr i)))
  obtain ⟨joint,hsize,eval⟩ := Crossing.exists_parallelFrames leaf
  let names (q : R × (Unit ⊕ (Fin d ⊕ Fin 9 × Fin w))) :
      (R × Column d w) ⊕ (Σ _ : R × Fin 9, Fin w) :=
    match q.2 with
    | .inl () => .inl (q.1,.inl ())
    | .inr (.inl j) => .inl (q.1,.inr (.inl j))
    | .inr (.inr (i,j)) => .inr ⟨(q.1,i),j⟩
  let result := (joint.withInput.select names).subst src
  refine ⟨result,?_,?_,?_,?_⟩
  · have bound (q : R × Fin 9) : (leaf q).size ≤ 500*(w+1)^2 := by
      have h := ((field q.2).frame_size w).trans (Nat.mul_le_mul_right _ (field_nodes q.2))
      simpa [leaf,← Nat.mul_assoc] using h
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun q _ => bound q)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul] at hs
    simp only [result,Frame.subst_size,Frame.select_size,Frame.withInput_size]
    calc
      _ ≤ src.size + (1 + Fintype.card R*9*(500*(w+1)^2)) := Nat.add_le_add_left
        (hsize.trans (Nat.add_le_add_left hs 1)) _
      _ = _ := by ring
  · intro x r; simp [result,names]
  · intro x r j; simp [result,names]
  · intro x r vals one oldRoom newRoom
    have wordRoom (a : Arg) : vals a < 2^w := value_lt _
    have mid : vals .oldBase + vals .clip < 2^w := by omega
    have fit (i : Fin 9) : (field i).Fits w vals := by
      fin_cases i <;> first
        | exact one
        | exact Nat.two_pow_pos _
        | exact wordRoom _
        | exact ⟨wordRoom .work,⟨wordRoom .oldBase,wordRoom .clip,mid⟩,oldRoom⟩
        | exact ⟨wordRoom _,wordRoom _,newRoom⟩
    have hword (i : Fin 9) : value (fun j => result.eval x (r,.inr (.inr (i,j)))) = (field i).eval vals := by
      let z := fun u : Arg × Fin w => src.eval x (r,.inr (.inr u))
      have hfun : (fun j => result.eval x (r,.inr (.inr (i,j)))) = ((field i).frame w).eval z := by
        funext j
        simp only [result,Frame.subst_eval,Frame.select_eval,names,Frame.withInput_eval_inr,eval,leaf]
        congr 1
        funext u
        simp [z]
      rw [hfun]
      exact (field i).frame_value w z (fit i)
    simpa only [hword] using fields_command vals

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI

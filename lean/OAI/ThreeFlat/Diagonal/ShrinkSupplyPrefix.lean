import OAI.ThreeFlat.Diagonal.PhysicalShrinkAssembly
import OAI.ThreeFlat.Diagonal.ShrinkSupplySend
import OAI.ThreeFlat.Diagonal.HistoryScopeOffsets

namespace OAI
/-! # The retained port prefix in the native successor half table -/

namespace ThreeFlat.Diagonal.CompressorPacking.SupplySend
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction Native.ShrinkStage
open scoped Classical BigOperators
noncomputable section

variable {V Tag Pins : Type} [Fintype V] [Fintype Tag] {d l : ℕ}
    (G : LiftedSlots (V × Tag) d (BitWord l)) (v : Site V Tag (BitWord l))

omit [Fintype V] [Fintype Tag] in
/-- A loop has a different physical ordinal on each of its two sides. -/
theorem successor_ordinal (a : (slotPortGraph G).Port v) :
    ((HalfOrder.order G v).symm a).val=halfOrdinal G a.val.1 a.val.2 := by
  rcases a with ⟨⟨e,b⟩,h⟩
  cases b <;> rfl

variable {width : Numbered V Tag (BitWord l) d → ℕ}
    (K : WordLayout (slotPortGraph G) width Pins)
    (count : K.count v=2*d)
    (order : ∀i, K.order v i=HalfOrder.order G v (i.cast count))

include count order in
/-- The supplied word layout may have any inherited external pins. Only its physical
order of incident ports contributes to the retained bit prefix. -/
theorem successor_prefix (a : (slotPortGraph G).Port v) :
    Halves.prefixValue G width ((v.1,v.2.1),v.2.2) ((HalfOrder.order G v).symm a)=K.ports.start v a := by
  let b:=(K.order v).symm a
  let j:=(HalfOrder.order G v).symm a
  have ord : b.cast count=j := by
    apply (HalfOrder.order G v).injective
    rw [←order]
    exact ((K.order v).apply_symm_apply a).trans ((HalfOrder.order G v).apply_symm_apply a).symm
  change Halves.prefixValue G width ((v.1,v.2.1),v.2.2) j=∑k:Fin b.val,K.ports.lengths v (Fin.castLE b.isLt.le k)
  rw [←ord]
  let f:=fun i : Fin (2*d)=>width (Halves.sourceHalf G ((v.1,v.2.1),v.2.2) i)
  let E : Fin b.val ≃ {k : Fin (2*d) // k.val<b.val} :=
    ⟨fun k=>⟨⟨k.val,k.isLt.trans (b.isLt.trans_eq count)⟩,k.isLt⟩,fun k=>⟨k.val.val,k.property⟩,
      fun _=>rfl,fun _=>rfl⟩
  change (∑ i : Fin (2*d), if i.val<b.val then f i else 0)=_
  rw [←Finset.sum_filter,←Finset.sum_subtype_eq_sum_filter,Finset.subtype_univ]
  calc
    _ = ∑ k : Fin b.val, f (E k).val := (E.sum_comp (fun i=>f i.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      let i:=Fin.castLE b.isLt.le k
      change width (Halves.sourceHalf G ((v.1,v.2.1),v.2.2) (i.cast count))=width (K.order v i).val.1
      rw [order,PhysicalStage.shrinkHalf_value]

include count order in
/-- Every geometrically numbered half prefix fits inside the whole public half bank. -/
theorem successor_prefix_le (i:Fin (2*d)) :
    Halves.prefixValue G width ((v.1,v.2.1),v.2.2) i≤K.ports.halfBits v := by
  let a:=HalfOrder.order G v i
  have h:=successor_prefix G v K count order a
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  let hpos:=(K.order v).symm a
  change (∑ b : Fin hpos.val,K.ports.lengths v (b.castLE hpos.isLt.le))≤∑ j,K.ports.lengths v j
  exact Finset.sum_le_sum_of_injOn (Fin.castLE hpos.isLt.le) (fun _ _ _ _ he => (Fin.castLEEmb hpos.isLt.le).injective he)
    (Finset.subset_univ _) (fun _ _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _)

include count order in
/-- Apply the stored successor's `HalfRows.start` at the actual supply-side port.
For a shrink layout (including its inherited external pins), `count` and `order` are reflexivity. -/
theorem successor_half_row (mem : ℕ→ℕ) (table : ℕ)
    (rows : ∀i : Fin (2*d), mem (table+4*i.val+3)=Halves.prefixValue G width ((v.1,v.2.1),v.2.2) i)
    (a : (slotPortGraph G).Port v) :
    mem (table+(4*halfOrdinal G a.val.1 a.val.2+3))=K.ports.start v a := by
  rw [←successor_ordinal G v a,←Nat.add_assoc]
  exact (rows _).trans (successor_prefix G v K count order a)


end
end ThreeFlat.Diagonal.CompressorPacking.SupplySend

end OAI

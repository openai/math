import OAI.Computability.VPVNP.CompressorBundleFixedGather

/-!
# Dense cursor order and physical addresses for the fixed-bank key gather

Each cursor decodes to a packed port and an element of the disjoint sum of
its thick and motif entries. The physical address embeds this sum into two
separate sets of equal-stride rows. Both maps work with empty classes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleGather.Fixed

open BurstRAM BundleKeys
open ShrinkRAM (div mod)
open scoped Fin.CommRing

variable {w : ℕ} (t : KeyTable w)

/-- A live entry identified by a bundle and either a thick-wire index or a motif index. -/
abbrev Entry (t : KeyTable w) := Fin t.bundles × (Fin t.thickCount ⊕ Fin t.motifCount)
/-- Total number of live thick-wire and motif entries across all bundles. -/
abbrev entryCount (t : KeyTable w) := t.bundles*(t.thickCount+t.motifCount)
/-- Number of physical slots reserved for the two strided row banks, including padding. -/
abbrev slots (t : KeyTable w) := (t.bundles+t.bundles)*t.stride

/-- Number the live entries consecutively, using the thick-wire indices before the motif
indices within each bundle. -/
def entryIndex : Entry t ≃ Fin (entryCount t) :=
  ((Equiv.refl (Fin t.bundles)).prodCongr finSumFinEquiv).trans finProdFinEquiv

/-- Place thick-wire entries in the first bank of rows and motif entries in the second,
retaining their index within each row. -/
def physical (reg : t.Layout) : Entry t ↪ Fin (t.bundles+t.bundles) × Fin t.stride where
  toFun z := match z.2 with
    | .inl i => (finSumFinEquiv (.inl z.1),i.castLE reg.thickFits)
    | .inr i => (finSumFinEquiv (.inr z.1),i.castLE reg.motifFits)
  inj' := by
    rintro ⟨a,i | i⟩ ⟨b,j | j⟩ h <;>
      have hr := finSumFinEquiv.injective (congrArg Prod.fst h)
    · exact Prod.ext (Sum.inl.inj hr) (congrArg Sum.inl (Fin.ext (congrArg (Fin.val ∘ Prod.snd) h)))
    · contradiction
    · contradiction
    · exact Prod.ext (Sum.inr.inj hr) (congrArg Sum.inr (Fin.ext (congrArg (Fin.val ∘ Prod.snd) h)))

/-- Map the dense cursor range bijectively onto the live rectangular slots. -/
def slot (reg : t.Layout) : Fin (entryCount t) ↪ Fin (slots t) :=
  (entryIndex t).symm.toEmbedding.trans ((physical t reg).trans finProdFinEquiv.toEmbedding)

/-- The gather worker's seven operands, encoding the row dimensions and the identifier,
lookup-key and output bases. -/
def parameters : Fin 7 → Word w :=
  ![word (t.thickCount+t.motifCount),word t.thickCount,word t.bundles,word t.stride,
    t.idsBase,t.keyBase,t.outputBase]

private theorem word_add (a b : ℕ) : word (w := w) a + word b = word (a+b) :=
  Fin.ext (Nat.add_mod ..).symm

private theorem word_mul (a b : ℕ) : word (w := w) a * word b = word (a*b) :=
  Fin.ext (Nat.mul_mod ..).symm

private theorem div_val (a b : Word w) : (div a b).val = a.val/b.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt a.isLt)

private theorem mod_val (a b : Word w) : (mod a b).val = a.val%b.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt a.isLt)

private theorem word_ext {i : Word w} {k : ℕ} (h : i.val = k) : i = word k := by
  subst k; exact Fin.ext (Nat.mod_eq_of_lt i.isLt).symm

private theorem mark (z k : Word w) (hz : z.val+1 < 2^w) :
    let q := div k (z+1)
    1-div q q = if z.val < k.val then 0 else 1 := by
  intro q
  have hs : (z+1).val = z.val+1 := by
    rw [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1 < 2^w by omega),Nat.mod_eq_of_lt hz]
  have hq : q.val = k.val/(z.val+1) := (div_val _ _).trans (by rw [hs])
  by_cases h : z.val < k.val
  · have hp := Nat.div_pos (Nat.succ_le_of_lt h) (Nat.zero_lt_succ z.val)
    have he : div q q = 1 := by
      apply Fin.ext
      rw [div_val,Nat.div_self (hq ▸ hp),Fin.val_one',Nat.mod_eq_of_lt (by omega)]
    simp [he,h]
  · have he : q.val = 0 := hq.trans (Nat.div_eq_of_lt (by omega))
    have eqn : div q q = 0 := Fin.ext (by rw [div_val,he,Nat.div_zero,Fin.val_zero])
    simp [eqn,h]

/-- The native decoder gives the exact embedded slot. The stop word of the
absolute-port scan represents its full entry count. -/
theorem offset_eq (reg : t.Layout) (hsize : entryCount t < 2^w) (j : Fin (entryCount t)) :
    (offset (parameters t) (word j.val)).val = (slot t reg j).val := by
  obtain ⟨z,rfl⟩ := (entryIndex t).surjective j
  let b := z.1
  let u := finSumFinEquiv z.2
  let m := t.thickCount+t.motifCount
  let i := word (w := w) (entryIndex t z).val
  have hb : 0 < t.bundles := b.isLt.pos
  have hm : 0 < m := u.isLt.pos
  have hmf : m < 2^w := (Nat.le_mul_of_pos_left m hb).trans_lt hsize
  have hcf : t.thickCount < 2^w := (Nat.le_add_right ..).trans_lt hmf
  have hi : i.val = (entryIndex t z).val := Nat.mod_eq_of_lt ((entryIndex t z).isLt.trans hsize)
  have he : (entryIndex t z).val = m*b.val + u.val := by change u.val + m*b.val = _; omega
  have hmword : ((parameters t) 0).val = m := Nat.mod_eq_of_lt hmf
  have hd : (div i ((parameters t) 0)).val = b.val := by
    rw [div_val,hi,he,hmword,Nat.mul_add_div hm,Nat.div_eq_of_lt u.isLt,Nat.add_zero]
  have hu : (mod i ((parameters t) 0)).val = u.val := by
    rw [mod_val,hi,he,hmword,Nat.mul_comm m b.val,Nat.mul_add_mod_of_lt u.isLt]
  have hmkr := mark (mod i ((parameters t) 0)) ((parameters t) 1)
    (show (mod i ((parameters t) 0)).val+1 < 2^w by rw [hu]; exact (Nat.succ_le_of_lt u.isLt).trans_lt hmf)
  rw [hu, show ((parameters t) 1).val = t.thickCount from Nat.mod_eq_of_lt hcf] at hmkr
  change (offset (parameters t) i).val = _
  rw [offset,hmkr,word_ext hd,word_ext hu]
  have hslot : slot t reg (entryIndex t z) = finProdFinEquiv (physical t reg z) := by
    simp [slot]
  rw [hslot]
  obtain ⟨b', v | v⟩ := z
  · have hlt : u.val < t.thickCount := v.isLt
    rw [ite_eq_left hlt,zero_mul,add_zero,zero_mul,sub_zero]
    change (word b'.val * word t.stride + word v.val).val = _
    rw [word_mul,word_add,Fin.val_ofNat]
    change (b'.val*t.stride+v.val) % (2^w) = v.val + t.stride * b'.val
    have bound := Nat.mul_le_mul_right t.stride (b'.isLt.trans_le (Nat.le_mul_of_pos_left t.bundles (by decide : 0<2)))
    rw [Nat.succ_mul] at bound
    have fit := reg.outputFits
    change t.outputBase.val+(2*t.bundles)*t.stride ≤ 2^w at fit
    rw [Nat.mod_eq_of_lt (by have := v.isLt.trans_le reg.thickFits; omega)]
    ac_rfl
  · have uval : u.val = t.thickCount+v.val := rfl
    rw [ite_eq_right (by rw [uval]; omega : ¬ u.val < t.thickCount),one_mul,one_mul,uval]
    change ((word b'.val + word t.bundles) * word t.stride +
      (word (t.thickCount+v.val)-word t.thickCount)).val = _
    rw [← word_add,add_sub_cancel_left,word_add,word_mul,word_add,Fin.val_ofNat]
    change ((b'.val+t.bundles)*t.stride+v.val) % (2^w) = v.val + t.stride * (t.bundles+b'.val)
    have bound := Nat.mul_le_mul_right t.stride (show b'.val+t.bundles+1 ≤ 2*t.bundles by have := b'.isLt; omega)
    rw [Nat.succ_mul] at bound
    have fit := reg.outputFits
    change t.outputBase.val+(2*t.bundles)*t.stride ≤ 2^w at fit
    rw [Nat.mod_eq_of_lt (by have := v.isLt.trans_le reg.motifFits; omega)]
    ac_rfl

end CompressorRecords.BundleGather.Fixed

end VPVNP
end Computability
end OAI

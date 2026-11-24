import OAI.Computability.VPVNP.CompressorRecordsDemandScan

/-!
# Constructing the genuine old-arc inputs of the slot compiler

Starting with the previous level's incidence and the selected layout's placement
columns, scan every directed old port once. The output occupies four consecutive
words per absolute old-arc ID. The CD flag and selected role cells then have exactly
the types and indexing read by the genuine-slot worker.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DemandRAM

open Compression Compression.SurvivingSlots BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w a g : ℕ} (X : State a (packingLaneBits a g))

/-- Number of directed old slots visited in site-major order, counting every base vertex,
packing lane and outgoing port. -/
abbrev oldCount := Fintype.card X.Base * 2^(packingLaneBits a g) * 2^a
/-- Size of the absolute old-arc directory, counting all base arc identifiers across the
residual lanes. -/
abbrev absoluteCount := Slots.oldBaseArcCount (Fintype.card X.Base) (2^(Shrink.J a)) (2^a) (Shrink.colors a) * 2^g
/-- The bijection that assigns each old arc its absolute directory index with the residual lane
as the least significant coordinate. -/
abbrev absoluteIndex := Slots.oldArcIndex X.packingData X.baseIndex (bitWordFinEquiv (Shrink.J a)) (bitWordFinEquiv g)

theorem count_eq : oldCount X = absoluteCount X := by
  have h := Fintype.card_congr ((BundleKeys.oldArcOrder X.baseIndex).symm.trans (absoluteIndex X))
  simpa using h

private theorem fieldAddr_word (p : Fin 11 → Word w) (i : Word w) (t : Fin 4) :
    fieldAddr p i t = (address p i + (t.val : Word w)).val := by
  fin_cases t <;> simp [fieldAddr] <;> congr 1 <;> ring

theorem fieldAddr_exact {p : Fin 11 → Word w} {B : ℕ} (hp : BundleRAM.Params p a (Shrink.colors a) (Shrink.J a) g B)
    (room : (p 10).val + 4*absoluteCount X ≤ 2^w) (e : BundleKeys.OldArc X.Base a g) {i : Word w}
    (hi : i.val = (BundleKeys.oldArcOrder X.baseIndex e).val) (t : Fin 4) :
    fieldAddr p i t = (p 10).val+4*(absoluteIndex X e).val+t.val := by
  rw [fieldAddr_word, address_exact X.slots X.baseIndex hp e hi]
  have fit : (p 10).val+4*(absoluteIndex X e).val+t.val < 2^w := by
    have h : (absoluteIndex X e).val < absoluteCount X := (absoluteIndex X e).isLt
    have ht := t.isLt
    omega
  have eqw : p 10 + 4 * ((absoluteIndex X e).val : Word w) + (t.val : Word w) =
      (((p 10).val + 4*(absoluteIndex X e).val + t.val : ℕ) : Word w) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul]
    have h : ((p 10).val : Word w) = p 10 := Fin.ext (Nat.mod_eq_of_lt (p 10).isLt)
    simp [h]
  rw [eqw]
  exact Nat.mod_eq_of_lt fit

/-- The old-site port order and absolute arc order are two bijections of the same
finite space. Consequently the four-word output rows are disjoint in memory. -/
theorem regions {p : Fin 11 → Word w} {B : ℕ} (hp : BundleRAM.Params p a (Shrink.colors a) (Shrink.J a) g B)
    (old : Memory w) (room : (p 10).val + 4*absoluteCount X ≤ 2^w)
    (outside : ∀ (i : Word w) (c : Fin 6), i.val < oldCount X →
      inputAddr p old i c < (p 10).val ∨ (p 10).val+4*absoluteCount X ≤ inputAddr p old i c) :
    Regions p old (oldCount X) := by
  let E := BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
  let src (i : Word w) (h : i.val<oldCount X) := E.symm ⟨i.val,h⟩
  have idx (i : Word w) (h : i.val<oldCount X) : i.val = (E (src i h)).val := by simp [src]
  have bound (i : Word w) (h : i.val<oldCount X) (t : Fin 4) :
      fieldAddr p i t < (p 10).val + 4*absoluteCount X := by
    rw [fieldAddr_exact X hp room _ (idx i h)]
    have h₀ : (absoluteIndex X (src i h)).val < absoluteCount X := (absoluteIndex X (src i h)).isLt
    have := t.isLt
    omega
  constructor
  · rw [count_eq X]; omega
  · intro i j t u hi hj
    rw [fieldAddr_exact X hp room _ (idx i hi), fieldAddr_exact X hp room _ (idx j hj)]
    constructor
    · intro eq
      have ht := t.isLt
      have hu := u.isLt
      have same : (absoluteIndex X (src i hi)).val = (absoluteIndex X (src j hj)).val := by omega
      have es := (absoluteIndex X).injective (Fin.ext same)
      exact ⟨Fin.ext ((idx i hi).trans ((congrArg (fun e => (E e).val) es).trans (idx j hj).symm)),
        Fin.ext (by omega)⟩
    · rintro ⟨rfl,rfl⟩; rfl
  · intro i j c t hi hj
    have h₀ := outside i c hi
    have h₁ := bound j hj t
    rw [fieldAddr_exact X hp room _ (idx j hj)] at *
    omega

/-- The exact two data predicates consumed by the surviving-slot generator. -/
structure RoleColumns (layout : Bool) (base : ℕ) (m : Memory w) : Prop where
  cd : ∀ e, (m (base+4*(absoluteIndex X e).val+3)).val = if Slots.isCD X.packingData e then 1 else 0
  packed : ∀ (e : X.packingData.Motif) (r : PackedRole),
    (m (base+4*(absoluteIndex X e.val).val+SlotOwners.roleOffset r)).val =
      (SlotSchedule.siteIndex X.baseIndex (bitWordFinEquiv (Shrink.J a)) (bitWordFinEquiv g)
        (X.packingData.survivingRole layout r e)).val

theorem run_roles (T : IncidenceDirectory w) {p : Fin 11 → Word w} {shr : Fin 14 → Word w}
    {m : Memory w} {layout : Bool} {B : ℕ} (hp : BundleRAM.Params p a (Shrink.colors a) (Shrink.J a) g B)
    (h : Inputs p shr T) (inc : T.ActualColumns X m) (place : ShrinkRAM.PlacementColumns X.slots X.baseIndex shr layout m)
    (room : (p 10).val+4*absoluteCount X ≤ 2^w)
    (outside : ∀ (i : Word w) (c : Fin 6), i.val<oldCount X →
      inputAddr p m i c < (p 10).val ∨ (p 10).val+4*absoluteCount X ≤ inputAddr p m i c) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 65 (some 0) m (List.replicate (oldCount X) []) = some rs ∧
      RoleColumns X layout (p 10).val (after m (eventLog rs)) ∧
      (∀ x, x<(p 10).val ∨ (p 10).val+4*absoluteCount X ≤ x → after m (eventLog rs) x = m x) ∧
      rs.length = oldCount X ∧ (∀ r ∈ rs, r.events.length=64 ∧ countProbes r.events=10) ∧
      RAMBuckets.cost Report.probes rs = 11*oldCount X := by
  let E := BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
  let old (e : BundleKeys.OldArc X.Base a g) : Word w := ShrinkRAM.word w (E e).val
  let reg := regions X hp m room outside
  have hval (e : BundleKeys.OldArc X.Base a g) : (old e).val = (E e).val := Nat.mod_eq_of_lt ((E e).isLt.trans_le reg.fits)
  obtain ⟨rs,hr,hout,hl,hwork,hcost⟩ := scan_run (k := 0) (n := oldCount X) reg (Written.start p m) (by simp)
  let mem := after m (eventLog rs)
  have out (e : BundleKeys.OldArc X.Base a g) (t : Fin 4) :
      mem ((p 10).val+4*(absoluteIndex X e).val+t.val) = (roles p m (old e)).field t := by
    rw [← fieldAddr_exact X hp room e (hval e) t]
    apply hout.row
    rw [hval,Nat.zero_add]; exact (E e).isLt
  have sem (e : BundleKeys.OldArc X.Base a g) := roles_exact X T h inc place hp.degree reg.fits e (hval e)
  refine ⟨rs,hr,⟨?_,?_⟩,?_,hl,hwork,hcost⟩
  · intro e
    have hd := (sem e).1
    have ho := out e 3
    change mem ((p 10).val+4*(absoluteIndex X e).val+3) = (roles p m (old e)).cd at ho
    change (mem _).val = _
    rw [ho, hd]
    have h₀ : (absoluteIndex X e).val < absoluteCount X := (absoluteIndex X e).isLt
    have h1 : (1 : Word w).val = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega : 1 < 2^w)
    split <;> first | exact h1 | rfl
  · intro e r
    let v := X.packingData.survivingRole layout r e
    have hv : Shrink.packedNumber X.baseIndex v < 2^w := by
      have hsite := (Shrink.packedIndex X.baseIndex v).isLt
      rw [Shrink.packedIndex_val] at hsite
      have hcard : Fintype.card X.Base*(2^(Shrink.J a)*2^g) ≤ oldCount X := by
        rw [← pow_add]
        apply (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
          (show Shrink.J a+g ≤ packingLaneBits a g by unfold Shrink.J packingLaneBits; omega))).trans
        exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      exact hsite.trans_le (hcard.trans reg.fits)
    have hslot : (SlotSchedule.siteIndex X.baseIndex (bitWordFinEquiv (Shrink.J a)) (bitWordFinEquiv g) v).val =
      Shrink.packedNumber X.baseIndex v := Shrink.packedIndex_val X.baseIndex v
    rw [hslot]
    have H := (sem e.val).2 e.prop
    have hrole : mem ((p 10).val+4*(absoluteIndex X e.val).val+SlotOwners.roleOffset r) =
        (Shrink.packedNumber X.baseIndex v : Word w) := by
      cases r with
      | a => exact (out e.val 0).trans H.1
      | b => exact (out e.val 1).trans H.2.1
      | d => exact (out e.val 2).trans H.2.2
    change (mem _).val = _
    rw [hrole]; exact Nat.mod_eq_of_lt hv
  · intro x hx
    apply hout.frame
    intro i t hi
    let e := E.symm ⟨i.val,by simpa only [Nat.zero_add] using hi⟩
    have hidx : i.val=(E e).val := by simp [e]
    rw [fieldAddr_exact X hp room _ hidx]
    have h₀ : (absoluteIndex X e).val < absoluteCount X := (absoluteIndex X e).isLt
    have := t.isLt
    omega

end CompressorRecords.DemandRAM

end VPVNP
end Computability
end OAI

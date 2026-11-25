import OAI.Computability.NearSquareRoot.KernelComputableMatrix
import OAI.Computability.NearSquareRoot.KernelComputableAddressLeaves
import OAI.Computability.NearSquareRoot.KernelPassCutoff

/-! # Primitive recursive finite-matrix test for a binary program

The uniform validator checks every entry up to the syntactic width cutoff.
Both the ideal target and the candidate use the same row-major and base-four
address order. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

open KernelComputableAddress KernelComputableMatrix

def volume (A h : ℕ) := (4^A)^h

theorem volume_pos (A h : ℕ) : 0 < volume A h := by unfold volume; positivity

def entryMatches (A W h : ℕ) (t : Table) (r c : ℕ) : Prop :=
  let V := volume A h
  KernelComputableDyadic.equal (entry (W*V) t r c)
    (KernelComputableAddress.target A h (r/V) (c/V) (r%V) (c%V)) = true

instance (A W h : ℕ) (t : Table) (r c : ℕ) : Decidable (entryMatches A W h t r c) :=
  inferInstanceAs (Decidable (_ = true))

def matrixMatches (A W h : ℕ) (t : Table) : Prop :=
  ∀ r < W*volume A h, ∀ c < W*volume A h, entryMatches A W h t r c

instance (A W h : ℕ) (t : Table) : Decidable (matrixMatches A W h t) :=
  inferInstanceAs (Decidable (∀ r < W*volume A h, ∀ c < W*volume A h, entryMatches A W h t r c))

theorem matrixMatches_iff {A W h : ℕ} {p : Plan A W W} {t : Table}
    (ht : Represents (W*volume A h) (bankIndex (pack A h)) (bankIndex (pack A h)) t (p.eval h)) :
    matrixMatches A W h t ↔ p.eval h = KernelPass.target A W h := by
  let V := volume A h
  let num (v : Fin W × Addr A h) := bankIndex (pack A h) v
  have lt (v : Fin W × Addr A h) : num v < W*V := by
    change v.1.val * V + (pack A h v.2).val < W*V
    have hv := (pack A h v.2).isLt
    change _ < V at hv
    calc
      _ < v.1.val * V + V := Nat.add_lt_add_left hv _
      _ = (v.1.val+1)*V := (Nat.succ_mul _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ v.1.isLt
  have entry_iff (u v : Fin W × Addr A h) : entryMatches A W h t (num u) (num v) ↔
      p.eval h u v = KernelPass.target A W h u v := by
    unfold entryMatches
    dsimp only
    rw [KernelComputableDyadic.equal_iff, ht u v]
    have e (i : Fin W × Addr A h) : num i / volume A h = i.1.val ∧
        num i % volume A h = (pack A h i.2).val := by
      have hlt : (pack A h i.2).val < volume A h := (pack A h i.2).isLt
      change (i.1.val * volume A h + _) / _ = _ ∧ (i.1.val * volume A h + _) % _ = _
      rw [Nat.mul_comm i.1.val (volume A h), Nat.mul_add_div (volume_pos _ _), Nat.mul_add_mod,
        Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, Nat.add_zero]
      exact ⟨rfl,rfl⟩
    rw [(e u).1,(e v).1,(e u).2,(e v).2,value_target]
  constructor
  · intro obs
    ext u v
    exact (entry_iff u v).mp (obs (num u) (lt u) (num v) (lt v))
  · intro he r hr c hc
    let read (n : ℕ) (hn : n < W*V) : Fin W × Addr A h :=
      (⟨n/V, (Nat.div_lt_iff_lt_mul (volume_pos A h)).mpr hn⟩,
        (pack A h).symm ⟨n%V,Nat.mod_lt _ (volume_pos A h)⟩)
    have inv (n : ℕ) (hn : n < W*V) : num (read n hn) = n := by
      change n/V * V + (pack A h ((pack A h).symm _)).val = _
      rw [Equiv.apply_symm_apply]
      exact Nat.div_add_mod' _ _
    have e := (entry_iff (read r hr) (read c hc)).mpr (congrFun (congrFun he _) _)
    simpa only [inv] using e

private theorem primrec_ball {X : Type*} [Primcodable X] {n : X → ℕ} {P : X → ℕ → Prop}
    (hn : Primrec n) (hp : PrimrecPred (fun t : X × ℕ => P t.1 t.2)) :
    PrimrecPred (fun x => ∀ k < n x, P x k) := by
  have rel : PrimrecRel (fun k x => P x k) := (hp.comp (Primrec.snd.pair Primrec.fst)).primrecRel
  exact (rel.forall_mem_list.comp (Primrec.list_range.comp hn) Primrec.id).of_eq (by simp)

theorem primrec_volume {X : Type*} [Primcodable X] {A h : X → ℕ}
    (hA : Primrec A) (hh : Primrec h) : Primrec fun x => volume (A x) (h x) :=
  primrec_pow (primrec_pow (Primrec.const 4) hA) hh

theorem primrec_entryMatches {X : Type*} [Primcodable X] {A W h r c : X → ℕ} {t : X → Table}
    (hA : Primrec A) (hW : Primrec W) (hh : Primrec h) (ht : Primrec t) (hr : Primrec r) (hc : Primrec c) :
    PrimrecPred fun x => entryMatches (A x) (W x) (h x) (t x) (r x) (c x) := by
  let hV := primrec_volume hA hh
  exact Primrec.eq.comp (KernelComputableDyadic.primrec_equal.comp (primrec_entry
    (Primrec.nat_mul.comp hW hV) ht hr hc) (primrec_target hA hh (Primrec.nat_div.comp hr hV)
      (Primrec.nat_div.comp hc hV) (Primrec.nat_mod.comp hr hV) (Primrec.nat_mod.comp hc hV)))
    (Primrec.const true)

theorem primrec_matrixMatches {X : Type*} [Primcodable X] {A W h : X → ℕ} {t : X → Table}
    (hA : Primrec A) (hW : Primrec W) (hh : Primrec h) (ht : Primrec t) :
    PrimrecPred fun x => matrixMatches (A x) (W x) (h x) (t x) := by
  have hn := Primrec.nat_mul.comp hW (primrec_volume hA hh)
  apply primrec_ball hn
  apply primrec_ball (hn.comp Primrec.fst)
  exact primrec_entryMatches (hA.comp (Primrec.fst.comp Primrec.fst))
    (hW.comp (Primrec.fst.comp Primrec.fst)) (hh.comp (Primrec.fst.comp Primrec.fst))
    (ht.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst) Primrec.snd

/-- Test the entire finite range of child widths. -/
def allWidths (A W bound : ℕ) (tableAt : ℕ → Table) : Prop :=
  ∀ h < bound+1, matrixMatches A W h (tableAt h)

instance (A W bound : ℕ) (u : ℕ → Table) : Decidable (allWidths A W bound u) :=
  inferInstanceAs (Decidable (∀ h < bound+1, matrixMatches A W h (u h)))

theorem primrec_allWidths {X : Type*} [Primcodable X] {A W bound : X → ℕ} {t : X → ℕ → Table}
    (hA : Primrec A) (hW : Primrec W) (hb : Primrec bound) (ht : Primrec₂ t) :
    PrimrecPred fun x => allWidths (A x) (W x) (bound x) (t x) := by
  apply primrec_ball (Primrec.succ.comp hb)
  exact primrec_matrixMatches (hA.comp Primrec.fst) (hW.comp Primrec.fst) Primrec.snd ht

theorem allWidths_iff {A W : ℕ} (p : Plan A W W) (t : ℕ → Table)
    (ht : ∀ h, Represents (W*volume A h) (bankIndex (pack A h)) (bankIndex (pack A h)) (t h) (p.eval h)) :
    allWidths A W p.stateBound t ↔ Correct p := by
  rw [correct_iff_bounded]
  exact ⟨fun h i hi => (matrixMatches_iff (ht i)).mp (h i (by omega)),
    fun h i hi => (matrixMatches_iff (ht i)).mpr (h i (by omega))⟩

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI

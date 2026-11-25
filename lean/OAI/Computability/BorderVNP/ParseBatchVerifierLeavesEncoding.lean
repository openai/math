import OAI.Computability.BorderVNP.ParseBatchRecordsQuery
import OAI.Computability.BorderVNP.ParseBatchRecordBits
import OAI.Computability.BorderVNP.ParseBatchSortCompare

/-!
# Padded leaf keys for a preorder query block

A key uses a dummy tag, the selected bit and the binary position. Internal
records and the unused sorting lanes have a single, fixed dummy code.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLeaves

open VPVNP BorderVNP.ParseRecords BorderVNP.ParseBatchSort

variable {α : Type*} {m g n rows cap : ℕ}

/-- Fill unused sorting lanes with one fixed value. -/
def pad (rows : Fin rows → α) (dummy : α) (i : Fin cap) : α :=
  if h : i.val < _ then rows ⟨i.val,h⟩ else dummy

private theorem ofFn_pad (a : Fin rows → α) (z : α) (h : rows ≤ cap) :
    List.ofFn (pad (cap := cap) a z) = List.ofFn a ++ List.replicate (cap-rows) z := by
  apply List.ext_getElem
  · simp; omega
  · intro j hj hk
    simp only [List.getElem_ofFn, pad, List.getElem_append, List.length_ofFn]
    split <;> simp_all

/-- The numeric position in a canonical record fits the word width. -/
theorem position_lt (g n : ℕ) (i : Fin m) : i.val < 2 ^ recordWidth m g n :=
  i.isLt.trans_le ((le_max_left ..).trans ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)))

/-- The prefix discriminates dummy keys and the selected bit. The position field
retains the same bit order as the physical record. -/
def keyBits (g n : ℕ) : Option (Fin m × Bool) → Fin (recordWidth m g n + 2) → Bool
  | none => Fin.cons true (fun _ => false)
  | some (i, b) => Fin.cons false (Fin.cons b (RAMSerialization.wordBits _ ⟨i.val, position_lt g n i⟩))

/-- Distinct labels, including the dummy, have distinct binary keys. -/
theorem keyBits_injective (m g n : ℕ) : Function.Injective (@keyBits m g n) := by
  rintro (_ | ⟨i,b⟩) (_ | ⟨j,c⟩) e
  · rfl
  · have h := congrFun e 0; simp [keyBits] at h
  · have h := congrFun e 0; simp [keyBits] at h
  · have h := Fin.cons_inj.mp e
    have ht := Fin.cons_inj.mp h.2
    have hij : i = j := Fin.ext (congrArg (fun z : Fin (2 ^ recordWidth m g n) => z.val) ((RAMSerialization.wordBits _).injective ht.2))
    rw [hij, ht.1]

/-- The two sorting arrays contain the same padded words exactly when the queried
variables have the multiset prescribed by the actual leaf records. -/
theorem padded_keys_iff (d : Fin n) (q : Fin m → Fin m × Bool)
    (records : Fin rows → GrammarLabel (Fin m × Bool) (Fin g) n)
    (hd : rows = 2*d.val+1) (hm : m = d.val+1) (hcap : rows ≤ cap) :
    (List.ofFn fun i : Fin cap => value (keyBits g n (pad (terminal ∘ records) none i))).Perm
      (List.ofFn fun i : Fin cap => value (keyBits g n (pad (some ∘ q) none i))) ↔
        Matches d q (List.ofFn records) := by
  let K := value ∘ (@keyBits m g n)
  have hK : Function.Injective K := (value_injective _).comp (keyBits_injective m g n)
  have hrep : Multiset.replicate (cap - m) (none : Option (Fin m × Bool)) =
      Multiset.replicate d.val none + Multiset.replicate (cap - rows) none := by
    rw [← Multiset.replicate_add]
    congr 1; omega
  change (List.ofFn (K ∘ pad (cap := cap) (terminal ∘ records) none)).Perm
    (List.ofFn (K ∘ pad (cap := cap) (some ∘ q) none)) ↔ _
  rw [← List.map_ofFn, ← List.map_ofFn, ← Multiset.coe_eq_coe]
  change Multiset.map K (List.ofFn (pad (cap := cap) (terminal ∘ records) none)) =
    Multiset.map K (List.ofFn (pad (cap := cap) (some ∘ q) none)) ↔ _
  rw [(Multiset.map_injective hK).eq_iff, ofFn_pad _ _ hcap, ofFn_pad _ _ (by omega : m ≤ cap)]
  simp only [← Multiset.coe_add, Multiset.coe_replicate]
  change _ ↔ (List.map terminal (List.ofFn records) : Multiset (Option (Fin m × Bool))) =
    Multiset.replicate d.val none + Multiset.map some (List.ofFn q)
  rw [hrep, ← add_assoc, add_left_inj]
  simp [List.map_ofFn, Function.comp_def, add_comm]

end ParseBatchLeaves

end BorderVNP
end Computability
end OAI

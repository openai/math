import OAI.ThreeFlat.RAM.StableCompactROMEntry
import OAI.ThreeFlat.RAM.StableCompactPadProgram
import OAI.ThreeFlat.RAM.StableCompactAddress

namespace OAI
/-! # The twelve static ROM words attached to one compaction template row -/

noncomputable section
namespace ThreeFlat.RAM.StableCompactROMEntries

open Computability.VPVNP.BurstRAM BitLayout Routing.StableCompactRows StableCompactROMProgram
open scoped Classical Fin.CommRing

variable {F : Type*} {m h w : ℕ}

abbrev Table (F : Type*) := (Fin 3 → Bool) → F

/-- All factors over the same finite coefficient alphabet have one shared table library. -/
def tableId [Fintype F] (t : Table F) : Fin (Fintype.card (Table F)) := Fintype.equivFin _ t

def globalTable [Fintype F] (id : Fin (Fintype.card (Table F))) : Table F := (Fintype.equivFin _).symm id

@[simp] theorem globalTable_id [Fintype F] (t : Table F) : globalTable (tableId t) = t :=
  (Fintype.equivFin _).symm_apply_apply t

def sourceEntry : Source m h → Entry
  | .constant b => .literal b.toNat
  | .siteBit j => if j<m then .siteBit j else .literal 0
  | .pin s => .pin s
  | .hidden r mask => .hidden r.val mask.val

theorem sourceEntry_fits (s : Source m h) (sites : 2^m < 2^w) : (sourceEntry s).Fits w := by
  cases s with
  | constant _ | pin _ => trivial
  | siteBit j =>
    by_cases hj : j<m
    · simp only [sourceEntry,ite_eq_left hj,Entry.Fits]
      exact hj.trans ((Nat.lt_two_pow_self : m < 2^m).trans sites)
    · simp only [sourceEntry,ite_eq_right hj,Entry.Fits]
  | hidden _ mask => exact mask.isLt.trans sites

theorem sourceEntry_at (s : Source m h) (n : ℕ) (hn : n ≤ 2^m) (v : Fin (2^m)) :
    (sourceEntry s).atSite (2^m) n v.val =
      StableCompactPadProgram.remap (2^m) n (sourceAddress (s.physical v)) := by
  cases s with
  | constant b =>
    exact (StableCompactPadProgram.remap_constant (2^m) n b.toNat (by cases b <;> decide)).symm
  | siteBit j =>
    change _ = StableCompactPadProgram.remap (2^m) n (v.val.testBit j).toNat
    rw [StableCompactPadProgram.remap_constant _ _ _ (by cases v.val.testBit j <;> decide)]
    by_cases hj : j<m
    · simp only [sourceEntry,ite_eq_left hj,Entry.atSite]
    · have bit := Nat.testBit_lt_two_pow (x:=v.val) (i:=j)
          (v.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hj)))
      simp [sourceEntry,hj,bit,Entry.atSite]
  | pin s =>
    simpa only [sourceEntry,Entry.atSite,Source.physical,sourceAddress,bankPin_val,Nat.add_assoc] using
      (StableCompactPadProgram.remap_pin (2^m) n s v hn).symm
  | hidden r mask =>
    have addr : sourceAddress ((Source.hidden r mask).physical v) =
        2+3*2^m + (r.val*2^m + (v.val ^^^ mask.val)) := by
      simp only [Source.physical,sourceAddress,hiddenBase,finProdFinEquiv,Equiv.coe_fn_mk,
        Fin.xor_val_of_two_pow,show (2^m+(2^m+2^m))=3*2^m by omega]
      ac_rfl
    rw [addr,StableCompactPadProgram.remap_hidden _ _ _ hn]
    change 2+3*n+r.val*2^m+(v.val ^^^ mask.val) = 2+3*n+(r.val*2^m+(v.val ^^^ mask.val))
    omega

/-- A tag is encoded in the same literal format as any constant integer.
The caller can use any fixed global numbering of the eight-entry tables. -/
def entry (T : Template F m h) (tag : Table F → ℕ) (t : Fin T.cells) (j : Fin 4) : Entry :=
  if hj : j.val<3 then sourceEntry (T.source t ⟨j.val,hj⟩) else .literal (tag (T.table t))

theorem entry_fits (T : Template F m h) (tag : Table F → ℕ) (t : Fin T.cells) (j : Fin 4)
    (sites : 2^m < 2^w) : (entry T tag t j).Fits w := by
  by_cases hj : j.val < 3
  · simpa only [entry,dite_eq_left hj] using sourceEntry_fits (T.source t ⟨j.val,hj⟩) sites
  · simp only [entry,dite_eq_right hj,Entry.Fits]

def field (T : Template F m h) (tag : Table F → ℕ) (t : Fin T.cells) (f : Fin 12) : ℕ :=
  let pair : Fin 4 × Fin 3 := finProdFinEquiv.symm f
  (entry T tag t pair.1).word pair.2

theorem field_at (T : Template F m h) (tag : Table F → ℕ) (t : Fin T.cells) (j : Fin 4) (l : Fin 3) :
    field T tag t (finProdFinEquiv (j,l)) = (entry T tag t j).word l := by
  simp only [field,Equiv.symm_apply_apply]

end ThreeFlat.RAM.StableCompactROMEntries

end
end OAI

import OAI.ThreeFlat.RAM.StableCompactROMEntries
import OAI.ThreeFlat.RAM.StableCompactROMProgram
import OAI.ThreeFlat.RAM.StableCompactPadSources

namespace OAI
/-! # A fixed ROM decoder for the physical rows of any shortened compaction template -/

noncomputable section
namespace ThreeFlat.RAM.StableCompactROMAddress

open Computability.VPVNP.BurstRAM BitLayout Routing.StableCompaction Routing.StableCompactRows StableCompactROMEntries
open scoped Fin.CommRing Classical

variable {F : Type*} {m h w k p : ℕ}

/-- Give each coefficient table its field-wide identifier. The same library serves every bank. -/
def library [Fintype F] (B : BitNetwork F p) : HistoryFactors.Library B where
  count := Fintype.card (Table F)
  id i := tableId (B.table i)
  table := globalTable
  correct i := (globalTable_id (B.table i)).symm

@[simp] theorem library_count [Fintype F] (B : BitNetwork F p) :
    (library B).count = (Fintype.card F)^8 := by
  simp [library,Table]

/-- Read-only memory holds twelve words per local template row. -/
def Stores (T : Template F m h) (tag : Table F → ℕ) (base : ℕ) (mem : Memory w) : Prop :=
  ∀ (t : Fin T.cells) (j : Fin 4) (l : Fin 3), mem (base+3*(4*t.val+j.val)+l.val) =
    (((entry T tag t j).word l : ℕ) : Word w)

theorem program_eval (T : Template F m h) (tag : Table F → ℕ) (n base : ℕ) (hn : n ≤ 2^m)
    (i : Fin T.network.cells) (j : Fin 4) (four : 4 < 2^w) (sites : 2^m < 2^w)
    (keyfit : 4*i.val+j.val < 2^w) (romroom : base+12*T.cells ≤ 2^w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin 4 → Word w)
    (key : vs 0 = ((4*i.val+j.val : ℕ) : Word w)) (size : vs 1 = ((2^m : ℕ) : Word w))
    (short : vs 2 = (n : Word w)) (atBase : vs 3 = (base : Word w))
    (stored : Stores T tag base mem) :
    StableCompactROMProgram.program.eval words mem vs =
      if hj : j.val < 3 then
        ((sourceAddress ((restrictRows T.network n).source i ⟨j.val,hj⟩) : ℕ) : Word w)
      else (tag (T.network.table i) : Word w) := by
  obtain ⟨⟨t,v⟩,rfl⟩ := (finProdFinEquiv (m:=T.cells) (n:=2^m)).surjective i
  have flat : (finProdFinEquiv (t,v)).val = t.val*2^m+v.val := by
    change v.val+2^m*t.val = _
    ac_rfl
  rw [flat] at key keyfit
  have romfit : base+3*(4*t.val+j.val)+2 < 2^w := by have := t.isLt; have := j.isLt; omega
  rw [StableCompactROMProgram.program_eval (entry T tag t j) (2^m) n base t.val v.val j hn v.isLt
    four sites keyfit romfit (entry_fits T tag t j sites) words mem vs key size short atBase (stored t j)]
  by_cases hj : j.val < 3
  · simp only [entry,dite_eq_left hj]
    have s := StableCompactPadSources.sourceAddress_restrictRows T.network n hn (finProdFinEquiv (t,v)) ⟨j.val,hj⟩
    rw [Template.network_source] at s
    exact congrArg (fun a : ℕ => (a : Word w)) ((sourceEntry_at _ n hn v).trans s.symm)
  · simp only [entry,dite_eq_right hj,StableCompactROMProgram.Entry.atSite,Template.network_table]

end ThreeFlat.RAM.StableCompactROMAddress

end
end OAI

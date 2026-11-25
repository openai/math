import OAI.ThreeFlat.RAM.StableCompactProgram
import OAI.ThreeFlat.RAM.StableCompactLibrary
import OAI.ThreeFlat.RAM.HistoryFactorLibrary
import OAI.ThreeFlat.Routing.StableCompactRows

namespace OAI
/-! # Native public words for the stable-compaction fibre network -/

namespace ThreeFlat.RAM.StableCompactAddress
open Computability.VPVNP.BurstRAM DescriptorExpr StableCompactProgram BitLayout Routing.StableCompactRows
open scoped Fin.CommRing

variable {F : Type*} {m h w k : ℕ}

/-- A constant, an extracted site bit, a bit in a contiguous input bank,
or a hidden bit translated by a fixed cube mask. -/
def sourceEntry : Source m h → Entry m
  | .constant b => .literal b.toNat
  | .siteBit j => .siteBit j
  | .pin stream => .translated (2 + stream.val*2^m) 0
  | .hidden reg mask => .translated (hiddenBase (2^m+(2^m+2^m)) + reg.val*2^m) mask

theorem sourceEntry_at (s : Source m h) (v : Fin (2^m)) :
    (sourceEntry s).atSite v = sourceAddress (s.physical v) := by
  cases s with
  | constant b => rfl
  | siteBit j => rfl
  | pin j => simp [sourceEntry,Entry.atSite,Source.physical,sourceAddress,Nat.add_assoc]
  | hidden reg mask =>
    simp only [sourceEntry,Entry.atSite,Source.physical,sourceAddress,finProdFinEquiv,
      Equiv.coe_fn_mk,Fin.xor_val_of_two_pow]
    ac_rfl

variable (T : Template F m h)

/-- Compact coefficient table shared by all sites. -/
def library : HistoryFactors.Library T.network where
  count := T.cells
  id i := (finProdFinEquiv.symm i).1
  table := T.table
  correct _ := rfl

def entry (t : Fin T.cells) (j : Fin 4) : Entry m :=
  if hj : j.val < 3 then sourceEntry (T.source t ⟨j.val,hj⟩) else .literal t.val

def metadataProgram : Term w k 1 := StableCompactProgram.program (entry T)
def scalarProgram (code : FieldCode F w) : Term w k 1 := StableCompactLibrary.program T.table code

theorem metadataProgram_binds : (metadataProgram (w:=w) (k:=k) T).binds ≤ 24*T.cells+20 :=
  StableCompactProgram.program_binds _

theorem scalarProgram_binds (code : FieldCode F w) : (scalarProgram (k:=k) T code).binds = 24*T.cells+1 :=
  StableCompactLibrary.program_binds _ _

/-- A single unsigned address in the compact row array selects an actual physical
network source or the same library tag at every site. -/
theorem metadataProgram_eval (i : Fin T.network.cells) (j : Fin 4) (four : 4 < 2^w)
    (sites : 2^m < 2^w) (small : 4*T.cells ≤ 2^w) (fit : 4*i.val+j.val < 2^w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
    (arg : vs 0 = ((4*i.val+j.val : ℕ) : Word w)) :
    (metadataProgram T).eval words mem vs =
      if hj : j.val < 3 then ((sourceAddress (T.network.source i ⟨j.val,hj⟩) : ℕ) : Word w)
      else (((library T).id i).val : Word w) := by
  obtain ⟨⟨t,v⟩,rfl⟩ := (finProdFinEquiv (m:=T.cells) (n:=2^m)).surjective i
  have flat : (finProdFinEquiv (t,v)).val = t.val*2^m+v.val := by
    change v.val+2^m*t.val = _
    ac_rfl
  rw [flat] at arg fit
  rw [metadataProgram,StableCompactProgram.program_eval (entry T) t v j four sites small fit words mem vs arg]
  by_cases hj : j.val < 3
  · simp [entry,hj,sourceEntry_at]
  · simp [entry,hj,library,Entry.atSite]

theorem scalarProgram_eval (code : FieldCode F w) (t : Fin (library T).count)
    (j : Fin 8) (small : 8*T.cells ≤ 2^w) (words : Fin k → Word w) (mem : Memory w)
    (vs : Fin 1 → Word w) (arg : vs 0 = ((8*t.val+j.val : ℕ) : Word w)) :
    (scalarProgram T code).eval words mem vs = code.encode ((library T).table t (bits j.val)) :=
  StableCompactLibrary.program_eval _ _ _ _ small words mem vs arg

end ThreeFlat.RAM.StableCompactAddress

end OAI

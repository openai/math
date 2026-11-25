import OAI.ThreeFlat.Diagonal.CompressorSupplyOrigins
import OAI.ThreeFlat.Diagonal.RefreshPartyAddress
import OAI.ThreeFlat.RAM.HistoryScopeAddress

namespace OAI
/-! # Native bitwise pointer production on actual shrink and refresh stages -/

namespace ThreeFlat.RAM.HistoryGeometryPointer

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open Diagonal Diagonal.CompressorPacking.Native
open scoped Fin.CommRing BigOperators Classical
noncomputable section

variable {W : ℕ}

/-- Register zero points at a compact word holding the actual stageInfoPtr.
The first six arguments give this word, site, incident descriptor, party,
local half number, and bit. The remaining seven locate the selected parent
and private half-width banks. -/
private def shrinkField (S : Graph.Stage) (supply : Bool) (j : Fin 4) : Term W 1 13 :=
  (ShrinkStage.BitOrigins.lookup S supply (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5) (.lit j.val) : Formula 13).compile
    (fun _ => 0)

private def refreshField (m h pad : ℕ) (supply : Bool) (j : Fin 4) : Term W 1 13 :=
  ((RefreshParty.lookup m h pad supply).compile (fun _ => (0 : Fin 1))).instantiate
    ![(.result 0 : Term W 1 13).load,.result 1,.result 2,.result 3,.result 4,.result 5,.literal (j.val:Word W)]

def resolve (field : Fin 4 → Term W 1 13) := (HistoryScopeAddress.program W).instantiate
  ![field 0,field 1,field 2,field 3,(.result 6 : Term W 1 13),.result 7,.result 8,.result 9,.result 10,.result 11,.result 12]

def shrink (W : ℕ) (S : Graph.Stage) (supply : Bool) : Term W 1 13 := resolve (shrinkField S supply)

def refresh (W m h pad : ℕ) (supply : Bool) : Term W 1 13 := resolve (refreshField m h pad supply)

/-- One expansion of the actual four numerical graph fields is enough to
resolve the source. Their result registers are shared across every use in
the scope interpreter. -/
theorem binds (field : Fin 4 → Term W 1 13) :
    (resolve field).binds = (HistoryScopeAddress.program W).binds + ∑ j, (field j).binds := by
  simp [resolve,Fin.sum_univ_succ,Term.binds]

theorem resolves (field : Fin 4 → Term W 1 13) (pub : Fin 1→Word W) (mem : Memory W) (vs : Fin 13→Word W) :
    (resolve field).eval pub mem vs = (HistoryScopeAddress.program W).eval pub mem
      ![(field 0).eval pub mem vs,(field 1).eval pub mem vs,(field 2).eval pub mem vs,(field 3).eval pub mem vs,
        vs 6,vs 7,vs 8,vs 9,vs 10,vs 11,vs 12] := by
  rw [resolve,Term.eval_instantiate]
  apply congrArg _
  funext j
  fin_cases j <;> rfl

/-- The finite degree and coloring in a geometry command determine the
number of native instructions independently of the diagonal word size. -/
theorem shrink_size (W W' : ℕ) (S : Graph.Stage) (supply : Bool) :
    (shrink W S supply).binds=(shrink W' S supply).binds := by
  simp only [shrink,binds,shrinkField,HistoryScopeAddress.program,Formula.binds_compile]

theorem refresh_size (W W' m h pad : ℕ) (supply : Bool) :
    (refresh W m h pad supply).binds=(refresh W' m h pad supply).binds := by
  simp [refresh,binds,refreshField,HistoryScopeAddress.program,Formula.binds_compile,
    Term.binds_instantiate,Term.load,Term.literal,Term.binds,Fin.sum_univ_succ]

end
end ThreeFlat.RAM.HistoryGeometryPointer

end OAI

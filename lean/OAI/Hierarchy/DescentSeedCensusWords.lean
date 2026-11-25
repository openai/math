import OAI.Hierarchy.DescentSeedWideBundleRead
import OAI.Hierarchy.DescentSeedCensusStamp

import OAI.Hierarchy.DescentEpochTagKeys
import OAI.Hierarchy.DescentSeedTokenPlan
import OAI.Hierarchy.DescentSeedTokenNumbers
import OAI.Hierarchy.DescentSeedChoiceBits
import OAI.Hierarchy.DescentSeedOriginalRoleData

namespace OAI
/-! # Numeric primitive roles from the one packed initial census shelf -/
namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSeedRoot DescentInitialHost DescentSixParty DescentPrimitivePalette DescentKernelHistory DescentEpochTagKeys
open DescentPhysicalSplit DescentSIMDLookup Catalyst CorrectionBatch Computability.BorderVNP.Crossing
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat Diagonal
open Computability.VPVNP.RAMMemory (initialMemory)
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {k p R s w : ℕ} (X : Approximation F k p)
local notation "N" => X.network.copyGraph
local notation "H" => Fintype.card (Old X)
local notation "d" => digitsNeeded s
local notation "B" => hubbed N

theorem plan_count : Fintype.card Plan≤4*8^8 := by
  rw [Fintype.card_sigma]
  calc (∑ m : Fin 4,Fintype.card ((Fin m.val→Bool)→Fin 8))
        ≤∑ _ : Fin 4,8^8:=Finset.sum_le_sum (fun m _=>by
            simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
            apply Nat.pow_le_pow_right (by decide)
            exact (Nat.pow_le_pow_right (by decide : 0<2) (show m.val≤3 by omega) : 2^m.val≤2^3))
    _=4*8^8:=by simp


def outside (s : ℕ) : Cell (roleBits s) :=
  ⟨((census s).store (.inr ())).val,((census s).store (.inr ())).isLt.trans (Nat.lt_log2_self ..)⟩

theorem count_at {cw : ℕ} (fit : s<2^cw) (c : (initialGroup X R s).Choice)
    (v : Old X) (j : Fin R) (pat : LocalPattern X v) :
    (((encode d 8).symm (bundles X (selectBit X cw c) ((Fintype.equivFin _) v) j)) (DescentSeedRoot.code X pat)).val=
      (c j (.inl v) pat).val := by
  simp only [bundles,groupedRows,Equiv.symm_apply_apply,cells_at,raw_select X fit,selected]

theorem role_at {cw : ℕ} (fit : s<2^cw) (c : (initialGroup X R s).Choice)
    (v : Old X) (j : Fin R) :
    (entry s (plan X v) (bundles X (selectBit X cw c) ((Fintype.equivFin _) v) j)).val=
      ((census s).store (seedRole X R c j (.inl v))).val := by
  unfold entry
  apply congrArg (fun t : CensusTag s=>((census s).store (.inl t)).val)
  change Sigma.mk _ _=Sigma.mk _ _
  congr 1
  funext pat
  apply Fin.ext
  let tr:=hubbed_trivalent N (physical_output X).1
  let old : LocalPattern X v := (seedPattern B tr.1 (.inl v)).symm pat
  have ok:=(c j (.inl v) old).isLt
  change (((encode d 8).symm (bundles X (selectBit X cw c) ((Fintype.equivFin _) v) j)
    (DescentSeedRoot.code X old)).val%(s+1))=(c j (.inl v) old).val
  exact (congrArg (fun n : ℕ => n % (s+1)) (count_at X fit c v j old)).trans (Nat.mod_eq_of_lt ok)

theorem outside_at (c : (initialGroup X R s).Choice) (j : Fin R) (p : _) :
    (outside s).val=((census s).store (seedRole X R c j (.inr p))).val := rfl


theorem from_header (wide : 16*d≤w) (sel : Select X R s→Bool)
    (p : Row H R (pieces w s)) :
    initialMemory (headerWords X R s w) (base X w sel) (publicWords X+(row H R (pieces w s) p).val)=
      ((data (bundles X sel) p).val:Computability.VPVNP.BurstRAM.Word w) := by
  have pos : 0<pieces w s:=(occupancy w (8*d) (by unfold digitsNeeded;positivity) (by omega)).1
  let mem:=initialMemory (headerWords X R s w) (base X w sel)
  have raw : ∀q : Row H (R*8) (multiplicity w s),
      mem (publicWords X+(row H (R*8) (multiplicity w s) q).val)=((data (cells X sel) q).val:Computability.VPVNP.BurstRAM.Word w):=
    data_at X w sel
  rw [grouped_multiplicity wide] at raw
  exact regroup_read pos (by decide : 0<8) (publicWords X) mem (cells X sel) raw p

end
end Hierarchy.DescentPackedSeed.Primitive

end OAI

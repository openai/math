import OAI.Hierarchy.ProtocolRAMWeightedOrder
import Mathlib.Tactic

namespace OAI
/-! # Counter keys after physical supergroup remapping, including dormant stages -/

namespace Hierarchy.ProtocolRAMTranslatedKey

open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAMReportedPorts TaggedShorterCommonScan TaggedShorterBudget
open scoped Classical Fin.CommRing

variable {N W w menu gb : ℕ}

def counter (menu : ℕ) (g : Fin (2^gb)) (k : Fin (menu+1)) : Fin (2^gb*(menu+1)) :=
  finProdFinEquiv (g,k)

def owner (W gb group : ℕ) : Fin (2^gb) :=
  ⟨(group:Word W).val%(2^gb),Nat.mod_lt _ (Nat.two_pow_pos _)⟩

noncomputable def classOf (rows : Fin N→ProtocolRAMEmit.Row) (w menu : ℕ) (i : Fin N) : Fin (menu+1) :=
  ⟨widthIndex menu ((rows i).width/(w:ℝ)),Nat.lt_succ_of_le (widthIndex_spec menu).1⟩

noncomputable def rowKey (W gb w menu : ℕ) (rows : Fin N→ProtocolRAMEmit.Row) (i : Fin N) :
    Fin (2^gb*(menu+1)) :=
  counter menu (owner W gb (rows i).group) (classOf rows w menu i)

theorem true_owner {g : ℕ} (fit : g<2^gb) (wide : 2^gb≤2^W) :
    (owner W gb g).val=g := by
  change (g:Word W).val%(2^gb)=g
  rw [Fin.val_cast_of_lt (fit.trans_le wide),Nat.mod_eq_of_lt fit]

/-- Irrelevant dormant rows may have a raw group index beyond the word-sized
per-format directory. Their piece count is zero in every wrapped counter bucket. -/
theorem rank_eq {groups γ : ℕ} (rows : Fin N→ProtocolRAMEmit.Row)
    (wide : 2^gb≤2^W) (directory : groups≤2^gb)
    (active : ∀j,0 < pieces rows w j→(rows j).group < groups)
    (order : StrictMono (fun i=>(rows i).link)) (g : Fin groups)
    (i : InGroup rows w menu γ g.val) :
    earlier (rowKey W gb w menu rows) (pieces rows w) i.1.val (rowKey W gb w menu rows i.1)=
      ProtocolRAMPortRanks.«prefix» (slotCount rows w menu γ g.val) (fun j=>(rows j.val).link) i := by
  classical
  let P (j : Fin N) := (rows j).group=g.val ∧ widthIndex menu ((rows j).width/(w:ℝ))=γ
  let mark (j : Fin N) : Fin 2 := if P j then 1 else 0
  have marking (j : Fin N) : mark j=1 ↔ P j := by by_cases h : P j <;> simp [mark,h]
  have ip : P i.1 := i.2
  have own : (owner W gb (rows i.1).group).val=g.val := by rw [ip.1];exact true_owner (g.isLt.trans_le directory) wide
  have equivalent (j : Fin N) (live : 0 < pieces rows w j) :
      rowKey W gb w menu rows j=rowKey W gb w menu rows i.1 ↔ P j := by
    have ownJ := true_owner (gb:=gb) (W:=W) ((active j live).trans_le directory) wide
    change finProdFinEquiv (_,_) = finProdFinEquiv (_,_) ↔ _
    simp only [finProdFinEquiv.injective.eq_iff,Prod.mk.injEq,Fin.ext_iff]
    change (owner W gb (rows j).group).val=(owner W gb (rows i.1).group).val ∧
      widthIndex menu ((rows j).width/(w:ℝ))=widthIndex menu ((rows i.1).width/(w:ℝ)) ↔ _
    rw [ownJ,own,ip.2]
  have bridge := TaggedShorterReportedRank.earlier_prefix mark 1 P marking (pieces rows w)
    (fun j=>(rows j).link) (Equiv.refl _) i (fun _=>order.lt_iff_lt.symm)
  refine Eq.trans ?_ (bridge.trans ?_)
  rotate_left
  · unfold slotCount
    congr 1; apply Subsingleton.elim
  unfold earlier
  refine Finset.sum_congr rfl ?_
  intro j hj
  have bnd : j < N := (Finset.mem_range.mp hj).trans i.1.isLt
  simp only [dite_eq_left bnd]
  by_cases live : 0 < pieces rows w ⟨j,bnd⟩
  · have test : (rowKey W gb w menu rows ⟨j,bnd⟩=rowKey W gb w menu rows i.1) ↔ mark ⟨j,bnd⟩=1 :=
      (equivalent _ live).trans (marking _).symm
    by_cases hit : mark ⟨j,bnd⟩=1
    · simp [test.2 hit,hit]
    · have absent : rowKey W gb w menu rows ⟨j,bnd⟩≠rowKey W gb w menu rows i.1 := fun eqn=>hit (test.mp eqn)
      simp [absent,hit]
  · have zero : pieces rows w ⟨j,bnd⟩=0 := by omega
    simp [zero]

end Hierarchy.ProtocolRAMTranslatedKey

end OAI

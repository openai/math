import OAI.Hierarchy.TaggedWideChronologicalOrder
import OAI.Hierarchy.TaggedWireSpillRowOrder
import OAI.Hierarchy.TaggedWideSparsePrefix
import OAI.Hierarchy.TaggedWideOriginalParts

namespace OAI
/-! # The same chronological commodity prefix on the sparse and dense original boards -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open AdaptiveProbe ProbeStage ProbeStage.CoreBoard ProbeStage.CoreBoard.HistoryRoles
open WireTelescope NamedAperture Tagged.PassiveWindow
open LinearAlgebra.SpectralBooks ChordGraph
open scoped BigOperators Classical

private theorem goods_enum {n K : ℕ} {P G A : Type*} [Fintype P] [Fintype G] [Fintype A]
    (num : Fin n≃P⊕(G⊕A)) (ch : P⊕(G⊕A)→Chord K) (spill : G→ℕ) (g : G) :
    prefixAt (ch ∘ num) ((Sum.elim (fun _:P=>0) (Sum.elim spill (fun _:A=>0))) ∘ num)
      (num.symm (.inr (.inl g)))=
      ∑i : G,if (num.symm (.inr (.inl i))).val<(num.symm (.inr (.inl g))).val ∧
        ch (.inr (.inl i))=ch (.inr (.inl g)) then spill i else 0 := by
  rw [prefixAt,original_prefix]
  let f (s : P⊕(G⊕A)):=if (num.symm s).val<(num.symm (.inr (.inl g))).val ∧ ch s=ch (.inr (.inl g)) then
    (Sum.elim (fun _:P=>0) (Sum.elim spill (fun _:A=>0))) s else 0
  calc
    _ = ∑j : Fin n,f (num j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [f,key]
    _ = ∑s,f s := num.sum_comp f
    _ = _ := by simp [Fintype.sum_sum_type,f]

variable {h W k attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marks : ReportSockets.Marks h W k attempts) (b : CatalogueRows.Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k)
    (sized : attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)=b.boughtRows) {axes : ℕ}
    (axis : Catalysts h W k≃Fin axes)
local notation "d" => 2^W
local notation "N" => Stages h d
local notation "Good" => Goods h W k
local notation "names" => timeRows S π depth marks b order sized axis
local notation "sites" => siteLast h d k+1
local notation "roleKey" => sparseKey S π depth marks b order sized (PurchaseInventory.slotEquiv h N k) axis

theorem old_prefix_on_goods (B : Mount (S:=S) π (siteNumber h d k) b.rows)
    (pad : Chord sites) (spill : Good→ℕ) (i : Good) :
    let L:=B.datedLayout (siteNumber h d k).injective pad
    prefixAt (sorted S π depth marks ∘ names)
      ((Sum.elim (fun _:Catalogue S π depth marks=>0) (Sum.elim spill (fun _:Catalysts h W k=>0))) ∘ names)
      ((names).symm (.inr (.inl i)))=
      prefixAt L.family (L.bits spill) (L.num.symm (.inr (.inl i))) := by
  intro L
  refine (goods_enum names (sorted S π depth marks) spill i).trans ?_
  refine Eq.trans ?_ (goods_enum L.num L.data.original spill i).symm
  apply Finset.sum_congr rfl
  intro j _
  have keys : ((names).symm (.inr (.inl j))).val<((names).symm (.inr (.inl i))).val ↔
      (L.num.symm (.inr (.inl j))).val<(L.num.symm (.inr (.inl i))).val := by
    calc
      _ ↔ (roleKey (names ((names).symm (.inr (.inl j))))).val <
          (roleKey (names ((names).symm (.inr (.inl i))))).val :=
        time_before S π depth marks b order sized axis _ _
      _ ↔ b.rows + PurchaseInventory.slot j < b.rows + PurchaseInventory.slot i := by
        simp only [Equiv.apply_symm_apply, key_goods]; rfl
      _ ↔ _ := by
        change _ ↔ ((SpillRows.chronological h N k b.rows).symm (.inr (.inl j))).val <
          ((SpillRows.chronological h N k b.rows).symm (.inr (.inl i))).val
        rw [SpillRows.original_good, SpillRows.original_good]
  simp only [keys]; rfl

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI

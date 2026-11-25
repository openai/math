import OAI.Hierarchy.TaggedWireEntryOrder

namespace OAI
/-! # The unique positive chronological role of every exposed source bit -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.EntryOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope TaggedPrune Tagged Catalyst AdaptiveProbe HistoryRoles ReportSockets
open scoped Classical BigOperators
variable {h W k w R epochs n : ℕ}
variable (S : PurchaseSampler) (p : Equiv.Perm (Row h)) (depth : ℕ) (marked : Marks h W k epochs)
local notation "Src" => HistoryRoles.Source S p.symm depth marked
local notation "Bucket₀" => Bucket h (2^W) k
local notation "rowChord" => HistoryRoles.sorted S p.symm depth marked

def source : Bucket₀→Src
  | .inl i=>.inr (.inl (.inl (p i)))
  | .inr c=>.inr (.inr c)

def sourceWidth (w R : ℕ) : Src→ℕ
  | .inl _=>0
  | .inr (.inl i)=> initialGoods h (2^W) k w i
  | .inr (.inr _)=> R

theorem source_width (b : Bucket₀) : sourceWidth S p depth marked w R (source S p depth marked b)=capacity w R b := by
  cases b <;> rfl

theorem source_ends (b : Bucket₀) : physicalEnds S p.symm depth marked (source S p depth marked b)=ends p b := by
  rcases b with i|⟨x,j⟩
  · simp [physicalEnds,source,commodityEnds,ends]
  · rfl

theorem source_chord (b : Bucket₀) : rowChord (source S p depth marked b)=chord p b := by
  unfold HistoryRoles.sorted chord
  simp only [source_ends]

theorem positive_source (e : Src) (b : Bucket₀) (pos : 0< sourceWidth S p depth marked w R e) (eq : rowChord e=chord p b) :
    e=source S p depth marked b := by
  rcases e with paid|((x|x)|r)
  · exact (Nat.not_lt_zero _ pos).elim
  · let q : Bucket₀:=.inl (p.symm x)
    have found : source S p depth marked q=.inr (.inl (.inl x)):=by simp [q,source]
    rw [←found] at eq ⊢
    exact congrArg _ (chord_injective p ((source_chord S p depth marked q).symm.trans eq))
  · exact (Nat.not_lt_zero _ pos).elim
  · have found:=chord_injective p ((source_chord S p depth marked (.inr r)).symm.trans eq)
    exact congrArg (source S p depth marked) found

theorem source_aggregate (rows : Fin n≃Src) :
    installedWidths (fun i=> rowChord (rows i)) (fun i=> sourceWidth S p depth marked w R (rows i))=
      exposedWidth p (2^W) k w R := by
  let good:=commodityGraph (d:=2^W) (k:=k) p.symm (siteNumber h (2^W) k)
  let cat:=catalystGraph (siteNumber h (2^W) k)
  have g (i) : good.chordWidth i (initialGoods h (2^W) k w i)=initialGoods h (2^W) k w i • unitChord (rowChord (.inr (.inl i))) :=
    oriented_width good i ((siteNumber h (2^W) k).injective.ne (goods_different p.symm i)) _
  have r (j) : cat.chordWidth j R=R • unitChord (rowChord (.inr (.inr j))) :=
    oriented_width cat j ((siteNumber h (2^W) k).injective.ne (physical_distinct S p.symm depth marked (.inr (.inr j)))) _
  unfold installedWidths
  rw [rows.sum_comp (fun e=> sourceWidth S p depth marked w R e • unitChord (rowChord e))]
  simp only [Fintype.sum_sum_type,sourceWidth,zero_smul,Finset.sum_const_zero,zero_add]
  change _=good.chordWidths (initialGoods h (2^W) k w)+cat.chordWidths (fun _=> R)
  simp only [PortGraph.chordWidths,g,r,Fintype.sum_sum_type]

theorem earlier_source (rows : Fin n≃Src) (b : Bucket₀) :
    let ep:=fun i=> rowChord (rows i)
    let bits:=fun i=> sourceWidth S p depth marked w R (rows i)
    let j:=rows.symm (source S p depth marked b)
    TaggedShorterCommonScan.earlier (NamedAperture.key ep) bits j.val (NamedAperture.key ep j)=0 := by
  intro ep bits j
  apply Finset.sum_eq_zero
  intro t ht
  have smaller:=Finset.mem_range.mp ht
  split
  · rename_i live
    split
    · rename_i same
      by_contra nz
      let i : Fin n:=⟨t,live⟩
      have eq : rowChord (rows i)=chord p b := by
        have ch:ep i=ep j:=(Fintype.equivFin _).injective same
        change rowChord (rows i)=rowChord (rows (rows.symm _)) at ch
        rw [rows.apply_symm_apply,source_chord] at ch
        exact ch
      have unique:=positive_source S p depth marked _ b (Nat.pos_of_ne_zero nz) eq
      have conflict : i=j:=rows.injective (unique.trans (rows.apply_symm_apply _).symm)
      have bad : t=j.val:=congrArg Fin.val conflict
      omega
    · rfl
  · rfl

end Hierarchy.ProbeStage.CoreBoard.EntryOrder
end

end OAI

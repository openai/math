import OAI.Hierarchy.TaggedWireEntrySource
import OAI.Hierarchy.TaggedWireCoreMatrix
import OAI.Hierarchy.TaggedWideDatedRows

namespace OAI
/-! # The named chronological sums on the paid, commodity, and reserve rows -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAM.Calendar WireTelescope TaggedPrune Tagged AdaptiveProbe ReportSockets
open scoped Classical BigOperators
/-- At a prefix of an accepted path only its already paid rows need endpoints.
The same terminal catalogue numbering therefore works before later purchases. -/
theorem named_widths {h W k attempts n edges : ℕ} (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (marks : Marks h W k attempts)
    (order : Fin n ≃ Source S π depth marks) (ordinal : Catalogue S π depth marks ↪ Fin edges)
    (G : PortGraph (Fin (siteLast h (2^W) k+1)) (Fin edges))
    (fixed : Fin edges→ℕ) (stock : Goods h W k→ℕ) (reserve : Catalysts h W k→ℕ)
    (pad : Chord (siteLast h (2^W) k+1))
    (miss : ∀ i, i ∉ Set.range ordinal → fixed i = 0)
    (loops : ∀ i, G.tail i = G.head i → fixed i = 0)
    (live : ∀ e : Catalogue S π depth marks, 0 < fixed (ordinal e) →
      filledChord G pad (ordinal e) = HistoryRoles.sorted S π depth marks (.inl e)) :
    installedWidths (HistoryRoles.sorted S π depth marks ∘ order)
      (Sum.elim (fixed ∘ ordinal) (Sum.elim stock reserve) ∘ order) = G.chordWidths fixed +
      (commodityGraph π (siteNumber h (2^W) k)).chordWidths stock +
      (catalystGraph (siteNumber h (2^W) k)).chordWidths reserve := by
  classical
  let edge := HistoryRoles.sorted S π depth marks
  let qty : Source S π depth marks → ℕ := Sum.elim (fixed ∘ ordinal) (Sum.elim stock reserve)
  let f (i:Fin edges):=fixed i • unitChord (filledChord G pad i)
  have paid : G.chordWidths fixed=∑ e : Catalogue S π depth marks, fixed (ordinal e) • unitChord (edge (.inl e)) := by
    rw [←filled_width G pad fixed loops]
    change (∑i,f i)=_
    calc
      _ = ∑i ∈ Finset.univ.map ordinal,f i := by
        apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro i _ absent
        have off : i∉Set.range ordinal:=by
          rintro ⟨c,rfl⟩
          exact absent (Finset.mem_map.mpr ⟨c,Finset.mem_univ _,rfl⟩)
        simp only [f,miss i off,zero_smul]
      _ = ∑ e : Catalogue S π depth marks, f (ordinal e) := Finset.sum_map ..
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases pos : 0<fixed (ordinal e)
        · simp only [f,live e pos,edge]
        · have zero : fixed (ordinal e)=0:=by omega
          simp only [f,zero,zero_smul]
  let good:=commodityGraph (d:=2^W) (k:=k) π (siteNumber h (2^W) k)
  let cat:=catalystGraph (siteNumber h (2^W) k)
  have goods (i) : good.chordWidth i (stock i)=stock i • unitChord (edge (.inr (.inl i))) :=
    oriented_width good i ((siteNumber h (2^W) k).injective.ne (goods_different π i)) _
  have cash (c) : cat.chordWidth c (reserve c)=reserve c • unitChord (edge (.inr (.inr c))) :=
    oriented_width cat c ((siteNumber h (2^W) k).injective.ne (physical_distinct S π depth marks (.inr (.inr c)))) _
  unfold installedWidths
  change (∑i,qty (order i) • unitChord (edge (order i)))=_
  rw [order.sum_comp (fun e=>qty e • unitChord (edge e)),paid]
  change _=_+good.chordWidths stock+cat.chordWidths reserve
  simp only [qty,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Function.comp_apply,
    PortGraph.chordWidths,goods,cash,add_assoc]

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows

end
end OAI

import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows

namespace OAI
/-! # Successive archive rows bound every earlier site ordinal -/

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows HistoryContraction
noncomputable section
variable {F : Type} [Field F]

theorem State.ArchiveSites.id_lt {d l : ℕ} {A : State d l} (O : A.ArchiveSites) (a : A.Site) :
    O.id a < O.layer.first+O.layer.count := Nat.add_lt_add_left (O.ord a).isLt _

namespace Run

theorem archive_bounds {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) :
    let last := (r.finalArchive h C O p).1
    O.layer.first ≤ last.first ∧ O.layer.first+O.layer.count ≤ last.first+last.count := by
  induction r with
  | done A => exact ⟨le_rfl,le_rfl⟩
  | step R next ih =>
    have z := ih h.1 (tailHistory R next h) (C.2 h.1) p.1.sites p.2
    have cont := p.1.row.contiguous
    exact ⟨(Nat.le_add_right O.layer.first _).trans (cont ▸ z.1), cont ▸
      ((Nat.le_add_right p.1.sites.layer.first _).trans z.2)⟩

end Run
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI

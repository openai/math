import OAI.Hierarchy.ProbeReportSockets
import OAI.Hierarchy.TaggedWideDyadicMenu
import OAI.Hierarchy.ProtocolRAMEmit

namespace OAI
/-! # The occupied dyadic types of the single-scale native probe protocol -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedShorterBudget TaggedShorterSupergroups
open scoped Classical

def typeIndex (W m : ℕ) : Fin (m+1) ↪ ℕ × ℕ where
  toFun i := (W,i.val)
  inj' := fun _ _ eq => Fin.ext (congrArg Prod.snd eq)

def activeType (m : ℕ) (width : ℝ) : Fin (m+1) :=
  ⟨widthIndex m width,Nat.lt_succ_of_le (widthIndex_spec m).1⟩

def typeMenu (κ A : ℝ) (W m k attempts ell : ℕ) (pos : 0<W) (offset : ℕ × ℕ → ℕ) :
    DyadicGeometry κ A (m+1) :=
  DyadicGeometry.of_stages (typeIndex W m) (fun _=>pos) (fun _=>2*copies k attempts+ell) offset

theorem type_address {κ A : ℝ} (W m k attempts ell : ℕ) (pos : 0<W) (offset : ℕ × ℕ → ℕ)
    (x : WideParent κ A) (i : Fin (m+1)) :
    let menu := typeMenu κ A W m k attempts ell pos offset
    2^(menu.supergroup (menu.index i) x) =
      (2:ℕ)^superAddress W (2*copies k attempts) x.h * 2^ell :=
  (address_width W (2*copies k attempts) x.h ell).symm

/-- Every active width class uses the same purchased stage directory,
including at a rounded or a partial final slice. -/
theorem cover {h W k attempts H n : ℕ}
    (dir : Directory (reserved h W (copies k attempts)) H)
    (raw : Fin n → ProtocolRAMEmit.Row) (positive : Fin n → Prop) (w m : ℕ)
    (site : (i : Fin n) → positive i → 0<(raw i).width → StageColumns h (2^W) × Role k attempts)
    (groupRead : ∀ i live width,(raw i).group=(packed dir (site i live width)).1.val) :
    ∀ i,positive i → 0<(raw i).width → ∃ j : Fin (m+1),
      typeIndex W m j=(W,widthIndex m ((raw i).width/(w:ℝ))) ∧ (raw i).group<dir.groups := by
  intro i live width
  refine ⟨activeType m _,rfl,?_⟩
  rw [groupRead i live width]
  exact (packed dir (site i live width)).1.isLt

end Hierarchy.ProbeStage.ReportSockets

end
end OAI

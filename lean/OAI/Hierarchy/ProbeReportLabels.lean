import OAI.Hierarchy.ProbeReportPlacement
import OAI.Hierarchy.ProbeCoreBoard

namespace OAI
/-! # The fixed global site at each physical positive transport address -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open AdaptiveProbe TaggedShorterSupergroups ChainStrip
open scoped Classical

variable {h W k attempts H : ℕ}

def physicalSite (x : StageColumns h (2^W) × Role k attempts) : CoreBoard.Site h (2^W) k :=
  (.inr (.inl x.1),layer x.2)

variable (dir : Directory (reserved h W (copies k attempts)) H)

/-- Fixed even for padding addresses. Every occupied transport lane at this
port belongs to the same site in the global board. -/
def publicSite (p : Fin dir.groups × Fin H) : Option (CoreBoard.Site h (2^W) k) :=
  if covered : ∃ x, packed dir x=p then some (physicalSite covered.choose) else none

@[simp] theorem publicSite_packed (x : StageColumns h (2^W) × Role k attempts) :
    publicSite dir (packed dir x)=some (physicalSite x) := by
  have hit : ∃ y,packed dir y=packed dir x := ⟨x,rfl⟩
  simp only [publicSite,dite_eq_left hit]
  rw [(packed dir).injective hit.choose_spec]

variable (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) (unique : Exclusive marked)

def geometry : Row S π depth marked → Bool → CoreBoard.Site h (2^W) k
  | .inl ((t,p),l),s =>
    let e := CoreBoard.ends (S:=S) π (.inr ((p,t),l))
    if s then e.2 else e.1
  | .inr ⟨a,p⟩,s =>
    (.inr (.inl (stripPlace S π depth (marked a) p (probeEnds depth s))),none)

theorem actual_site (r : Row S π depth marked) (s : Bool) :
    publicSite dir (placed S π depth marked unique dir (r,s))=
      some (geometry S π depth marked r s) := by
  change publicSite dir (packed dir (locate S π depth marked unique (r,s)))=_
  rw [publicSite_packed]
  rcases r with ⟨⟨t,p⟩,l⟩|⟨a,p⟩
  · cases s <;> rfl
  · change some ((Sum.inr (Sum.inl (purchaseSockets S π depth (marked a) (unique a) (p,s))),none) :
        CoreBoard.Site h (2^W) k) = _
    change some ((Sum.inr (Sum.inl (allStripColumns S π depth (marked a) (unique a)
      (p,probeEnds depth s))),none) : CoreBoard.Site h (2^W) k) = _
    rw [allStripColumns_single]
    rfl

end Hierarchy.ProbeStage.ReportSockets

end
end OAI

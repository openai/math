import OAI.Hierarchy.ProbeDisjointStrips

namespace OAI
/-! # Both physical sockets used by each actually acquired endpoint probe -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe ChainStrip
open scoped Classical
noncomputable section

variable {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d→(Fin k×Bool)→Finset (Fin (2^h)))

/-- False names the actual initial inlet; true names the actual terminal outlet.
They are different even for a chain of one tile. -/
def probeEnds (depth : ℕ) : Bool ↪ Columns depth where
  toFun
    | false => inlet depth 0
    | true => outlet depth (Fin.last depth)
  inj' := by
    intro s t eq
    cases s <;> cases t
    · rfl
    · exact False.elim ((probe depth ()).apart eq)
    · exact False.elim ((probe depth ()).apart eq.symm)
    · rfl

/-- Across all signs and groups of one activation, no two endpoint occurrences
use the same physical group/port. Distinct attempts receive distinct public banks. -/
def purchaseSockets (unique : ∀ s c c' r,r∈marked s c → r∈marked s c' → c=c') :
    LiveChains S π depth marked × Bool ↪ StageColumns h d :=
  ((Function.Embedding.refl _).prodMap (probeEnds depth)).trans (allStripColumns S π depth marked unique)

theorem purchaseSockets_in (unique : ∀ s c c' r,r∈marked s c → r∈marked s c' → c=c')
    (path : LiveChains S π depth marked) :
    let p := advisedStage h d π path.1
    let row := liveRow S π depth marked path
    purchaseSockets S π depth marked unique (path,false)=⟨path.1,p.group (row 0),Sum.inl (p.input (row 0))⟩ := by
  exact (allStripColumns_single S π depth marked unique path (inlet depth 0)).trans
    (stripPlace_in S π depth marked path 0)

theorem purchaseSockets_out (unique : ∀ s c c' r,r∈marked s c → r∈marked s c' → c=c')
    (path : LiveChains S π depth marked) :
    let p := advisedStage h d π path.1
    let row := liveRow S π depth marked path
    purchaseSockets S π depth marked unique (path,true)=⟨path.1,p.group (row 0),Sum.inr (p.output (row (Fin.last depth)))⟩ := by
  exact (allStripColumns_single S π depth marked unique path (outlet depth (Fin.last depth))).trans
    (stripPlace_out S π depth marked path (Fin.last depth))

end
end Hierarchy.ProbeStage

end OAI

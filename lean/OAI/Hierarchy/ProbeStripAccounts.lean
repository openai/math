import OAI.Hierarchy.ProbeChainPlacement
import OAI.Hierarchy.ProbeDisjointStrips
import OAI.Hierarchy.ProbeColumnAccounts

namespace OAI
/-! # Exact native commodity and cash accounts of each purchased-strip price menu -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe ChainStrip
open scoped BigOperators Classical
noncomputable section

variable {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))

def stripAddress (path : LiveChains S π depth marked) (i : Axes depth k) :
    Commodity (Fin (2^h)) (permutationFabric h d).shapes.length k :=
  .inr ((liveRow S π depth marked path i.1,path.1),i.2)

theorem actual_strip_prices (path : LiveChains S π depth marked) (M : ℝ)
    (x : Commodity (Fin (2^h)) (permutationFabric h d).shapes.length k → ℝ) :
    prices depth k M (postQuote S π depth marked path x) =
    activePrice (ColumnWires.account (stripAddress S π depth marked path))
      (ColumnWires.printed M (length depth)) x := by
  funext r; exact ColumnWires.quote_active M (length depth) _ x r

/-- Every signed altimeter of any one tile on any selected path retains its own
inventory coordinate in this activation. There are no multiple account writes between
separate selected strips, including when their direction-of-purchase labels differ. -/
def allSignedAddresses (unique : ∀ s c c' r, r∈marked s c → r∈marked s c' → c=c') :
    LiveChains S π depth marked × Axes depth k ↪
    Commodity (Fin (2^h)) (permutationFabric h d).shapes.length k := by
  let stageRows := plainRows S π depth marked unique
  refine ⟨fun q => stripAddress S π depth marked q.1 q.2,?_⟩
  rintro ⟨u,i,j⟩ ⟨v,i',j'⟩ h
  have pair := Sum.inr.inj h
  have ray := congrArg Prod.snd pair
  have r := congrArg (fun p => p.1.1) pair
  have s := congrArg (fun p => p.1.2) pair
  have origin : stageRows (u,i)=stageRows (v,i') := Prod.ext s r
  have ids := stageRows.injective origin
  have a := congrArg Prod.fst ids
  have b := congrArg Prod.snd ids
  dsimp at a b ray; subst v; subst i'; subst j'; rfl

end
end Hierarchy.ProbeStage

end OAI

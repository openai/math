import OAI.Hierarchy.TaggedWireFeedRepartition
import OAI.Hierarchy.TaggedWidePacketHidden
import OAI.Hierarchy.TaggedWireFeedMatrix
import OAI.Hierarchy.TaggedWireSiteBits
import OAI.Hierarchy.TaggedWideHost
import OAI.Hierarchy.TaggedWidePadding

namespace OAI
/-! # Physical feed repartition and the shared middle state of a repaired attempt -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.LedgerStep
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Tagged WireTelescope WireTelescope.CalendarTape
open scoped BigOperators Classical
variable {F V J : Type} [Field F] [Fintype J] [Fintype V] {K : ℕ}
local notation "Net" => BitNetwork F (Fintype.card V)

def siteProduct (first second : Net) : Net :=
  WideHost.localFamily (A:=fun _ : Bool=>V) (fun b=>if b then first else second) (fun _=>Sum.inl)

theorem siteProduct_value (first second : Net) (v : V→Bool) :
    TypedWiring.value (siteProduct first second) v=TypedWiring.value first v*TypedWiring.value second v := by
  rw [siteProduct,WideHost.localFamily_eval,Fintype.prod_bool];rfl

omit [Field F] in
theorem siteProduct_size (first second : Net) :
    let t:=siteProduct first second
    t.cells+t.internal=(first.cells+first.internal)+(second.cells+second.internal) := by
  dsimp only
  rw [siteProduct,WideHost.localFamily_size,Fintype.sum_bool];rfl

variable (G : PortGraph (Fin K) J) (pass : Widths K) (old active held kept spill : J→ℕ)
    (balanced : ∀i,old i+active i=held i+kept i+spill i)
local notation "res" => pass+G.chordWidths held+G.chordWidths kept
local notation "input" => pass+G.chordWidths old+G.chordWidths active

omit [Field F] in
private theorem rebase_read {A T B : Widths K} (eqn : A=T)
    (M : SiteMatrix (State A) (State B) F) (s : Fin K) (x : State T s) (y : State B s) :
    rebase eqn rfl M s x y=M s (cast (congrArg (fun q=>State q s) eqn.symm) x) y := by
  subst T
  rfl

/-- Read the complete two-sided spill-and-carry circuit on the reblocked
old state. This formulation uses the same split as the standalone feed
and the post-attempt clipping operator. -/
theorem feed_of_carry {B : Widths K} (R : SiteMatrix (State (G.chordWidths spill)) (State B) F)
    (s : Fin K) (x : State input s) (y : State (res+B) s) (network : Net) (v : V→Bool)
    (read : TypedWiring.value network v=carry R res s
      (repartition G pass old active held kept spill balanced s x) y) :
    TypedWiring.value network v=matrix G pass old active held kept spill balanced R s x y :=by
  unfold matrix
  rw [rebase_read]
  exact read

private theorem carry_entry {U B C : Widths K} (R : SiteMatrix (State B) (State C) F)
    (s : Fin K) (x : State (U+B) s) (y : State (U+C) s) :
    carry R U s x y =
      (if (splitPortState U C s y).1 = (splitPortState U B s x).1 then 1 else 0) *
        R s (splitPortState U B s x).2 (splitPortState U C s y).2 := by
  unfold carry productTable SiteMatrix.identity
  by_cases same : (splitPortState U C s y).1 = (splitPortState U B s x).1
  · simp only [ite_eq_left same]
  · simp only [ite_eq_right same]

/-- The full feed matrix factors into a physical passive comparator and
the actual heterogeneous routed spill. Its low split is taken *after* the
held/kept repartition of the source word. -/
theorem feed_value {B : Widths K} (R : SiteMatrix (State (G.chordWidths spill)) (State B) F)
    (s : Fin K) (x : State input s) (y : State (res+B) s) (carryGate spillGate : Net) (v : V→Bool)
    (carried : TypedWiring.value carryGate v=
      if (splitPortState res B s y).1=(splitPortState res (G.chordWidths spill) s
        (repartition G pass old active held kept spill balanced s x)).1 then 1 else 0)
    (routed : TypedWiring.value spillGate v=R s (splitPortState res (G.chordWidths spill) s
      (repartition G pass old active held kept spill balanced s x)).2 (splitPortState res B s y).2) :
    TypedWiring.value (siteProduct carryGate spillGate) v=matrix G pass old active held kept spill balanced R s x y := by
  apply feed_of_carry G pass old active held kept spill balanced R s x y
  rw [siteProduct_value,carried,routed,carry_entry]

variable {n : ℕ}
local notation "Branch" => BitNetwork F (Fintype.card (V⊕Fin n))

private def middleEquiv {A : Widths K} (s : Fin K) (place : SiteBit A s ↪ Fin n) :
    State A s ≃ ({i // i ∈ Set.range place} → Bool) :=
  (siteBits A s).trans (Equiv.arrowCongr (Equiv.ofInjective place place.injective) (Equiv.refl Bool))

/-- Encode the temporary local state on its finite original role aperture.
All unused physical mid-date bits are zero. -/
def middle {A : Widths K} (s : Fin K) (place : SiteBit A s↪Fin n) (y : State A s) :=
  WidePadding.pad (fun i=>i∈Set.range place) (middleEquiv s place y)

private def maskedSum (used : Fin n → Prop) (weight : (Fin n → Bool) → F) :=
  ∑ h : Fin n → Bool, if ∀ i, h i=true → used i then weight h else 0

private theorem maskedProduct (used : Fin n → Prop) (mask weight : (Fin n → Bool) → F)
    (yes : ∀ h, (∀ i, h i=true → used i) → mask h = 1)
    (no : ∀ h, ¬(∀ i, h i=true → used i) → mask h = 0) :
    ∑ h : Fin n → Bool, mask h * weight h = maskedSum used weight := by
  unfold maskedSum
  apply Finset.sum_congr rfl
  intro h _
  by_cases accepts : ∀ i, h i=true → used i
  · rw [ite_eq_left accepts, yes h accepts, one_mul]
  · rw [ite_eq_right accepts, no h accepts, zero_mul]

private theorem sumMiddle {Z : Type} [Fintype Z] (used : Fin n → Prop)
    (e : Z ≃ ({i // used i} → Bool)) (embed : Z → Fin n → Bool)
    (widths : ∀ z, embed z = WidePadding.pad used (e z)) (weight : (Fin n → Bool) → F) :
    maskedSum used weight = ∑ z : Z, weight (embed z) := by
  unfold maskedSum
  calc
    _ = ∑ a : {i // used i} → Bool, weight (WidePadding.pad used a) := WidePadding.sum_padded used weight
    _ = ∑ z : Z, weight (WidePadding.pad used (e z)) :=
      (e.sum_comp (fun a => weight (WidePadding.pad used a))).symm
    _ = _ := Finset.sum_congr rfl fun z _ => congrArg weight (widths z).symm

/-- A repaired attempt followed by clipping is a local matrix composition.
The same hidden degree-times-capacity aperture is shared by both physical
circuits. The mask removes every unused bit, so multiplicities are exact. -/
theorem attempt_then_spill {B C A : Widths K} (op : SiteMatrix (State A) (State B) F)
    (clip : SiteMatrix (State B) (State C) F) (s : Fin K) (x : State A s) (y : State C s)
    (place : SiteBit B s↪Fin n) (mask attempt spillNet : Branch) (v : V→Bool)
    (zero : ∀h,TypedWiring.value mask (Sum.elim v h)=if ∀i,h i=true→i∈Set.range place then 1 else 0)
    (run : ∀z,TypedWiring.value attempt (Sum.elim v (middle s place z))=op s x z)
    (settle : ∀z,TypedWiring.value spillNet (Sum.elim v (middle s place z))=clip s z y) :
    TypedWiring.value (ChosenPackets.RowRouting.hiddenEntry mask attempt spillNet) v=SiteMatrix.compose op clip s x y := by
  let used:=fun i=>i∈Set.range place
  let weight:=fun h : Fin n→Bool=>TypedWiring.value attempt (Sum.elim v h)*TypedWiring.value spillNet (Sum.elim v h)
  rw [ChosenPackets.RowRouting.hiddenEntry_sum]
  calc
    _=maskedSum used weight :=
      maskedProduct used (fun h => TypedWiring.value mask (Sum.elim v h)) weight
        (fun h usedBits => (zero h).trans (ite_eq_left usedBits))
        (fun h unusedBit => (zero h).trans (ite_eq_right unusedBit))
    _=∑z:State B s,weight (middle s place z) :=
      sumMiddle (Z:=State B s) used (middleEquiv s place) (middle s place) (fun _ => rfl) weight
    _=SiteMatrix.compose op clip s x y := by
      apply Finset.sum_congr rfl
      intro z _
      dsimp only [weight]
      rw [run,settle,mul_comm]


end Hierarchy.ProbeStage.CoreBoard.LedgerStep

end
end OAI

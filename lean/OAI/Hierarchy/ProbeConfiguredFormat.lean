import OAI.Hierarchy.ProbeFixedCalendarParameters
import OAI.Hierarchy.ProtocolRAMCalendarMenuSizes
import OAI.Hierarchy.ProbeCofinalFormat

namespace OAI
/-! # Mounting the same two finite catalogues and the same copied batch at every height -/

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage StripDirectory
open scoped Classical
noncomputable section
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

/-- All calendar fields affecting the finite menu get their one previously chosen
value, across every native family. Address allocation and original measured port
rows are passed in unchanged. -/
def configured {z raw : ℕ} (s : StripChart.Boards z (2^v.W) k raw v.depth) :=
  { s with
    sampler := v.sampler
    radius := v.radius
    radius_nonneg := Nat.cast_nonneg _
    tolerance := v.toleranceAt
    tolerance_pos := v.geometry.cutoff.1
    minimum := 0
    tree := v.cost.atAttempt
    tree_nonneg := v.cost.nonneg }

/-- Both finite packages are reindexed by the very same stage count as the
initially precomputed protocol. In particular the two physical words for the
selector length and for its maximum multiplicity are constant in the height. -/
theorem catalogue_words {z raw : ℕ} (s : StripChart.Boards z (2^v.W) k raw v.depth) (width : ℕ) :
    let loaded := StripChart.catalogue F (v.configured s) v.cost
    loaded.alphabet=v.menu.alphabet ∧ loaded.maximum=v.menu.maximum ∧
      loaded.copiesAt v.copyScale width=v.menu.copiesAt v.copyScale width := by
  let words (N : ℕ) : ℕ × ℕ × ℕ :=
    let m := menuOfShape F N v.depth k v.positive v.radius v.toleranceAt v.geometry.cutoff.1
    (m.alphabet,m.maximum,m.copiesAt v.copyScale width)
  let count := (permutationFabric z (2^v.W)).shapes.length
  have equal : count=publicStages v.W := fixed_stage_count z v.W
  let actual (N : ℕ) : ℕ × ℕ × ℕ := by
    letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    let a := payloadMenu F N k v.positive v.radius (Nat.cast_nonneg _) v.toleranceAt v.geometry.cutoff.1
      v.cost.payload v.cost.payload_nonneg 0
    let b := purchasedMenu F v.depth k v.positive v.radius (Nat.cast_nonneg _) v.toleranceAt v.geometry.cutoff.1
      v.cost.purchase v.cost.purchase_nonneg 0
    let m := (PacketWidths.ofMenu a).either (PacketWidths.ofMenu b)
    exact (m.alphabet,m.maximum,m.copiesAt v.copyScale width)
  have same : actual count=words (publicStages v.W) := by
    calc
      actual count=actual (publicStages v.W) := congrArg actual equal
      _=words (publicStages v.W) := rfl
  exact ⟨congrArg Prod.fst same,congrArg (fun t=>t.2.1) same,congrArg (fun t=>t.2.2) same⟩

/-- Literal stock-commit RAM width at every clock attempt, including purchased
and payload rows. The ordinary word base used by the instruction is arbitrary. -/
theorem native_copies {z raw : ℕ} (s : StripChart.Boards z (2^v.W) k raw v.depth) (width addr : ℕ) (a : Attempt) :
    let mounted := StripChart.withMenuSizes F (v.configured s) v.cost v.copyScale width
    let f := StripChart.build F mounted a addr
    f.batch.batch.maxWidth=v.menu.maximum ∧ f.histMass=v.menu.copiesAt v.copyScale width := by
  have literal := StripChart.actual_width F (v.configured s) v.cost v.copyScale width addr a
  have matchWords := v.catalogue_words s width
  exact ⟨literal.1.trans matchWords.2.1,literal.2.trans matchWords.2.2⟩

end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI

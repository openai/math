import OAI.Hierarchy.ProbeStockQuotes
import OAI.Hierarchy.ProbePayloadStrip
import OAI.Hierarchy.ProbePublicTimes
import OAI.Hierarchy.ProbeCommodityBounds
import OAI.Hierarchy.ProbeChainPlacement

namespace OAI
/-! # Public prices on the physical inventory and its two strip restrictions -/

noncomputable section
namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped BigOperators Classical

/-- Payloads are quoted at kind zero. Signed altimeters use kind one, the
unit of headroom above M, and the excess-price coefficient at scale W. -/
def publicPhase (N : ℕ) (a M W T s : ℝ) (bits precision : ℕ) : PhasePrice where
  a := a
  M := M
  time := s
  bonus := fun kind => if kind = 0 then 0 else W⁻¹^4/((N:ℝ)*T^2)
  cap := fun kind => if kind = 0 then (N:ℝ) else M+1
  bits := bits
  precision := precision

theorem public_quote_mem {a M W T s : ℝ} (ha : 0<a) (hM : 0≤M) (hs : 0<s)
    (N bits precision kind stock : ℕ) :
    (publicPhase N a M W T s bits precision).quote kind stock ∈
      Set.Icc 0 (if kind = 0 then (N:ℝ) else M+1) := by
  have bonus : 0 ≤ (publicPhase N a M W T s bits precision).bonus kind := by
    dsimp [publicPhase]
    split <;> positivity
  have cap : 0 ≤ (if kind = 0 then (N:ℝ) else M+1) := by split <;> positivity
  exact (offer_spec ha bonus hM hs (show 0≤(stock:ℝ)/bits by positivity) cap).1

/-- A signed stage and axis occupy their own physical lane. All positive
lane numbers nevertheless read the same signed price table. -/
theorem public_lane_quote {z N k : ℕ} (a M W T s : ℝ) (bits precision stock : ℕ)
    (i : Commodity (Fin (2^z)) N k) :
    let phase := publicPhase N a M W T s bits precision
    phase.quote (PurchaseInventory.lane i) stock =
      phase.quote (match i with | .inl _ => 0 | .inr _ => 1) stock := by
  rcases i with p | ⟨⟨p,t⟩,j⟩
  · rfl
  · have pos : 1+t.val*(2*k)+((PurchaseMarks.signedDirection k).symm j).val ≠ 0 := by omega
    simp [PurchaseInventory.lane,PhasePrice.quote,publicPhase]

theorem public_row_quotes {z d k w : ℕ} {a M W T s : ℝ} (ha : 0<a) (hM : 0≤M) (hs : 0<s)
    (bits precision base : ℕ) (mem : Memory w) (p : Fin (2^z)) :
    let N := 2*rounds d+1
    let phase := publicPhase N a M W T s bits precision
    PayloadStrip.rowQuotes (stockQuotes (d:=d) (k:=k) phase 0 1 base mem) p ∈
      Set.Icc 0 (PayloadStrip.ceiling N k M) := by
  dsimp only
  let N := 2*rounds d+1
  let phase := publicPhase N a M W T s bits precision
  let row := PayloadStrip.rowQuotes (stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 base mem) p
  have both (i : PayloadStrip.Quotes N k) : row i ∈ Set.Icc 0 (PayloadStrip.ceiling N k M i) := by
    rcases i with u | j
    · exact public_quote_mem ha hM hs N bits precision 0 _
    · exact public_quote_mem ha hM hs N bits precision 1 _
  exact ⟨fun i => (both i).1,fun i => (both i).2⟩

/-- Translate the stage index in a live chain into the ordinal of its
physical inventory cell. The payload and signed axis are unchanged. -/
def stageQuotes {z d k w : ℕ} (phase : PhasePrice) (payload signed base : ℕ) (mem : Memory w) :
    Commodity (Fin (2^z)) (permutationFabric z d).shapes.length k → ℝ
  | .inl p => stockQuotes (z:=z) (d:=d) (k:=k) phase payload signed base mem (.inl p)
  | .inr ((p,t),j) =>
    stockQuotes (z:=z) (d:=d) (k:=k) phase payload signed base mem (.inr ((p,stageNumber t),j))

theorem public_post_quotes {z d k w : ℕ} {a M W T s : ℝ} (ha : 0<a) (hM : 0≤M) (hs : 0<s)
    (bits precision base : ℕ) (mem : Memory w) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (marked : StageAt z d → (Fin k × Bool) → Finset (Fin (2^z)))
    (path : LiveChains S π depth marked) :
    let phase := publicPhase (2*rounds d+1) a M W T s bits precision
    postQuote S π depth marked path (stageQuotes phase 0 1 base mem) ∈
      Set.Icc 0 (fun _ => M+1) := by
  dsimp only
  let phase := publicPhase (2*rounds d+1) a M W T s bits precision
  have both (i : ChainStrip.Axes depth k) :
      postQuote S π depth marked path (stageQuotes phase 0 1 base mem) i ∈ Set.Icc 0 (M+1) :=
    public_quote_mem ha hM hs _ bits precision 1 _
  exact ⟨fun i => (both i).1,fun i => (both i).2⟩

/-- One rational coefficient works on all word widths, schedule times and
inventory contents. The cardinality of the actual bank cancels the number
of payloads in the normalized squared-price sum. -/
theorem public_quadratic_receipt (N k : ℕ) {M W : ℝ} (hM : 0≤M) (a : ℚ) (ha : 0<a)
    (small : (a:ℝ)*(1+2*N*k:ℕ)*(max (N:ℝ) (M+1))^2≤W⁻¹^4) :
    ∀ (z d w : ℕ), 2*rounds d+1=N →
      ∀ (T s : ℝ), 0<s → ∀ (bits precision base : ℕ) (mem : Memory w),
      let phase := publicPhase N a M W T s bits precision
      let x := stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 base mem
      (a:ℝ)*(∑ i,x i^2)/(2:ℝ)^z ≤ W⁻¹^4 := by
  let A := max (N:ℝ) (M+1)
  let R : ℝ := (1+2*N*k:ℕ)
  intro z d w fixed T s hs bits precision base mem
  let phase := publicPhase N a M W T s bits precision
  let x := stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 base mem
  have pa : (0:ℝ)<a := by exact_mod_cast ha
  have box (i) : x i ∈ Set.Icc 0 A := by
    rcases i with p | j
    · have h := public_quote_mem (a:=(a:ℝ)) (W:=W) (T:=T) pa hM hs N bits precision 0
        (PurchaseInventory.stock base mem (Sum.inl p : Commodity (Fin (2^z)) (2*rounds d+1) k))
      exact ⟨h.1,h.2.trans (le_max_left ..)⟩
    · have h := public_quote_mem (a:=(a:ℝ)) (W:=W) (T:=T) pa hM hs N bits precision 1
        (PurchaseInventory.stock base mem (Sum.inr j : Commodity (Fin (2^z)) (2*rounds d+1) k))
      exact ⟨h.1,h.2.trans (le_max_right ..)⟩
  have count : (Fintype.card (Commodity (Fin (2^z)) (2*rounds d+1) k):ℝ) = (2:ℝ)^z*R := by
    rw [commodity_count,Fintype.card_fin,fixed]
    simp [R]
  have sq : (∑ i,x i^2) ≤ (2:ℝ)^z*R*A^2 := calc
    _ ≤ ∑ _i : Commodity (Fin (2^z)) (2*rounds d+1) k,A^2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (box i).1 (box i).2 2
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,count]
  change (a:ℝ)*(∑ i,x i^2)/(2:ℝ)^z ≤ _
  apply (div_le_iff₀ (show 0<(2:ℝ)^z by positivity)).mpr
  calc
    _ ≤ (a:ℝ)*((2:ℝ)^z*R*A^2) := mul_le_mul_of_nonneg_left sq pa.le
    _ = ((a:ℝ)*R*A^2)*(2:ℝ)^z := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right small (by positivity)


theorem public_quadratic_price (N k : ℕ) {M W : ℝ} (hM : 0≤M) (hW : 0<W) :
    ∃ a : ℚ, 0<a ∧ ∀ (z d w : ℕ), 2*rounds d+1=N →
      ∀ (T s : ℝ), 0<s → ∀ (bits precision base : ℕ) (mem : Memory w),
      let phase := publicPhase N a M W T s bits precision
      let x := stockQuotes (z:=z) (d:=d) (k:=k) phase 0 1 base mem
      (a:ℝ)*(∑ i,x i^2)/(2:ℝ)^z ≤ W⁻¹^4 := by
  let A := max (N:ℝ) (M+1)
  let R : ℝ := (1+2*N*k:ℕ)
  obtain ⟨a,ha,small⟩ := small_quadratic_price (R:=R) (A:=A) hW (Nat.cast_nonneg _)
  exact ⟨a,ha,public_quadratic_receipt N k hM a ha small⟩


end Hierarchy.ProtocolRAM.PurchaseCT

end
end OAI

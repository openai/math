import OAI.Optimization.LinearProgramming.PriceGame.TrialPathGrid
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionComplexity
import OAI.Optimization.LinearProgramming.PriceGame.StatesCommunication
import OAI.Optimization.LinearProgramming.PriceGame.CatalogueGrid

/-! The full wire-cost bound instantiated with the actual catalogue, clearing markets and
self-delimiting rational query format. It holds on inconsistent transcripts as well. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass

def trialMarketSize (N ne : ℕ) : ℕ := ne + 2 * N^2 + 1

/-- Bits required by any signed reduced numerator and positive reduced denominator
in any price produced by a trial on `ne` experts. -/
def trialPriceBits (N ne R D : ℕ) : ℕ :=
  3 + (D.log2+1 + ((R+1).log2+1) + depth N*((8*trialMarketSize N ne+1).log2+1)) + D.log2

private theorem log2_monotone : Monotone Nat.log2 := by
  intro a b h
  simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) h

/-- The wire coefficient is a fixed polynomial in the list length, dimension, bit
length of `R`, and bit length of the common grid, even if the costs are enormous. -/
theorem trialPriceBits_polynomial (N ne R D X : ℕ) (hn : N ≤ X) (he : ne ≤ X)
    (hr : R.size ≤ X) (hd : D.log2 ≤ X) : trialPriceBits N ne R D ≤ 100*(X+1)^3 := by
  have hR : (R+1).log2 ≤ X := by
    have hx := log2_monotone (show R+1 ≤ 2^R.size from Nat.lt_size_self R)
    rw [Nat.log2_two_pow] at hx
    exact hx.trans hr
  have hg : trialMarketSize N ne ≤ X + 2*X^2 + 1 :=
    Nat.add_le_add_right (Nat.add_le_add he (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _))) 1
  have ha : (8*trialMarketSize N ne + 1).log2+1 ≤ 8*(X+2*X^2+1)+2 := by
    have hh := Nat.log2_le_self (8*trialMarketSize N ne + 1)
    omega
  have hDepth : depth N ≤ X+1 := Nat.add_le_add_right ((Nat.log2_le_self N).trans hn) 1
  calc
    trialPriceBits N ne R D ≤ 3+(X+1+(X+1)+(X+1)*(8*(X+2*X^2+1)+2))+X := by
      unfold trialPriceBits
      exact Nat.add_le_add (Nat.add_le_add_left
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right hd 1) (Nat.add_le_add_right hR 1))
          (Nat.mul_le_mul hDepth ha)) 3) hd
    _ ≤ 100*(X+1)^3 := by nlinarith [Nat.zero_le (X^3), Nat.zero_le (X^2), Nat.zero_le X]

theorem runAtArity_grid {N ne : ℕ} (r : ℕ) (hN : 0 < N) (D R : ℕ) (experts : Fin ne → Expert N)
    (raw : RawBox D R experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    let B := Complexity.priceMax R (trialMarketSize N ne) (depth N)
    (execute r R experts (marketSolverAtCommonWeightUnit experts) (depth N) 0 .root
      (fun _ _ => 0) w hw).Guarded
      (fun q => ∀ i, PriceBox D B (q.prices i)) (fun out => OutputBox D B out.val) := by
  let G := trialMarketSize N ne
  have hG : 0 < G := Nat.succ_pos _
  have hc l (hl : l ≤ depth N) : ne + N*2^l + 1 ≤ G := by
    have hc := card_vertices_le N l hN hl
    rw [card_vertices, Nat.mul_comm (2^l) N] at hc
    exact Nat.add_le_add_right (Nat.add_le_add_left hc ne) 1
  exact execute_price_grid r D R G (depth N) hG experts raw hc
    (depth N) 0 (by omega) .root True.intro (fun _ _ => 0) (fun _ hj => by omega) w hw

theorem runReference_grid {N ne : ℕ} (hN : 0 < N) (D R : ℕ) (experts : Fin ne → Expert N)
    (raw : RawBox D R experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    let B := Complexity.priceMax R (trialMarketSize N ne) (depth N)
    (runReference R experts w hw).Guarded
      (fun q => ∀ i, PriceBox D B (q.prices i)) (fun out => OutputBox D B out.val) := by
  dsimp only
  unfold runReference run
  generalize Moment.probes = r
  exact runAtArity_grid r hN D R experts raw w hw

theorem priceBox_ratBits {N ne R D : ℕ} (hd : 0 < D) {q : ℚ}
    (hb : PriceBox D (Complexity.priceMax R (trialMarketSize N ne) (depth N)) q) :
    RAM.ratBits q ≤ trialPriceBits N ne R D := by
  let G := trialMarketSize N ne
  let B := Complexity.priceMax R G (depth N)
  let L := D.log2+1 + ((R+1).log2+1) + depth N*((8*G+1).log2+1)
  have hnum := Moment.rat_num_abs_le_of_den_dvd q B D hd hb.2 hb.1
  have hden := Nat.le_of_dvd hd hb.1
  have hn : q.num.natAbs < 2 ^ L := by
    rw [Nat.mul_comm] at hnum
    exact hnum.trans_lt (Complexity.price_numerator_lt D R G (depth N))
  have hbits : q.num.natAbs.log2 ≤ L := by
    by_cases hz : q.num.natAbs = 0
    · simp [hz]
    · exact ((Nat.log2_lt hz).mpr hn).le
  change 3 + q.num.natAbs.log2 + q.den.log2 ≤ 3 + L + D.log2
  exact Nat.add_le_add (Nat.add_le_add_left hbits _) (log2_monotone hden)

theorem trialPriceBits_mono_experts (N R D : ℕ) :
    Monotone (fun ne => trialPriceBits N ne R D) := by
  intro a b hab
  have hg : (8*(a+2*N^2+1)+1).log2 ≤ (8*(b+2*N^2+1)+1).log2 :=
    log2_monotone (by omega)
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.mul_le_mul_left (depth N) (Nat.add_le_add_right hg 1)) _) 3) D.log2

def ProbeBits {N : ℕ} (B : ℕ) (p : Probe N) : Prop :=
  (∀ i, RAM.ratBits (p.prices i) ≤ B) ∧ ∀ j < p.level, ∀ i, RAM.ratBits (p.history j i) ≤ B

def OutputBits {N ne r l : ℕ} (B : ℕ) (out : Output N ne r l) : Prop :=
  (∀ i, RAM.ratBits (out.prices i) ≤ B) ∧ ∀ p ∈ out.log, ProbeBits B p

private theorem runAtArity_bits_guarded {N ne M : ℕ} (r : ℕ) (hN : 0 < N) (hm : ne ≤ M)
    (D R : ℕ) (hd : 0 < D) (experts : Fin ne → Expert N) (raw : RawBox D R experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    (execute r R experts (marketSolverAtCommonWeightUnit experts) (depth N) 0 .root
      (fun _ _ => 0) w hw).Guarded (PricesBounded (trialPriceBits N M R D))
      (fun out => OutputBits (trialPriceBits N M R D) out.val) := by
  let B := Complexity.priceMax R (trialMarketSize N ne) (depth N)
  have hbit (q) (hq : PriceBox D B q) : RAM.ratBits q ≤ trialPriceBits N M R D :=
    (priceBox_ratBits hd hq).trans (trialPriceBits_mono_experts N R D hm)
  apply Computation.guarded_mono (runAtArity_grid r hN D R experts raw w hw)
  · exact fun q hq i => hbit _ (hq i)
  · intro out h
    refine ⟨fun i => hbit _ (h.1 i), ?_⟩
    intro p hp
    have hh := h.2 p hp
    exact ⟨fun i => hbit _ (hh.1 i), fun j hj i => hbit _ (hh.2 j hj i)⟩

/-- A single arity-independent public bit cap holds for every price field the trial returns,
logs, or sends, with any supplied upper bound on the runtime expert-list size. -/
theorem runReference_bits_guarded {N ne M : ℕ} (hN : 0 < N) (hm : ne ≤ M)
    (D R : ℕ) (hd : 0 < D) (experts : Fin ne → Expert N) (raw : RawBox D R experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    (runReference R experts w hw).Guarded (PricesBounded (trialPriceBits N M R D))
      (fun out => OutputBits (trialPriceBits N M R D) out.val) := by
  unfold runReference run
  generalize Moment.probes = r
  exact runAtArity_bits_guarded r hN hm D R hd experts raw w hw

private theorem runAtArity_wireCost {N ne : ℕ} (r : ℕ) (hN : 0 < N) (D R : ℕ) (hd : 0 < D)
    (experts : Fin ne → Expert N) (raw : RawBox D R experts) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) (reply : List (Query N × Bool) → Query N → Bool)
    (history : List (Query N × Bool)) :
    let p := execute r R experts (marketSolverAtCommonWeightUnit experts) (depth N) 0 .root
      (fun _ _ => 0) w hw
    (p.runMetered (Computation.wireCost Wire.query) reply history).2 ≤
      p.height * (N*(2*trialPriceBits N ne R D+1)+(N.log2+1)+1) := by
  intro p
  let B := Complexity.priceMax R (trialMarketSize N ne) (depth N)
  let Q (q : Query N) := ∀ i, PriceBox D B (q.prices i)
  let P (out : Certified (N:=N) (r:=r) (l:=0) w) := OutputBox D B out.val
  have hg : p.Guarded Q P := runAtArity_grid r hN D R experts raw w hw
  have hgrid : p.AllQueries Q := Computation.Guarded.allQueries (p := p) (P := P) (Q := Q) hg
  have hbits := Computation.allQueries_mono _ (PricesBounded (trialPriceBits N ne R D))
    (fun q h i => priceBox_ratBits hd (h i)) p hgrid
  exact query_bits_le p hbits reply history

/-- Meter the actual emitted bits, including the answer bit, against every history-dependent oracle. -/
theorem runReference_wireCost {N ne : ℕ} (hN : 0 < N) (D R : ℕ) (hd : 0 < D)
    (experts : Fin ne → Expert N) (raw : RawBox D R experts) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) (reply : List (Query N × Bool) → Query N → Bool)
    (history : List (Query N × Bool)) :
    ((runReference R experts w hw).runMetered (Computation.wireCost Wire.query) reply history).2 ≤
      (2*(N+1))^605 * (N*(2*trialPriceBits N ne R D+1)+(N.log2+1)+1) := by
  unfold runReference
  refine Nat.le_trans ?_ (Nat.mul_le_mul_right _
    (run_height_polynomial R experts (marketSolverAtCommonWeightUnit experts) w hw))
  unfold run
  generalize Moment.probes = r
  exact runAtArity_wireCost r hN D R hd experts raw w hw reply history

/-- Every expert retained from any previous trial meets the raw-grid hypothesis. -/
theorem catalogue_rawBox {N R : ℕ} (hist : ℕ → List (Probe N)) (T : ℕ) :
    let xs := Learning.Catalog.entries (fun t => Learning.Pool.batch N R (hist t)) T
    RawBox Learning.Bits.commonDenominator R (fun e : Fin xs.length => xs.get e) := by
  intro xs e i _
  exact Learning.Pool.catalogue_entry_grid hist T _ (List.get_mem xs e) i

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

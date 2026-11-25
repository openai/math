import OAI.Computability.BinPacking.Expanders.SpectralCut
import OAI.ThreeFlat.Concentrator.Greedy

namespace OAI
/-! # The large-set edge bound for the first concentrator pass -/

namespace ThreeFlat.Concentrator

open BinPackingGames.Foundations.PCP
open PoweringWalks SpectralReturn SpectralCut

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D] [DecidableEq V]

/-- If there is no port edge from `A` to `B`, the centered one-step average
of the indicator of `B` equals minus its mean everywhere on `A`.
Its energy lower bound contradicts spectral contraction for large sets. -/
theorem exists_port_between (G : PortGraph V D) {lam : ℝ} (cert : SpectralCertificate G lam)
    (A B : Finset V) (large : lam ^ 2 <
      ((A.card : ℝ) / Fintype.card V) * ((B.card : ℝ) / Fintype.card V)) :
    ∃ x ∈ A, ∃ d : D, (G.rot (x,d)).1 ∈ B := by
  by_contra! hnone
  let b := mean (indicator B)
  have hb : 0 < b := by
    rw [← mean_indicator A, ← mean_indicator B] at large
    have hprod := (sq_nonneg lam).trans_lt large
    exact pos_of_mul_pos_right hprod (mean_nonnegative _ (indicator_nonnegative A))
  have zeroMean : mean (fun x => indicator B x - b) = 0 := by
    rw [mean_sub, mean_const]
    exact sub_self b
  have upper := cert.contraction _ zeroMean
  rw [operator_sub_const, energy_sub_const (indicator B) b, energy_indicator] at upper
  change energy (fun x => averagingOperator G (indicator B) x - b) ≤
    lam ^ 2 * (b - 2 * b * b + b ^ 2) at upper
  have vanish (x : V) (hx : x ∈ A) : averagingOperator G (indicator B) x = 0 := by
    change mean (fun d : D => indicator B (G.rot (x,d)).1) = 0
    have h0 : (fun d : D => indicator B (G.rot (x,d)).1) = fun _ => 0 := by
      funext d
      simp [indicator, hnone x hx d]
    rw [h0, mean_const]
  have lower : mean (indicator A) * b ^ 2 ≤
      energy (fun x => averagingOperator G (indicator B) x - b) := by
    rw [← mean_mul_right]
    apply mean_mono
    intro x
    change indicator A x * b ^ 2 ≤ (averagingOperator G (indicator B) x - b) ^ 2
    by_cases hx : x ∈ A
    · rw [vanish x hx]
      simp [indicator, hx]
    · simpa [indicator, hx] using sq_nonneg (averagingOperator G (indicator B) x - b)
  have variance : b - 2 * b * b + b ^ 2 ≤ b := by nlinarith [sq_nonneg b]
  have bounded := lower.trans (upper.trans (mul_le_mul_of_nonneg_left variance (sq_nonneg lam)))
  rw [← mean_indicator A, ← mean_indicator B] at large
  have contradicts := mul_lt_mul_of_pos_right large hb
  change lam ^ 2 * b < mean (indicator A) * b * b at contradicts
  nlinarith

variable {L R : Type*}

/-- Scan the ports in their prescribed order, omitting destinations outside
the right slots. The order may list parallel incidences. -/
def portCandidates (G : PortGraph V D) (ports : List D) (left : L → V)
    (readRight : V → Option R) (x : L) : List R :=
  ports.filterMap fun d => readRight (G.rot (left x, d)).1

omit [Fintype V] [Fintype D] [Nonempty V] [Nonempty D] [DecidableEq V] in
theorem portCandidates_length (G : PortGraph V D) (ports : List D) (left : L → V)
    (readRight : V → Option R) (x : L) : (portCandidates G ports left readRight x).length ≤ ports.length :=
  List.length_filterMap_le ..

omit [Fintype V] [Nonempty V] [Nonempty D] [DecidableEq V] in
/-- A right slot has at most one contender per return port. Distinct left
slots are distinguished by their destination vertex on reversing that port. -/
theorem portCandidates_contenders_card [Fintype L] [DecidableEq R]
    (G : PortGraph V D) (ports : List D) (left : L ↪ V) (right : R → V)
    (readRight : V → Option R) (sound : ∀ {v r}, readRight v = some r → v = right r)
    (r : R) : (Finset.univ.filter fun x => r ∈ portCandidates G ports left readRight x).card ≤
      Fintype.card D := by
  classical
  let contenders := Finset.univ.filter fun x => r ∈ portCandidates G ports left readRight x
  have back (x : contenders) : ∃ d : D, (G.rot (right r,d)).1 = left x.val := by
    have hm := (Finset.mem_filter.mp x.property).2
    obtain ⟨d, _, hd⟩ := List.mem_filterMap.mp hm
    have dest : (G.rot (left x.val,d)).1 = right r := sound hd
    refine ⟨(G.rot (left x.val,d)).2, ?_⟩
    rw [← dest]
    exact congrArg Prod.fst (G.rot_involutive (left x.val,d))
  let tail (x : contenders) := Classical.choose (back x)
  have hinj : Function.Injective tail := by
    intro x y heq
    apply Subtype.ext
    apply left.injective
    calc
      _ = (G.rot (right r,tail x)).1 := (Classical.choose_spec (back x)).symm
      _ = (G.rot (right r,tail y)).1 := by rw [heq]
      _ = _ := Classical.choose_spec (back y)
  change contenders.card ≤ Fintype.card D
  rw [← Fintype.card_coe]
  exact Fintype.card_le_of_injective tail hinj

/-- Spectral certification and injections of the two slot sets suffice for
the deterministic greedy pass to leave fewer than `threshold` active slots. -/
theorem greedy_missed_card_lt_of_candidate_cover [DecidableEq L] [DecidableEq R]
    (G : PortGraph V D) {lam : ℝ} (cert : SpectralCertificate G lam)
    (ports : List D) (allPorts : ∀ d : D, d ∈ ports)
    (left : L ↪ V) (right : R ↪ V) (readRight : V → Option R)
    (readSlot : ∀ r, readRight (right r) = some r)
    (N : L → List R) (covers : ∀ x r, r ∈ portCandidates G ports left readRight x → r ∈ N x)
    (xs : List L) (F : Finset R) (threshold : ℕ) (slack : xs.length + threshold ≤ F.card)
    (spectral : lam < (threshold : ℝ) / Fintype.card V) :
    (Greedy.run N xs F).missed.card < threshold := by
  apply Greedy.missed_card_lt_of_mixing _ _ _ _ slack
  intro A B _ _ hA hB
  have hsize : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have ratioA : (threshold : ℝ) / Fintype.card V ≤ (A.card : ℝ) / Fintype.card V :=
    div_le_div_of_nonneg_right (by exact_mod_cast hA) hsize.le
  have ratioB : (threshold : ℝ) / Fintype.card V ≤ (B.card : ℝ) / Fintype.card V :=
    div_le_div_of_nonneg_right (by exact_mod_cast hB) hsize.le
  have large : lam ^ 2 < ((A.card : ℝ) / Fintype.card V) * ((B.card : ℝ) / Fintype.card V) := by
    rw [sq]
    calc
      _ ≤ lam * ((B.card : ℝ) / Fintype.card V) :=
        mul_le_mul_of_nonneg_left (spectral.trans_le ratioB).le cert.nonnegative
      _ < _ := mul_lt_mul_of_pos_right (spectral.trans_le ratioA)
        (cert.nonnegative.trans_lt (spectral.trans_le ratioB))
  obtain ⟨v, hv, d, hd⟩ := exists_port_between G cert (A.map left) (B.map right) (by simpa using large)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hv
  obtain ⟨r, hr, he⟩ := Finset.mem_map.mp hd
  refine ⟨x, hx, r, hr, covers x r (List.mem_filterMap.mpr ⟨d, allPorts d, ?_⟩)⟩
  rw [← he, readSlot]

/-- The candidates can in particular be visited in port order. -/
theorem greedy_missed_card_lt_of_certificate [DecidableEq L] [DecidableEq R]
    (G : PortGraph V D) {lam : ℝ} (cert : SpectralCertificate G lam)
    (ports : List D) (allPorts : ∀ d : D, d ∈ ports)
    (left : L ↪ V) (right : R ↪ V) (readRight : V → Option R)
    (readSlot : ∀ r, readRight (right r) = some r)
    (xs : List L) (F : Finset R) (threshold : ℕ) (slack : xs.length + threshold ≤ F.card)
    (spectral : lam < (threshold : ℝ) / Fintype.card V) :
    (Greedy.run (portCandidates G ports left readRight) xs F).missed.card < threshold :=
  greedy_missed_card_lt_of_candidate_cover G cert ports allPorts left right readRight readSlot _
    (fun _ _ h => h) xs F threshold slack spectral

end ThreeFlat.Concentrator

end OAI

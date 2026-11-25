import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryGrid
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecution
import OAI.Optimization.LinearProgramming.PriceGame.TrialMarketDataBounds
import OAI.Optimization.LinearProgramming.PriceGame.Complexity

/-! Bounds every emitted query, returned price, and recorded trial price/history in the
actual recursive execution, allowing arbitrary replies at every designated query. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass

def PriceBox (D U : ℕ) (q : ℚ) : Prop := q.den ∣ D ∧ |q| ≤ (U : ℚ)

theorem PriceBox.mono {D U V : ℕ} {q : ℚ} (hq : PriceBox D U q) (h : U ≤ V) :
    PriceBox D V q := ⟨hq.1, hq.2.trans (by exact_mod_cast h)⟩

private theorem box_zero (D U : ℕ) : PriceBox D U 0 := by simp [PriceBox]

/-- Only earlier depths of the stored price history can be accessed by a pivot. -/
def HistoryBox {N : ℕ} (D U l : ℕ) (history : History N) : Prop :=
  ∀ j < l, ∀ i, PriceBox D U (history j i)

theorem historyBox_push {N D U V l : ℕ} {history : History N} {y : Prices N l}
    (huv : U ≤ V) (hh : HistoryBox D U l history) (hy : ∀ i, PriceBox D V (y i)) :
    HistoryBox D V (l+1) (history.push l y) := by
  intro j hj i
  by_cases he : j = l
  · subst j
    simpa [History.push] using hy i
  · simpa only [History.push, dite_eq_right he] using (hh j (by omega) i).mono huv

theorem median_box {D U n : ℕ} {f : Fin n → ℚ} (hf : ∀ i, PriceBox D U (f i)) :
    PriceBox D U (median f) := by
  unfold median
  split
  · exact hf _
  · exact box_zero _ _

theorem priceMax_mono (R G : ℕ) (hG : 0 < G) : Monotone (Complexity.priceMax R G) := by
  apply monotone_nat_of_le_succ
  intro l
  change Complexity.priceMax R G l ≤ 2*G*(2*(R+1)+Complexity.priceMax R G l)
  have h := Nat.mul_le_mul_right (2*(R+1)+Complexity.priceMax R G l) (show 1 ≤ 2*G by omega)
  rw [one_mul] at h
  omega

def ProbeBox {N : ℕ} (D U : ℕ) (p : Probe N) : Prop :=
  (∀ i, PriceBox D U (p.prices i)) ∧ HistoryBox D U p.level p.history

def OutputBox {N ne r l : ℕ} (D U : ℕ) (out : Output N ne r l) : Prop :=
  (∀ i, PriceBox D U (out.prices i)) ∧ ∀ p ∈ out.log, ProbeBox D U p

def CallBox {N ne r l : ℕ} (D U B : ℕ) (c : Call N ne r l) : Prop :=
  (∀ i, PriceBox D U (c.data.baseline i)) ∧ (∀ i, PriceBox D B (c.data.mapped i)) ∧
    (∀ p ∈ c.child.log, ProbeBox D B p)

/-- All accepted expert inputs lie on the common grid; inactive raw coordinates are ignored. -/
def RawBox {N ne : ℕ} (D R : ℕ) (experts : Fin ne → Expert N) : Prop :=
  ∀ e a, a ∈ (experts e).skeleton.sources → PriceBox D (R+1) ((experts e).raw a)

theorem market_box {N ne : ℕ} (D R G l : ℕ) (experts : Fin ne → Expert N)
    (raw : RawBox D R experts) (history : History N)
    (hh : HistoryBox D (Complexity.priceMax R G l) l history) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) (hG : ne + N*2^l+1 ≤ G) :
    ∀ i, PriceBox D (Complexity.priceMax R G (l+1))
      ((marketSolverAtCommonWeightUnit experts l history w hw).prices i) := by
  intro i
  have hb := marketPrice_den_abs experts l history w hw D (R+1) (Complexity.priceMax R G l) raw hh i
  apply PriceBox.mono (q := (marketSolverAtCommonWeightUnit experts l history w hw).prices i)
    (D := D) (U := 2*(ne+N*2^l+1)*(2*(R+1)+Complexity.priceMax R G l)) hb
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hG)

private theorem nodeLog_box {N ne r l D U B : ℕ} (history : History N)
    (hh : HistoryBox D B l history) (xs : Fin (2*r) → Call N ne r l)
    (hU : U ≤ B) (hc : ∀ j, CallBox D U B (xs j)) :
    ∀ p ∈ nodeLog history xs, ProbeBox D B p := by
  intro p hp
  unfold nodeLog at hp
  obtain ⟨sub, hs, hmem⟩ := List.mem_flatten.mp hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
  split at hmem
  · rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨fun i => ((hc j).1 i).mono hU, hh⟩
    · exact (hc j).2.2 p hmem
  · exact (hc j).2.2 p hmem

theorem executeStep_box_with {N ne r l : ℕ} (extra : Output N ne r (l+1) → Prop) (D R G B : ℕ)
    (experts : Fin ne → Expert N) (raw : RawBox D R experts)
    (history : History N) (hh : HistoryBox D (Complexity.priceMax R G l) l history)
    (path : States.Path (Fin N) (Vertex N l)) (hp : path.pricesSatisfy (PriceBox D B))
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (hG : ne+N*2^l+1 ≤ G)
    (hB : Complexity.priceMax R G (l+1) ≤ B)
    (child : (y : Prices N l) → (cw : Weights ne) → (∀ e, 0 ≤ cw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) cw))
    (hchild : ∀ y, (∀ i, PriceBox D (Complexity.priceMax R G (l+1)) (y i)) →
      ∀ cw hcw, (child y cw hcw).Guarded (fun q => ∀ i, PriceBox D B (q.prices i))
        (fun out => OutputBox D B out.val ∧ extra out.val))
    (j : ℕ) (xs : Fin j → Call N ne r l)
    (hx : ∀ i, CallBox D (Complexity.priceMax R G (l+1)) B (xs i)) :
    (executeStep experts (marketSolverAtCommonWeightUnit experts) w hw history path child j xs).Guarded
      (fun q => ∀ i, PriceBox D B (q.prices i))
      (fun c => CallBox D (Complexity.priceMax R G (l+1)) B c.val ∧ extra c.val.child) := by
  unfold executeStep
  dsimp only
  split
  · let A := marketSolverAtCommonWeightUnit experts l history (incomingLocal experts w xs)
      (incomingLocal_nonneg experts w hw xs)
    have hy := market_box D R G l experts raw history hh (incomingLocal experts w xs)
      (incomingLocal_nonneg experts w hw xs) hG
    refine Computation.guarded_bind (hchild A.prices hy _ _) ?_
    intro out ho
    have hbase i := (hy i).mono hB
    refine Computation.guarded_map
      (States.feedbackAll_guarded (PriceBox D B) path A.prices out.val.prices hp hbase ho.1.1) ?_
    intro labels _
    exact ⟨⟨hy, States.parentPrices_satisfy (PriceBox D B) A.prices out.val.prices hbase ho.1.1, ho.1.2⟩, ho.2⟩
  · rename_i hj
    let y : Prices N l := fun i => median fun a : Fin r =>
      (xs ⟨a.val, lt_of_lt_of_le a.isLt (Nat.le_of_not_gt hj)⟩).data.baseline i
    have hy (i) : PriceBox D (Complexity.priceMax R G (l+1)) (y i) :=
      median_box (fun a => (hx _).1 i)
    refine Computation.guarded_map (hchild y hy _ _) ?_
    intro out ho
    exact ⟨⟨hy, States.parentPrices_satisfy _ y out.val.prices (fun i => (hy i).mono hB) ho.1.1, ho.1.2⟩, ho.2⟩

theorem executeStep_box {N ne r l : ℕ} (D R G B : ℕ)
    (experts : Fin ne → Expert N) (raw : RawBox D R experts)
    (history : History N) (hh : HistoryBox D (Complexity.priceMax R G l) l history)
    (path : States.Path (Fin N) (Vertex N l)) (hp : path.pricesSatisfy (PriceBox D B))
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (hG : ne+N*2^l+1 ≤ G)
    (hB : Complexity.priceMax R G (l+1) ≤ B)
    (child : (y : Prices N l) → (cw : Weights ne) → (∀ e, 0 ≤ cw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) cw))
    (hchild : ∀ y, (∀ i, PriceBox D (Complexity.priceMax R G (l+1)) (y i)) →
      ∀ cw hcw, (child y cw hcw).Guarded (fun q => ∀ i, PriceBox D B (q.prices i))
        (fun out => OutputBox D B out.val))
    (j : ℕ) (xs : Fin j → Call N ne r l)
    (hx : ∀ i, CallBox D (Complexity.priceMax R G (l+1)) B (xs i)) :
    (executeStep experts (marketSolverAtCommonWeightUnit experts) w hw history path child j xs).Guarded
      (fun q => ∀ i, PriceBox D B (q.prices i))
      (fun c => CallBox D (Complexity.priceMax R G (l+1)) B c.val) := by
  have hs := executeStep_box_with (fun _ => True) D R G B experts raw history hh path hp w hw
    hG hB child (fun y hy cw hcw => Computation.guarded_mono (hchild y hy cw hcw)
      (fun _ h => h) (fun _ h => ⟨h,trivial⟩)) j xs hx
  exact Computation.guarded_mono hs (fun _ h => h) (fun _ h => h.1)

/-- The market/input and ancestor estimates propagate over the actual history-dependent
query tree, including every feedback query and each log saved for a later trial. -/
theorem execute_price_grid {N ne : ℕ} (r D R G bottom : ℕ) (hG : 0 < G)
    (experts : Fin ne → Expert N) (raw : RawBox D R experts)
    (hvertices : ∀ l ≤ bottom, ne+N*2^l+1 ≤ G)
    (fuel l : ℕ) (hl : l+fuel ≤ bottom)
    (path : States.Path (Fin N) (Vertex N l))
    (hp : path.pricesSatisfy (PriceBox D (Complexity.priceMax R G bottom)))
    (history : History N) (hh : HistoryBox D (Complexity.priceMax R G l) l history)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    (execute r R experts (marketSolverAtCommonWeightUnit experts) fuel l path history w hw).Guarded
      (fun q => ∀ i, PriceBox D (Complexity.priceMax R G bottom) (q.prices i))
      (fun out => OutputBox D (Complexity.priceMax R G bottom) out.val) := by
  induction fuel generalizing l history w with
  | zero =>
    constructor
    · intro i
      have hupper : R+1 ≤ Complexity.priceMax R G bottom :=
        priceMax_mono R G hG (Nat.zero_le bottom)
      change PriceBox D _ (if weight N l true i ≤ 1 then (R:ℚ)+1 else -((R:ℚ)+1))
      have huv : PriceBox D (R+1) ((R:ℚ)+1) := by
        unfold PriceBox
        constructor
        · rw [← Nat.cast_add_one R]
          simp
        · rw [abs_of_nonneg (by positivity : 0 ≤ (R:ℚ)+1)]
          exact_mod_cast le_rfl
      split
      · exact huv.mono hupper
      · exact (show PriceBox D (R+1) (-((R:ℚ)+1)) by
          simpa only [PriceBox, Rat.neg_den, abs_neg] using huv).mono hupper
    · intro p hmem
      have : p ∈ ([] : List (Probe N)) := hmem
      simp at this
  | succ f ih =>
    rw [execute]
    have hnext : Complexity.priceMax R G (l+1) ≤ Complexity.priceMax R G bottom :=
      priceMax_mono R G hG (by omega)
    refine Computation.guarded_map (runSchedule_guarded _ _ _ _
      (fun _ c => CallBox D (Complexity.priceMax R G (l+1)) (Complexity.priceMax R G bottom) c) ?_) ?_
    · intro j _ xs hx
      apply executeStep_box D R G _ experts raw history hh path hp w hw (hvertices l (by omega)) hnext _ _ j xs hx
      intro y hy cw hcw
      apply ih (l+1) (by omega) (.extend path y (vertexDecidableEq N l))
        ⟨hp, fun i => (hy i).mono hnext⟩ (history.push l y)
        (historyBox_push (priceMax_mono R G hG (Nat.le_succ _)) hh hy) cw hcw
    · intro run hrun
      constructor
      · exact fun i => median_box (fun j => (hrun (finalIndex j)).2.1 i)
      · exact nodeLog_box history (fun j hj i => (hh j hj i).mono
          (priceMax_mono R G hG (by omega))) _ hnext hrun

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI

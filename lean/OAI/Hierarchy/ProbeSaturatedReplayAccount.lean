import OAI.Hierarchy.ProbeCrudeReplay
import OAI.Hierarchy.ProbeRepairReplayAccount

namespace OAI
/-! # Native balance receipt for a saturated inner reserve interval -/

namespace Hierarchy.AdaptiveProbe.OuterBank
open scoped BigOperators Classical
noncomputable section
variable {I X : Type*} [Fintype I] (B : OuterBank I X)

/-- A saturated native reserve replay. `active` is the observed mode-two bit of
each attempted local repair. The saturation evidence supplies one actual complete
slice. Remaining slices only need their charged physical stock/cash transitions. -/
structure SaturatedReplayRows (n w K cap : ℕ) (ρ γ ρBuy reward s : ℝ) (x out : X) where
  m : ℕ
  mesh_pos : 0 < m
  states : ℕ → ℕ → X
  attempts : ℕ → ℕ
  active : ℕ → ℕ → Bool
  sliceId : ℕ
  fuel : ℕ
  selected : sliceId < m
  full : fuel ≤ ((Finset.range (attempts sliceId)).filter fun u => active sliceId u).card
  bought : ℕ
  fee : ℝ
  feeBound : ℝ
  dimension : ℝ
  boxMax : ℝ
  dimension_bound : (Fintype.card I:ℝ) ≤ dimension*n
  cap_pos : 0≤boxMax
  cap_bound : ∀ i, B.box i ≤ boxMax
  entry_fits : ∀ i, B.stock x i ≤ cap*w
  fee_bound : bought*fee ≤ n*feeBound
  fuel_budget : feeBound + dimension*cap*boxMax + ρBuy*reward/8 ≤ fuel*(ρ*γ/(8*K))
  initial_cash : B.cash (states 0 0) ≤ B.cash x + bought*fee
  initial_stock : ∀ i, B.stock (states 0 0) i = B.stock x i/2
  terminal : states m 0=out
  repaired : ∀ j < m, ∀ u<attempts j, active j u=true →
    Nonempty (B.FailedRows n w K cap ρ γ (replayTime s m j) (states j u) (states j (u+1)))
  skipped : ∀ j < m, ∀ u<attempts j, active j u=false →
    B.cash (states j (u+1)) = B.cash (states j u) ∧ B.stock (states j (u+1))=B.stock (states j u)
  retained : ∀ j < m, ∀ i, B.stock (states (j+1) 0) i = min (B.replayFeed m j x (states j (attempts j)) i) (cap*w)
  charged : ∀ j < m, B.cash (states (j+1) 0) ≤ B.cash (states j (attempts j))+
    pairing (bitStock w (spillBits cap w (B.replayFeed m j x (states j (attempts j))))) B.box

theorem SaturatedReplayRows.decrease {n w K cap : ℕ} {ρ γ ρBuy reward s : ℝ} {x out : X}
    (H : B.SaturatedReplayRows n w K cap ρ γ ρBuy reward s x out) (hw : 0<w) (hK : 0<K)
    (hγ : 0<γ) (hρ : 0<ρ) (_hρBuy : 0<ρBuy) (_hr : 0<reward) (_hn : 0<n)
    (ha : 0<B.a) (hb : ∀ i, 0≤B.coefficient i) (hM : 0≤B.M) (hs : 0<s) (s1 : s≤1)
    (box : ∀ i, 0≤B.box i)
    (saturates : ∀ t, 0<t → t≤1 → ∀ i, t*rowSlope B.a (B.coefficient i) B.M (B.box i)≤cap) :
    B.balance w s out ≤ B.balance w s x - (n:ℝ)*ρBuy*reward/8 := by
  let time := replayTime s H.m
  let pre := fun j => H.states j (H.attempts j)
  let value := fun j => B.balance w (time j) (H.states j 0)
  let gain := ρ*γ/(8*K)
  let cnt (j u : ℕ) := ((Finset.range u).filter fun v => H.active j v).card
  have t0 : time 0=s/2 := by simp [time,replayTime]
  have tend : time H.m=s := by dsimp [time,replayTime]; field_simp [Nat.cast_ne_zero.mpr H.mesh_pos.ne']; ring
  have nonnegDt : 0≤ s/(2*(H.m:ℝ)) := by positivity
  have tpos (j : ℕ) : 0<time j := by dsimp [time,replayTime]; positivity
  have mono : Monotone time := by
    intro i j order
    have growth := mul_le_mul_of_nonneg_right (show (i:ℝ)≤j from Nat.cast_le.mpr order) nonnegDt
    dsimp [time,replayTime]; linarith only [growth]
  have tsmall (j : ℕ) (hj : j≤H.m) : time j≤1 := (mono hj).trans (tend.le.trans s1)
  have recovered (j : ℕ) (hj : j<H.m) : B.balance w (time j) (pre j)+(cnt j (H.attempts j):ℝ)*(n*gain) ≤ value j := by
    have prefixBound : ∀ u≤H.attempts j, B.balance w (time j) (H.states j u)+(cnt j u:ℝ)*(n*gain) ≤ value j := by
      intro u; induction u with
      | zero => simp [cnt,value]
      | succ u ih =>
        intro le; have prior := ih (by omega)
        by_cases yes : H.active j u=true
        · obtain ⟨f⟩ := H.repaired j hj u (by omega) yes
          have decrease := FailedRows.decrease B f hw hK hγ ha hb hM (tpos j) box (saturates _ (tpos j) (tsmall j hj.le))
          have step : cnt j (u+1)=cnt j u+1 := by simp [cnt,Finset.range_add_one,Finset.filter_insert,yes,Finset.card_insert_of_notMem]
          rw [step,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
          dsimp [gain] at prior ⊢; linarith [show (n:ℝ)*(ρ*γ/(8*K))=n*ρ*γ/(8*K) by ring]
        · have skip := H.skipped j hj u (by omega) (by simpa using yes)
          have step : cnt j (u+1)=cnt j u := by simp [cnt,Finset.range_add_one,Finset.filter_insert,yes]
          have oldStock : B.units w (H.states j (u+1))=B.units w (H.states j u) := by
            funext i; unfold units; rw [skip.2]
          simpa only [step,balance,skip.1,oldStock] using prior
    exact prefixBound _ le_rfl
  have zero : 0 ≤ potential B.a B.M s B.coefficient B.box (B.units w x) := by
    have low := maximizes B.coefficient B.box (B.units w x) (fun _ => 0) ha hb hM hs
      (fun i => by unfold units; positivity) box (fun i => ⟨le_rfl,box i⟩)
    simpa [pairing,score,rowScore,rise,max_eq_right (neg_nonpos.mpr hM)] using low
  have entry : value 0 ≤ B.balance w s x + H.bought*H.fee := by
    have half := split_start B.coefficient B.box (B.stock x) w hw ha hb hM hs box
    have stock : B.units w (H.states 0 0) = fun i => ((B.stock x i/2:ℕ):ℝ)/w := by funext i; simp only [units,H.initial_stock]
    dsimp only [value,balance]; rw [t0,stock]; change _ ≤ B.cash x+potential B.a B.M s B.coefficient B.box (B.units w x)+_
    change _ ≤ potential B.a B.M s B.coefficient B.box (B.units w x)/2 at half
    linarith only [H.initial_cash,half,zero]
  have feed (j : ℕ) (hj : j<H.m) : value (j+1) + (cnt j (H.attempts j):ℝ)*(n*gain) ≤ value j + reserveCharge w H.m j (B.stock x) B.box := by
    let raw := B.replayFeed H.m j x (pre j)
    have stock : B.units w (H.states (j+1) 0)=bitStock w (clipBits cap w raw) := by funext i; simp only [units,bitStock,clipBits,H.retained j hj,raw,pre]
    have unclipped : bitStock w raw = fun i => B.units w (pre j) i+reserveDelta w H.m j (B.stock x) i := by
      funext i; simp [raw,replayFeed,bitStock,units,reserveDelta,Nat.cast_add,add_div]
    have exactCost := outer_stock_cap (paid:=B.cash (pre j)) cap B.coefficient B.box raw hw ha hb hM (tpos (j+1))
      (saturates _ (tpos _) (tsmall _ (by omega)))
    have next : value (j+1) ≤ B.cash (pre j)+potential B.a B.M (time (j+1)) B.coefficient B.box (bitStock w raw) := by
      rw [exactCost]; change B.cash _+potential _ _ _ _ _ _ ≤ _; rw [stock]
      exact add_le_add (H.charged j hj) le_rfl
    rw [unclipped] at next
    exact crude_slice B.coefficient B.box (B.units w (pre j)) (reserveDelta w H.m j (B.stock x)) (cnt j (H.attempts j))
      ha hb hM (tpos j) (mono (by omega)) box (fun i => by unfold units; positivity)
      (fun i => by dsimp [reserveDelta]; positivity) (recovered j hj) next
  have fit (i : I) : (B.stock x i:ℝ)/w≤cap := by
    apply (div_le_iff₀ (show 0<(w:ℝ) by exact_mod_cast hw)).2
    exact_mod_cast H.entry_fits i
  have done := saturated_replay w H.m n H.fuel H.sliceId (B.stock x) B.box value (fun j => cnt j (H.attempts j))
    H.mesh_pos H.selected H.full H.dimension_bound (Nat.cast_nonneg cap) H.cap_pos (show 0≤gain by dsimp [gain]; positivity)
    (fun i => ⟨box i,H.cap_bound i⟩) fit entry H.fee_bound feed H.fuel_budget
  change B.balance w (time H.m) (H.states H.m 0) ≤ _ at done
  rw [tend,H.terminal] at done; convert done using 1; ring

end
end Hierarchy.AdaptiveProbe.OuterBank

end OAI

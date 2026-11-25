import OAI.Computability.MultitapeWeakETH.WitnessWalkClock

/-! # Acceptance of the polynomially clocked witness traversal -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code
open private data? data_poly present present_poly empty from OAI.Computability.MultitapeWeakETH.WitnessWalk
open private fits stored Meter.count from OAI.Computability.MultitapeWeakETH.WitnessWalkClock

private theorem clip_none (cap : Tally) : clip (cap,none) = none := by
  unfold clip
  cases fits (cap,Meter.count stored (data? none)) <;> rfl

private theorem clip_refines (cap : Tally) (x : Option Store) (st : Store) (ok : clip (cap,x) = some st) :
    x = some st := by
  cases x with
  | none => rw [clip_none] at ok; contradiction
  | some s =>
    unfold clip at ok
    cases p : fits (cap,Meter.count stored (data? (some s)))
    · rw [p,Bool.cond_false] at ok; contradiction
    · simpa only [p,Bool.cond_true] using ok

variable {D : Type} (visit : Visit D) (ctx : D) (cap : Tally)

/-- Read a completed forest; each unfinished frontier and each failed parse rejects. -/
def finish (q : Option Store) : Option (Bits.Word × List Tally) :=
  let st := data? q
  bif present q then bif empty st.1.1 then some (st.1.2,st.2) else none else none

private theorem finish_poly : Poly finish := by
  have emp : Poly empty := (Easy.listCase true (Easy.const false)).poly
  exact Poly.choose present_poly
    (Poly.choose (data_poly.fstCompose.fstCompose.compose emp)
      ((data_poly.fstCompose.sndCompose.pair data_poly.sndCompose).compose Easy.some.poly) (Code.Poly.const none))
    (Code.Poly.const none)

private theorem finish_eq (q : Option Store) (tail : Bits.Word) (labels : List Tally) :
    finish q = some (tail,labels) ↔ q = some (([],tail),labels) := by
  rcases q with _ | ⟨⟨jobs,bits⟩,out⟩
  · simp [finish,present]
  · cases jobs <;> simp [finish,present,empty,data?]

private def limited (q : Option Store) := clip (cap,advance visit ctx q)

private theorem run_limited [Codec D] (fuel : Tally) (st : Option Store) :
    clockRun visit (fuel,(ctx,cap),st) = ((ctx,cap),(limited visit ctx cap)^[fuel.length] st) := by
  unfold clockRun
  generalize fuel.length = n
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih]; rfl

private theorem limited_refines (n : ℕ) (q : Option Store) :
    (limited visit ctx cap)^[n] q = none ∨ (limited visit ctx cap)^[n] q = (advance visit ctx)^[n] q := by
  induction n with
  | zero => exact Or.inr rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    rcases ih with h | h
    · exact Or.inl (by rw [h]; exact clip_none _)
    · rw [h]
      cases hit : limited visit ctx cap ((advance visit ctx)^[n] q) with
      | none => exact Or.inl rfl
      | some x => exact Or.inr (clip_refines cap _ _ hit).symm

private theorem limited_complete (n : ℕ) (q : Option Store)
    (room : ∀ j ≤ n, ∀ st, (advance visit ctx)^[j] q = some st → size st ≤ cap.length) :
    (limited visit ctx cap)^[n] q = (advance visit ctx)^[n] q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih (fun j hj => room j (hj.trans (Nat.le_succ _)))]
    change clip (cap,advance visit ctx _) = _
    cases hit : advance visit ctx ((advance visit ctx)^[n] q) with
    | none => exact clip_none _
    | some st => exact (clip_some _ _).mpr (room _ le_rfl _ (by rw [Function.iterate_succ_apply',hit]))

/-- Physical decoder for a forest with independently supplied unary time and space budgets. -/
def evaluate [Codec D] (q : Tally × ClockState D) := finish (clockRun visit q).2

theorem evaluate_poly [Codec D] (h : Poly visit) : Poly (evaluate visit) :=
  (clockRun_poly visit h).sndCompose.compose finish_poly

/-- A successful physical run is always a syntactic witness of this exact forest,
even if the supplied budgets are too small for other candidates. -/
theorem evaluate_sound [Codec D] (fuel : Tally) (jobs : List Job) (bits tail : Bits.Word) (labels : List Tally)
    (hit : evaluate visit (fuel,(ctx,cap),some ((jobs,bits),[])) = some (tail,labels)) :
    ∃ n ≤ fuel.length, Parses visit ctx jobs bits n tail labels := by
  unfold evaluate at hit
  rw [run_limited] at hit
  have accepted := (finish_eq _ _ _).mp hit
  dsimp only [Prod.snd] at accepted
  rcases limited_refines visit ctx cap fuel.length (some ((jobs,bits),[])) with bad | agree
  · rw [accepted] at bad; contradiction
  · rw [agree] at accepted
    obtain ⟨n,time,l,parse,eq⟩ := run_sound fuel.length jobs bits tail [] labels accepted
    simp only [List.nil_append] at eq
    exact ⟨n,time,eq.symm ▸ parse⟩

/-- Every forest witness passes at each sufficiently large time cutoff, provided
its intermediate frontiers fit the supplied space budget. -/
theorem evaluate_complete [Codec D] (fuel : Tally) {jobs : List Job} {bits tail : Bits.Word} {labels : List Tally}
    {steps : ℕ} (h : Parses visit ctx jobs bits steps tail labels) (time : steps ≤ fuel.length)
    (room : ∀ j ≤ fuel.length, ∀ st, (advance visit ctx)^[j] (some ((jobs,bits),[])) = some st → size st ≤ cap.length) :
    evaluate visit (fuel,(ctx,cap),some ((jobs,bits),[])) = some (tail,labels) := by
  unfold evaluate
  rw [run_limited]
  apply (finish_eq _ _ _).mpr
  dsimp only [Prod.snd]
  rw [limited_complete visit ctx cap _ _ room]
  have actual := Parses.run visit h [] []
  simp only [List.append_nil,List.nil_append] at actual
  have extra (n : ℕ) : (advance visit ctx)^[n] (some (([],tail),labels)) = some (([],tail),labels) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih,advance_done]
  rw [show fuel.length = (fuel.length-steps)+steps by omega,Function.iterate_add_apply,actual,extra]

end OAI.Computability.MultitapeWeakETH.WitnessWalk

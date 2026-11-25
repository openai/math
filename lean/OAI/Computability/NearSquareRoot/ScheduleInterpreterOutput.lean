import OAI.Computability.NearSquareRoot.ScheduleInterpreterRelease

/-!
# Clocked attempt with physical product publication

All internal passes, the binary clock, rollback and the final literal output
copy execute in one transition table. The caller supplies a unary slot budget
and an already fenced trial. The space estimate for the final scan uses the
actual displacement of its frontier marks.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.PublishedAttempt

open IntegerMultiplication TM

abbrev Payload (A : Type) := Fence.Symbol A ⊕ Option Bool
abbrev Symbol (A : Type) := Reset.Cell (Payload A) (Payload A)

private def finished {Q I : Type} : Restart.Control Q I → Bool
  | .inl _ => true
  | .inr _ => false

/-- A successful return is in the output-copy phase. A rejected return is
in the trial phase with all tapes restored. -/
def accepted {Q : Type} : Release.Control Q → Bool
  | .inr _ => true
  | .inl _ => false

variable {A Q I : Type} [Fintype I] [DecidableEq I]

abbrev outputRule (src : I) (decode : A → Option Bool) (bit : Bool → Symbol A) :=
  Copy.rule (Sum.inl src : I ⊕ Bool) Reset.Cell.leftEnd Reset.Cell.origin
    (fun v => Copy.readWork decode v.val) bit

abbrev rule (m : Rule A Q I) (rawBlank : A) (src : I)
    (decode : A → Option Bool) (bit : Bool → Symbol A) :=
  Release.rule (Attempt.rule rawBlank m) finished (outputRule src decode bit)

theorem run (m : Rule A Q I) (rawBlank : A) (rawBit : Bool → A) (src : I)
    (lo hi : I → ℤ) (x : Config A Q I) (hx : Fence.within lo hi x)
    (origin : (x.tape src).pos = 0) (e : List Bool) (T : Bool → Tape (Option Bool))
    (hf : SM.faithful (ScheduleClock.cfg .initialize [] e).stack T)
    (decode : A → Option Bool) (empty : decode rawBlank = none) (digits : ∀ b, decode (rawBit b) = some b)
    (blank : Symbol A) (bit : Bool → Symbol A) (P : List Bool → Prop) (N : ℕ)
    (correct : ∀ {t y}, t < 2^e.length → Trace (advance m) x t y → advance m y = none →
      ∃ z : List Bool, z.length ≤ N ∧ P z ∧ whole rawBlank (z.map rawBit) (y.tape src)) :
    let init := Attempt.entry lo hi x T
    let start := Release.active blank (Restart.start init)
    let M := rule m rawBlank src decode bit
    let B := Schedule.tryFor (tapeTick (Fence.guard m) (fun q => !q.1)) (2^e.length) (Fence.marked lo hi false x)
    let clock := 2*(e.length+1+6*2^e.length)
    let space := Fintype.card (I ⊕ Bool) * (2*((∑ i : I, (hi i+1-lo i).toNat)+2*(e.length+3))+1)
    ∃ t ≤ 7*clock+N+7, ∃ w,
      Trace (advance M) start t w ∧ advance M w = none ∧
      VisitsAtMost M start t (space+1+Fintype.card (Option (I ⊕ Bool))*(8*space+2*N+7)) ∧
      ((B = none ∧ accepted w.pc = false ∧ w.tape = start.tape) ∨
        (B.isSome ∧ accepted w.pc = true ∧ ∃ z, P z ∧ whole blank (z.map bit) (w.tape none))) := by
  let init := Attempt.entry lo hi x T
  let trial := Attempt.rule rawBlank m
  let out := outputRule src decode bit
  let M := Release.rule trial finished out
  let cap := Fintype.card (I ⊕ Bool) * (2*((∑ i : I, (hi i+1-lo i).toNat)+2*(e.length+3))+1)
  obtain ⟨t,ht,w,hist,stop,space,rejected | success⟩ := Attempt.run m rawBlank lo hi x hx e T hf
  · obtain ⟨hb,rfl⟩ := rejected
    obtain ⟨run,halt⟩ := Release.rejected trial finished out blank hist stop rfl
    refine ⟨t,by omega,_,run,halt,?_,.inl ⟨hb,rfl,?_⟩⟩
    · obtain ⟨cells,hc,cover⟩ := Release.work_space trial finished out blank hist space
      exact ⟨cells,hc.trans (Nat.le_add_right ..),cover⟩
    · exact congrArg (fun s => (Copy.beginCopy blank s).tape) (Restart.retry_tapes init)
  · obtain ⟨ym,c,l,r,hb,rfl,range⟩ := success
    obtain ⟨j,hj,y,rfl,hraw,hstop⟩ := Fence.trial_sound m lo hi hx hb
    obtain ⟨z,hlen,hP,word⟩ := correct hj hraw hstop
    let idx : I ⊕ Bool := .inl src
    let y' := Timed.pack (Fence.marked lo hi false y) c
    let u := ((y.tape src).pos - l idx).toNat + (-l idx).toNat + z.length + 2
    have ho : Rollback.origins init idx = 0 := origin
    have bounds := range idx
    change l idx ≤ (x.tape src).pos ∧ (x.tape src).pos ≤ r idx ∧ l idx ≤ (y.tape src).pos ∧
      (y.tape src).pos ≤ r idx ∧ _ at bounds
    obtain ⟨hl₀,hr₀,hl,hr,width⟩ := bounds
    rw [origin] at hl₀ hr₀
    obtain ⟨endCopy,copy,done,product,time⟩ := Copy.release_clocked src (Rollback.snapshot init)
      (Rollback.origins init) l r lo hi y c z rawBlank rawBit decode blank bit empty digits word
      ho hl hr hl₀ hr₀
    change u ≤ 2*(r idx-l idx).toNat+z.length+2 at time
    obtain ⟨run,halt⟩ := Release.accepted trial finished out blank hist stop rfl copy done
    refine ⟨t+(1+u),by omega,_,run,halt,?_,.inr ⟨by rw [hb]; rfl,rfl,z,hP,product⟩⟩
    have bound := Restart.endpoint_radius init y' l r hist space idx
    change (x.tape src).pos - (cap : ℤ) ≤ l idx ∧ r idx ≤ (x.tape src).pos + (cap : ℤ) at bound
    have hu : 2*(1+u)+1 ≤ 8*cap+2*N+7 := by omega
    obtain ⟨cells,hc,cover⟩ := Release.with_copy_space trial finished out blank hist space (1+u)
    exact ⟨cells,hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hu) _),cover⟩

/-- If the tentative output tape starts empty, the entire slot (including
publication on success) costs an absolute constant times its budget. -/
theorem slot (m : Rule A Q I) (rawBlank : A) (rawBit : Bool → A) (src : I)
    (lo hi : I → ℤ) (x : Config A Q I) (hx : Fence.within lo hi x)
    (origin : (x.tape src).pos = 0) (e : List Bool) (T : Bool → Tape (Option Bool))
    (pristine : (x.tape src).absolute = fun _ => rawBlank)
    (hf : SM.faithful (ScheduleClock.cfg .initialize [] e).stack T)
    (decode : A → Option Bool) (empty : decode rawBlank = none) (digits : ∀ b, decode (rawBit b) = some b)
    (blank : Symbol A) (bit : Bool → Symbol A) (P : List Bool → Prop) (N : ℕ)
    (correct : ∀ {t y}, Trace (advance m) x t y → advance m y = none →
      ∃ z : List Bool, z.length ≤ N ∧ P z ∧ whole rawBlank (z.map rawBit) (y.tape src)) :
    let init := Attempt.entry lo hi x T
    let start := Release.active blank (Restart.start init)
    let M := rule m rawBlank src decode bit
    let B := Schedule.tryFor (tapeTick (Fence.guard m) (fun q => !q.1)) (2^e.length) (Fence.marked lo hi false x)
    let space := Fintype.card (I ⊕ Bool) * (2*((∑ i : I, (hi i+1-lo i).toNat)+2*(e.length+3))+1)
    ∃ t ≤ 106*2^e.length, ∃ w,
      Trace (advance M) start t w ∧ advance M w = none ∧
      VisitsAtMost M start t (space+1+Fintype.card (Option (I ⊕ Bool))*(8*space+2*N+7)) ∧
      ((B = none ∧ accepted w.pc = false ∧ w.tape = start.tape) ∨
        (B.isSome ∧ accepted w.pc = true ∧ ∃ z, P z ∧ whole blank (z.map bit) (w.tape none))) := by
  let B := 2^e.length
  have nonblank (b : Bool) : rawBit b ≠ rawBlank := by
    intro he
    have eq := congrArg decode he
    simp [empty,digits] at eq
  obtain ⟨t,ht,w,hist,halt,space,branch⟩ := run m rawBlank rawBit src lo hi x hx origin e T hf
    decode empty digits blank bit P (min N B) (fun hk raw done => by
      obtain ⟨z,hn,hp,whole⟩ := correct raw done
      have hlen := literal_length src raw origin rawBlank rawBit nonblank pristine z whole
      exact ⟨z,le_min hn (by dsimp [B]; omega),hp,whole⟩)
  have he : e.length+1 ≤ B := Nat.lt_two_pow_self
  have h₁ : 1 ≤ B := by omega
  refine ⟨t,?_,w,hist,halt,?_,branch⟩
  · change t ≤ 106*B
    change t ≤ 7*(2*(e.length+1+6*B))+min N B+7 at ht
    omega
  · obtain ⟨cells,hc,cover⟩ := space
    refine ⟨cells,hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _),cover⟩
    omega

end Uniform.PublishedAttempt

end NearSquareRoot
end Computability
end OAI

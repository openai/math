import OAI.Computability.NearSquareRoot.ScheduleStagingPorts

/-! # Erasing and reusing the private digit tapes

The public input head and the callee's own heads share one fenced working bank.
After a confined call their exterior cells still contain the original blank.
Resetting the bank therefore restores every private tape and head exactly,
while all controller shelves stay parked.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingPrivate

open IntegerMultiplication TM CommonAlphabet CommonAlphabet.Pipeline
open StagingPorts (Encoding Bank active marked)

variable {X J I Q : Type}

def working_rule (J I : Type) [Fintype I] (blank : X) :
    Rule (StagingReset.Symbol X) (Option I → Reset.Phase) (Bank J I) :=
  StagingPorts.working.rule (StagingReset.rule (StagingReset.marks blank))

private theorem packed (R : ℕ) (shelf : J → Tape X) (base T : Option I → Tape X)
    (pc : Q) :
    CommonTapes.config StagingPorts.working.index (marked R shelf base)
      (⟨pc, fun i => StagingReset.markedTape R (T i)⟩ : Config _ Q _) =
      ⟨pc, marked R shelf T⟩ := by
  simp only [CommonTapes.config,Config.mk.injEq,true_and]
  change CommonTapes.extend _ _ _ = _
  rw [← Route.put_eq]
  funext j
  cases j <;> rfl

private theorem clean (blank : X) (R : ℕ) :
    Reset.atHead 0 (fun z => StagingReset.symbol R z blank) =
      StagingReset.markedTape R (Tape.loaded blank []) := by
  change Tape.mk _ _ = Tape.mk _ _
  rw [Tape.mk.injEq]
  exact ⟨rfl, funext fun z => by cases z <;> rfl⟩

/-- Reset all private tapes in parallel, preserving every controller tape and
bounding the head positions at every prefix by the marked endpoints. -/
theorem reset [Fintype I] (blank : X) (R : ℕ) (shelf : J → Tape X) (T : Option I → Tape X)
    (hp : ∀ i, -(R : ℤ) ≤ (T i).pos ∧ (T i).pos ≤ R)
    (outside : ∀ i z, z < -(R : ℤ) ∨ (R : ℤ) < z → (T i).absolute z = blank) :
    let m := working_rule J I blank
    let start : Config _ (Option I → Reset.Phase) _ :=
      ⟨fun _ => .seekLeft, marked R shelf T⟩
    let stop : Config _ (Option I → Reset.Phase) _ :=
      ⟨fun _ => .done, marked R shelf (fun _ => Tape.loaded blank [])⟩
    ∃ n ≤ 5*R+3, Trace (advance m) start n stop ∧ advance m stop = none ∧
      ∀ {k c}, k ≤ n → Trace (advance m) start k c →
        (∀ j, c.tape (.inl j) = StagingReset.markedTape R (shelf j)) ∧
        ∀ i, -(R : ℤ) ≤ (c.tape (.inr i)).pos ∧ (c.tape (.inr i)).pos ≤ R := by
  dsimp only
  obtain ⟨n,hn,run,halt,fit⟩ := StagingReset.reset_marked blank R T hp outside
  let e := (StagingPorts.working (J := J) (I := I)).index
  let park := marked R shelf T
  have atStart := packed R shelf T T (fun _ : Option I => Reset.Phase.seekLeft)
  have atEnd := packed R shelf T (fun _ => Tape.loaded blank [])
    (fun _ : Option I => Reset.Phase.done)
  change CommonTapes.config e park (StagingReset.entry _) = _ at atStart
  have endLocal : StagingReset.done (fun (_ : Option I) z => StagingReset.symbol R z blank) =
      ⟨fun _ => .done, fun _ => StagingReset.markedTape R (Tape.loaded blank [])⟩ := by
    simp [StagingReset.done,clean]
  rw [← endLocal] at atEnd
  change CommonTapes.config e park (StagingReset.done (fun (_ : Option I) z =>
    StagingReset.symbol R z blank)) = _ at atEnd
  unfold working_rule
  rw [Route.rule_eq, ← atStart, ← atEnd]
  refine ⟨n,hn,CommonTapes.trace _ _ _ run,?_,fun _ cut => ?_⟩
  · rw [CommonTapes.advance_config,halt]
    rfl
  · obtain ⟨u,hu,rfl⟩ := CommonTapes.reflectTrace _ _ _ cut
    refine ⟨fun j => CommonTapes.extend_off e _ park (.inl j) (by rintro ⟨i,hi⟩; cases hi),
      fun i => ?_⟩
    change _ ≤ (CommonTapes.extend e u.tape park (e i)).pos ∧ (CommonTapes.extend e u.tape park (e i)).pos ≤ _
    rw [CommonTapes.extend_apply]
    exact fit hu i

theorem loaded_outside (xs : List Public.Letter) {R : ℕ} (hl : xs.length ≤ R)
    (z : ℤ) (hz : z < -(R : ℤ) ∨ (R : ℤ) < z) :
    (Tape.loaded none xs).absolute z = none := by
  cases z with
  | negSucc n => rfl
  | ofNat n =>
    change (n : ℤ) < -(R : ℤ) ∨ (R : ℤ) < n at hz
    have h : xs.length ≤ n := by omega
    simp [Tape.absolute,Tape.loaded,List.getElem?_eq_none h]

/-- A finite cell bound confines the private heads and leaves all exterior
symbols blank. The input length accounts for preloaded cells even if the
callee never visits them. -/
theorem active_clean (e : Encoding X) (m : Rule Public.Letter Q (Index I)) (q : Q)
    (x y : List Bool) {t S R : ℕ} {finish : Config _ Q (Index I)}
    (run : Trace (advance m) ⟨q,publicLoad x y⟩ t finish)
    (space : VisitsAtMost m ⟨q,publicLoad x y⟩ t S) (hS : S ≤ R)
    (hlen : (rawWord x y).length ≤ R) :
    (∀ i, -(R : ℤ) ≤ (active e finish.tape i).pos ∧ (active e finish.tape i).pos ≤ R) ∧
    ∀ i z, z < -(R : ℤ) ∨ (R : ℤ) < z →
      (active e finish.tape i).absolute z = e.embed none := by
  have fits {k : ℕ} {v : Config _ Q (Index I)} (hk : k ≤ t)
      (cut : Trace (advance m) ⟨q,publicLoad x y⟩ k v) (j : Index I) :
      -(R : ℤ) ≤ (v.tape j).pos ∧ (v.tape j).pos ≤ R := by
    have h := Uniform.radius_of_visits space hk cut j
    have head : (publicLoad x y j).pos = 0 := by rcases j with (b|j); cases b <;> rfl; rfl
    change (publicLoad x y j).pos-_ ≤ _ ∧ _ ≤ (publicLoad x y j).pos+_ at h
    rw [head] at h
    omega
  have exterior (j : Index I) (z : ℤ) (hz : z < -(R : ℤ) ∨ (R : ℤ) < z) :
      (finish.tape j).absolute z = none := by
    rw [StagingReset.outside_eq_of_confined m R run fits j z hz]
    rcases j with (b|j)
    · cases b
      · exact loaded_outside _ hlen z hz
      · exact loaded_outside [] (Nat.zero_le _) z hz
    · exact loaded_outside [] (Nat.zero_le _) z hz
  refine ⟨fun i => ?_,fun i z hz => ?_⟩
  · cases i with
    | none => simpa [active,StagingPorts.imageTape] using fits le_rfl run (.inl false)
    | some i => simpa [active,StagingPorts.imageTape] using fits le_rfl run (.inr i)
  · cases i with
    | none => simpa [active,StagingPorts.imageTape,Tape.absolute] using
        congrArg e.embed (exterior (.inl false) z hz)
    | some i => simpa [active,StagingPorts.imageTape,Tape.absolute] using
        congrArg e.embed (exterior (.inr i) z hz)

end StagingPrivate

end NearSquareRoot
end Computability
end OAI

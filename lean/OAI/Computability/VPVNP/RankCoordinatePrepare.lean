import OAI.Computability.VPVNP.RankCoordinatePrepareCost

/-! # Preparing the actual two Cramer roots from live evaluator inputs

A fixed table clones the shared templates, computes the current original row
and replacement ordinal, converts the label when required, and writes the
four varying words to the numerator. The operation mode is fixed in control.
Both modes can start from the same advised stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.Prepare

open RAMTape UniversalCountStack BurstRAM NativeReader SliceArithmetic
open RadicalCertificate.MonomialIndex

variable {D K T : Type} [DecidableEq D] [DecidableEq K] [DecidableEq T]

/-- Source ports for the numerator’s replacement-row ordinal and three target inputs. Dynamic
registers five and seven supply the ordinal and monomial. The other ports supply the label
mark and operation-specific scale. -/
def sources (b : Bool) := ArgumentStage.sources (dyn (D := D) (K := K) (T := T))
  (workPort (unary .number)) (scale b)

private def isRoot : Ports D K T → Bool
  | .aux (.inr (.inl (.inl _))) => true
  | _ => false

private def isScratch : Ports D K T → Bool
  | .aux (.inr (.inr _)) => true
  | _ => false

omit [DecidableEq D] [DecidableEq K] [DecidableEq T] in
private theorem source_flags (b : Bool) (f : ArgumentStage.Field) :
    isRoot (sources (D := D) (K := K) (T := T) b f) = false ∧ isScratch (sources b f : Ports D K T) = false := by
  rcases f with ⟨⟩|i
  · exact ⟨rfl,rfl⟩
  · fin_cases i <;> exact ⟨rfl,rfl⟩

omit [DecidableEq D] [DecidableEq K] [DecidableEq T] in
private theorem apart (target : Fin 3 ↪ K) (b : Bool) (f g : ArgumentStage.Field) :
    sources (D := D) (K := K) (T := T) b f ≠ ArgumentStage.workPort (ArgumentStage.destination root target g) := by
  intro eq
  have h := congrArg isRoot eq
  rw [(source_flags b f).1] at h
  exact Bool.noConfusion (show false = true from h)

omit [DecidableEq D] [DecidableEq K] [DecidableEq T] in
private theorem separate (b : Bool) (f : ArgumentStage.Field) :
    sources (D := D) (K := K) (T := T) b f ≠ ArgumentStage.workPort scratch := by
  intro eq
  have h := congrArg isScratch eq
  rw [(source_flags b f).2] at h
  exact Bool.noConfusion (show false = true from h)

omit [DecidableEq D] [DecidableEq K] [DecidableEq T] in
private theorem unused (target : Fin 3 ↪ K) (f : ArgumentStage.Field) :
    ArgumentStage.destination (root (D := D) (T := T)) target f ≠ scratch := Sum.inl_ne_inr

/-- Load the root templates, compute the replacement row from the next basis ordinal and the
target monomial from the current one, and install those words with the operation’s label
mark and scale. -/
noncomputable def machine [Fintype (Parts D K T)] (selector : FiniteRoutine (OrdinalRead.Port T))
    (target : Fin 3 ↪ K) (b : Bool) : FiniteRoutine (Ports D K T) :=
  (((load.followedBy ((Dynamic.machine selector).onPorts dynPort)).followedBy (labelCall b))).followedBy
    (ArgumentStage.machine root target (sources b) scratch)

omit [DecidableEq D] [DecidableEq K] [DecidableEq T] in
private theorem dormant_regs (w a b c d e f g h : ℕ) :
    dormant (Dynamic.regs (w := w) a b c d e f g h) = Dynamic.regs 0 0 c d e f g h := by
  funext i; fin_cases i <;> rfl

variable [Fintype (Parts D K T)] {F : Type} [Field F] [DecidableEq F] {p e x y z w v M A S B : ℕ}

set_option maxHeartbeats 1500000 in
/-- Complete dynamic preparation. The live ordinal words and unary label are
the only request-dependent input. The prepared roots contain the selected
replacement row and the original powered-target monomial. -/
theorem machine_bounded (W : Matrix (Fin x) (Fin z) F) (Y : Matrix (Fin y) (Fin z) F)
    (cur next : Fin (suffixDimension W Y)) (label : ℕ) (b : Bool) (scaleValue : Bool → ℕ)
    (c : Vector p e) (r : ℕ) (den : Stacks D) (raw : Stacks K) (target : Fin 3 ↪ K)
    (selector : FiniteRoutine (OrdinalRead.Port T)) {ready : Stacks T → Prop}
    (hsel : OrdinalRead.CorrectSpace selector (greedyRowIndex (appendRows W Y)) w B S ready)
    (hw : w ≤ S) (fits : x+y < 2^w) (hready : ∀ s, ready s → ∀ k, (s k).length ≤ S)
    (side : Stacks T) (hs : ready side) (labelFit : label+1 < 2^w)
    (old : List Bool) (oldSize : old.length ≤ w) (rawSize : ∀ i, (raw (target i)).length ≤ w) :
    let rootData := RootInit.template c r w v den (Replacement.workBank w old (Submatrix.workBank [] [] raw))
    let dynamicData := Dynamic.bank side (Dynamic.regs (w := w) 0 0 (rankQuery W) x 0 0 0 0)
    let unaryData := UnaryWord.store [] [] (digits w 0) [] []
    let advised := advice rootData dynamicData unaryData (fun mode => digits w (scaleValue mode))
    (∀ i, (rootData i).length ≤ M) → (∀ i, (dynamicData i).length ≤ M) → (∀ i, (unaryData i).length ≤ M) →
    (∀ k, (state (List.replicate label true) (digits w cur) (digits w next) [] advised (fun _ : Work D K T => []) k).length ≤ A) →
    ∃ t ≤ time (Parts D K T) b M B label w, ∃ out : Stacks (Work D K T), out scratch = [] ∧
      (∀ i, out (root i) = RootInit.template c r w v den (Replacement.workBank w (digits w (combinedOrdinal W Y next))
        (Submatrix.workBank [] [] (installStacks target raw (TargetRead.words w (suffixBasisIndex W Y cur)
          (scaleValue b) (if b then 0 else label+1))))) i) ∧
      (machine selector target b).BoundedRun (peak (Parts D K T) M A S label w) t
        (state (List.replicate label true) (digits w cur) (digits w next) [] advised (fun _ : Work D K T => []))
        (state (List.replicate label true) (digits w cur) (digits w next) [] advised out) := by
  intro roots dynamicData unaryData adv rootFit dynFit unFit start
  let labelBits := List.replicate label true
  let cap := baseCap (Parts D K T) M A S label w
  let full := peak (Parts D K T) M A S label w
  have loadRoom : A+RootInit.loadClock (Parts D K T) M ≤ cap := le_max_left ..
  have dynRoom : S+Dynamic.overhead w ≤ cap := (le_max_left ..).trans (le_max_right ..)
  have labelRoom : max label w+LabelWord.clock label w ≤ cap := (le_max_right ..).trans (le_max_right ..)
  have finishRoom : cap ≤ full := Nat.le_add_right ..
  obtain ⟨u,hu,loaded⟩ := load_bounded labelBits (digits w cur) (digits w next) roots dynamicData unaryData
    (fun mode => digits w (scaleValue mode)) A M rootFit dynFit unFit start
  let ri := combinedOrdinal W Y cur
  let rj := combinedOrdinal W Y next
  let row := greedyRowIndex (appendRows W Y) ri
  let mono := suffixBasisIndex W Y cur
  let before := Dynamic.regs (w := w) cur next (rankQuery W) x 0 0 0 0
  let after := Dynamic.regs (w := w) cur next (rankQuery W) x ri rj row mono
  obtain ⟨u₁,hu₁,side',_,rawRun⟩ := Dynamic.machine_bounded W Y cur next selector hsel hw fits hready side hs
  have stage₀ := loaded.enlarge loadRoom
  have dh : dormant before = Dynamic.regs (w := w) 0 0 (rankQuery W) x 0 0 0 0 := dormant_regs ..
  have dh' : dormant after = Dynamic.regs (w := w) 0 0 (rankQuery W) x ri rj row mono := dormant_regs ..
  have stage₁ := dynamic_bounded selector side side' before after rfl rfl roots unaryData labelBits adv
    (rawRun.enlarge dynRoom) (by rw [dh]; exact stage₀.final_cap)
  rw [dh,dh'] at stage₁
  let computed := Dynamic.bank side' (Dynamic.regs (w := w) 0 0 (rankQuery W) x ri rj row mono)
  let mark := if b then 0 else label+1
  let unaryOut := UnaryWord.store [] [] (digits w mark) [] []
  have stage₂ := label_bounded b labelFit roots computed (digits w cur) (digits w next) adv stage₁.final_cap labelRoom
  let installed := work roots computed unaryOut
  let result := TargetRead.words w mono (scaleValue b) mark
  let values := Sum.elim (fun _ : Unit => digits w rj) result
  have hvalues : ∀ f, state labelBits (digits w cur) (digits w next) [] adv installed (sources b f) = values f := by
    apply ArgumentStage.source_words dyn (workPort (unary .number)) (scale b) labelBits _ _ [] adv installed side'
      0 0 (rankQuery W) x ri rj row mono mark (scaleValue b) (fun _ => rfl) rfl rfl
  have tiny (f : ArgumentStage.Field) : (values f).length ≤ w := by
    rcases f with ⟨⟩|i
    · simp [values]
    · fin_cases i <;> simp [values,result,TargetRead.words]
  have oldBound (f : ArgumentStage.Field) : (installed (ArgumentStage.destination root target f)).length ≤ w := by
    rcases f with ⟨⟩|i
    · exact oldSize
    · exact rawSize i
  obtain ⟨u₃,hu₃,st⟩ := ArgumentStage.machine_bounded root target (sources b) scratch w cap labelBits (digits w cur)
    (digits w next) [] adv installed values (apart target b) (separate b) (unused target) rfl hvalues tiny oldBound stage₂.final_cap
  let out := installStacks (ArgumentStage.destination root target) installed values
  have hs' : out scratch = [] := installStacks_outside installed values (unused target)
  have hhost (i : Root D K) := ArgumentStage.host_after c r w v root target den raw old (digits w rj) result installed
    (fun _ => rfl) i
  have first := ((stage₀.followedBy stage₁).followedBy stage₂).enlarge finishRoom
  exact ⟨u+u₁+labelTime b label w+u₃,Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hu hu₁) _) hu₃,out,hs',hhost,first.followedBy st⟩

end RankQuery.Stack.Coordinate.Prepare

end VPVNP
end Computability
end OAI

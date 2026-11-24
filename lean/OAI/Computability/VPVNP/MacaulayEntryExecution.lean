import OAI.Computability.VPVNP.MacaulayEntryPhase

/-! # Execution of the shifted and powered coefficient arms

The two ordinal scans run on the source and column words issued by the row
decoder. The divisibility and equality flags below come from the actual scans
and determine the subsequent bit-stack computation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.Arms

open BurstRAM RAMTape UniversalCountStack MacaulayRowDispatch RadicalCertificate.MonomialIndex

variable {K : Type} [DecidableEq K] {w A S : ℕ}

omit [DecidableEq K] in
private theorem start_room (rs : Reg → Word w) (d : Bool → PairCall.Inputs) (v : Bool → List Bool)
    (aux : Stacks K) (pre : Preload (w := w) A d v aux) :
    ∀ z, (frame rs [] (storage w d blank blank v aux) z).length ≤ A :=
  frame_bound rs [] d blank blank v aux pre.words (by simp) pre.arity (by simp [blank]) (by simp [blank]) pre.scalars pre.payload

/-- Complete shifted-monomial matrix read. The chosen leaf receives exactly
the coordinatewise difference and is skipped when the multiplier fails to
divide the column. -/
theorem equation_execution (rs : Reg → Word w) (data : Bool → PairCall.Inputs) (constants : Bool → List Bool)
    (aux : Stacks K) (pre : Preload (w := w) A data constants aux) (hw : 1 ≤ w)
    (leaf : FiniteRoutine (Ports K)) (ans : List Bool) (ha : ans.length ≤ A) (leafTicks : ℕ)
    (k : PairCall.Ordinals (addressed rs (data false)))
    (hk : ∀ b, (addressed rs (data false)).ordinal b = (k b).val)
    (fit : ∀ b, RadicalCertificate.MonomialIndex.ISA.Fits
      (RadicalCertificate.MonomialIndex.ISA.graded (data false).arity ((data false).degree b) (k b)) w)
    (ss : PairCall.equationSpace w A (data false) ≤ S) (trans : transient A (data false).arity w ≤ S) :
    let d := addressed rs (data false)
    let a := PairCall.monomial d k false
    let c := PairCall.monomial d k true
    let pack := selected false (PairCall.difference w a c)
    let flag := selected false (digits w (decide (a.val ≤ c.val)).toNat)
    (a.val ≤ c.val → ∃ n ≤ leafTicks, ∃ rest : List Bool, rest.length ≤ d.arity*w ∧
      leaf.BoundedRun S n (frame rs [] (storage w data pack flag constants aux))
        (frame rs ans (storage w data (selected false rest) flag constants aux))) →
    ∃ n ≤ PairCall.scanClock w A d + PairCall.packClock d.arity w A + PairCall.clearCost w + postTicks A d.arity w leafTicks,
      (phase false leaf).BoundedRun S n (frame rs [] (storage w data blank blank constants aux))
        (frame rs (if a.val ≤ c.val then ans else constants false) (storage w data blank blank constants aux)) := by
  intro d a c pack flag yes
  have hA : A ≤ S := by dsimp [transient] at trans; omega
  obtain ⟨ns,hs,run⟩ := PairCall.equation_runs d k hk fit [] [] pre.words (pre.arity false) (by simp) (by simp)
  have run' := scan_bounded PairCall.equation false rs [] data blank blank constants aux
    (PairCall.difference w a c) (digits w (decide (a.val ≤ c.val)).toNat)
    (by simpa only [List.append_nil] using run.mono_cap ss)
    (fun z => (start_room rs data constants aux pre z).trans hA)
  have out := complete_phase hw false (decide (a.val ≤ c.val)) rs data constants aux pre trans leaf
    (PairCall.difference w a c) ans (by simp [a, c, d, addressed]) ha ⟨ns,hs,run'⟩
    (fun h => yes (of_decide_eq_true h))
  obtain ⟨v,hv,vr⟩ := out
  refine ⟨v,hv,?_⟩
  have same : (if decide (a.val ≤ c.val) then ans else constants false) =
      (if a.val ≤ c.val then ans else constants false) := by
    by_cases h : a.val ≤ c.val
    · rw [ite_eq_left (decide_eq_true h), ite_eq_left h]
    · rw [ite_eq_right (fun e => h (of_decide_eq_true e)), ite_eq_right h]
  exact same ▸ vr

/-- Complete powered-monomial read. The successful equality flag emits the
stored unit scalar, and an unequal exponent emits zero. This code also
handles marked or Frobenius targets via the scan's `scale` and `mark` words. -/
theorem powered_execution (rs : Reg → Word w) (data : Bool → PairCall.Inputs) (constants : Bool → List Bool)
    (aux : Stacks K) (pre : Preload (w := w) A data constants aux) (hw : 1 ≤ w)
    (k : PairCall.Ordinals (addressed rs (data true)))
    (hk : ∀ b, (addressed rs (data true)).ordinal b = (k b).val)
    (fit : ∀ b, RadicalCertificate.MonomialIndex.ISA.Fits
      (RadicalCertificate.MonomialIndex.ISA.graded (data true).arity ((data true).degree b) (k b)) w)
    (hfit : ExponentISA.Fits (PairCall.powerParams (data true)) w)
    (ss : PairCall.poweredSpace w A ≤ S) (trans : transient A (data true).arity w ≤ S) :
    let d := addressed rs (data true)
    let matched := PairCall.powerMatch d (PairCall.monomial d k false) (PairCall.monomial d k true)
    ∃ n ≤ PairCall.scanClock w A d + PairCall.powerClock d.arity w A + PairCall.clearCost w + postTicks A d.arity w (5*A+2),
      (phase true (emit true)).BoundedRun S n (frame rs [] (storage w data blank blank constants aux))
        (frame rs (constants matched) (storage w data blank blank constants aux)) := by
  intro d matched
  have hA : A ≤ S := by dsimp [transient] at trans; omega
  obtain ⟨ns,hs,run⟩ := PairCall.powered_runs d k hk fit hfit [] [] pre.words (pre.arity true) (by simp) (by simp)
  have run' := scan_bounded PairCall.powered true rs [] data blank blank constants aux [] (digits w matched.toNat)
    (by simpa only [List.append_nil] using run.mono_cap ss) (fun z => (start_room rs data constants aux pre z).trans hA)
  have out := complete_phase hw true matched rs data constants aux pre trans (emit true) [] (constants true)
    (by simp) (pre.scalars true) ⟨ns,hs,run'⟩ (leafTicks := 5*A+2) (fun _ => by
      have len := pre.scalars true
      refine ⟨_,by omega,[],by simp,spaceRun_of_steps (emit_runs rs true data (selected true [])
        (selected true (digits w matched.toNat)) constants aux) ?_⟩
      intro z
      have cap := frame_bound rs [] data (selected true []) (selected true (digits w matched.toNat)) constants aux pre.words
        (by simp) pre.arity (by intro b; cases b <;> simp [selected, blank])
        (by intro b; cases b <;> simp [selected,blank,pre.words]) pre.scalars pre.payload z
      exact (Nat.add_le_add cap (Nat.le_refl _)).trans (by dsimp [transient] at trans; omega))
  have sel : (if matched then constants true else constants false) = constants matched := by cases matched <;> rfl
  rwa [sel] at out

end RankQuery.Stack.MacaulayRead.Arms

end VPVNP
end Computability
end OAI

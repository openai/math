import OAI.Computability.MultitapeWeakETH.WitnessWalkExact
import OAI.Computability.IntegerMultiplication.Code.Padding

/-! # Uniform space and fuel cutoffs for the private witness traversal -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code
open private data? data_poly from OAI.Computability.MultitapeWeakETH.WitnessWalk

private structure Meter (A : Type) [Codec A] where
  count : A → Tally
  program : Poly count
  length : ∀ a, (count a).length = size a

private def atom {A : Type} [Codec A] (unit : ∀ a : A, size a = 1) : Meter A :=
  ⟨fun _ => [()],Code.Poly.const _,fun a => (unit a).symm⟩

private def Meter.pair {A B : Type} [Codec A] [Codec B] (x : Meter A) (y : Meter B) : Meter (A × B) where
  count p := () :: (x.count p.1 ++ y.count p.2)
  program := ((Code.Poly.const ()).pair ((Easy.fst.poly.compose x.program).app (Easy.snd.poly.compose y.program))).compose Easy.cons.poly
  length p := by simp [x.length,y.length]

private def Meter.list {A : Type} [Codec A] (x : Meter A) : Meter (List A) where
  count xs := () :: (xs.map (fun a => () :: x.count a)).flatten
  program := ((Code.Poly.const ()).pair ((Poly.maps _ (((Code.Poly.const ()).pair x.program).compose Easy.cons.poly)).compose Easy.flatten.poly)).compose Easy.cons.poly
  length xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.map_cons,List.flatten_cons,List.length_cons,List.length_append,size_cons,x.length] at *
      omega

private def stored : Meter Store :=
  let t := (atom (A:=Unit) (fun _ => rfl)).list
  let word := (atom size_bit).list
  (((t.pair t).pair word).list.pair word).pair t.list

private def fits (q : Tally × Tally) := (cutLists q).2.isEmpty

private theorem fits_poly : Poly fits := by
  have test : Easy (fun xs : Tally => xs.isEmpty) := by
    convert Easy.listCase (X:=Unit) true (Easy.const false) using 1
    funext xs; cases xs <;> rfl
  exact ((easy_cut Easy.identity).compose Easy.snd).poly.compose test.poly

private theorem fits_iff (cap n : Tally) : fits (cap,n) = true ↔ n.length ≤ cap.length := by
  simp [fits,cutLists,List.isEmpty_iff]

/-- Retain a candidate traversal state only within its unary space budget. -/
def clip (q : Tally × Option Store) : Option Store :=
  bif fits (q.1,stored.count (data? q.2)) then q.2 else none

theorem clip_poly : Poly clip :=
  Poly.choose ((Easy.fst.poly.pair (Easy.snd.poly.compose (data_poly.compose stored.program))).compose fits_poly)
    Easy.snd.poly (Code.Poly.const none)

theorem clip_some (cap : Tally) (q : Store) :
    clip (cap,some q) = some q ↔ size q ≤ cap.length := by
  have h := fits_iff cap (stored.count q)
  rw [stored.length] at h
  change (bif fits (cap,stored.count q) then some q else none) = some q ↔ _
  cases hit : fits (cap,stored.count q) <;> simp_all

theorem clip_size (cap : Tally) (q : Option Store) : size (clip (cap,q)) ≤ cap.length+2 := by
  unfold clip
  cases h : fits (cap,stored.count (data? q))
  · simp
  · have bound := (fits_iff _ _).mp h
    cases q with
    | none => simp
    | some v =>
      change (stored.count v).length ≤ cap.length at bound
      rw [stored.length] at bound
      simpa only [Bool.cond_true,size_some] using Nat.add_le_add_right bound 2

variable {D : Type} [Codec D] (visit : Visit D)

abbrev ClockState (D : Type) := (D × Tally) × Option Store

def clockStep (p : ClockState D) : ClockState D :=
  (p.1,clip (p.1.2,tick visit (p.1.1,p.2)))

private theorem clockStep_poly (h : Poly visit) : Poly (clockStep visit) :=
  Easy.fst.poly.pair (((Easy.fst.compose Easy.snd).poly.pair
    (((Easy.fst.compose Easy.fst).pair Easy.snd).poly.compose (tick_poly visit h))).compose clip_poly)

def clockRun (p : Tally × ClockState D) := (clockStep visit)^[p.1.length] p.2

/-- Uniform polynomial bit time on every encoded candidate, including histories
that try to create more pending jobs or coefficient names than the budget allows. -/
theorem clockRun_poly (h : Poly visit) : Poly (clockRun visit) := by
  have fuel : Dom (size (X:=Tally × ClockState D)) (fun p : Tally × ClockState D => p.1.length) := (Dom.base _).mono (fun p => by
    rw [size_prod,size_tally]; omega)
  have context (p : ClockState D) (j : ℕ) : ((clockStep visit)^[j] p).1 = p.1 := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply']; exact ih
  have reachable (p : Tally × ClockState D) (j : ℕ) : size ((clockStep visit)^[j] p.2) ≤ 3*(size p+1) := by
    cases j with
    | zero => change size p.2 ≤ _; simp only [size_prod]; omega
    | succ j =>
      let prev := (clockStep visit)^[j] p.2
      have same : prev.1 = p.2.1 := context p.2 j
      rw [Function.iterate_succ_apply']
      change size (prev.1,clip (prev.1.2,tick visit (prev.1.1,prev.2))) ≤ _
      have bound := clip_size prev.1.2 (tick visit (prev.1.1,prev.2))
      rw [size_prod,same]
      rw [same] at bound
      simp only [size_prod,size_tally] at *
      omega
  have run := bounded_iteration size (fun p : Tally × ClockState D => p.1.length) Prod.snd (clockStep visit) (clockStep_poly visit h)
    fuel 3 1 (fun p j _ => by simpa only [pow_one] using reachable p j)
  unfold Code.Poly clockRun
  simpa only [recover_tally,Prod.mk.eta] using run

end OAI.Computability.MultitapeWeakETH.WitnessWalk

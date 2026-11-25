import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveRetain
import OAI.Computability.NearSquareRoot.CRTPositionRouter

/-! # One emitted command for the three calls of a conjugated batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective.BatchCmd

open IntegerMultiplication Code EffectiveBoundedTask KernelEffectiveFamily CommonRegisters GeneratorSyntax
open InterchangeROMAddress.Affine PositionProgram Filter

noncomputable section

/-- The two relocation calls share the router. The first reads the inverse table,
the last reads the forward table, and the middle command sees the original header. -/
def compile (pre post : Cmd) (mid : Template) (a b : ℕ) (rect : Cmd) : Cmd :=
  (restoring ((leftCmd pre).join (routeCmd a b rect))).join
    ((restoring (mid.eval rect)).join ((leftCmd post).join (routeCmd a b rect)))

theorem effective {P : Type} [Primcodable P] (pre post : Cmd) (mid : Template)
    {a b : P → ℕ} {rect : P → Cmd} (ha : Computable a) (hb : Computable b)
    (hc : GeneratorSyntax.Effective ltr rect) :
    GeneratorSyntax.Effective ltr (fun p => compile pre post mid (a p) (b p) (rect p)) := by
  have route := routeCmd_effective ha hb hc
  exact (effective_restoring ((effective_const ltr (leftCmd pre)).join route)).join
    ((effective_restoring (mid.effective hc)).join ((effective_const ltr (leftCmd post)).join route))

theorem within (pre post : Cmd) (mid : Template) (R : ℕ) :
    ∃ B, 0 < B ∧ ∀ a b rect, Within R rect → Within B (compile pre post mid a b rect) := by
  obtain ⟨M,_,mask⟩ := mid.within R
  obtain ⟨N,_,route⟩ := routeCmd_within R
  obtain ⟨B,three,hM,hN,hpre,hpost⟩ :=
    ((eventually_ge_atTop (3:ℕ)).and ((eventually_ge_atTop M).and ((eventually_ge_atTop N).and
      ((RegisterSelect.within_eventually (leftCmd pre)).and (RegisterSelect.within_eventually (leftCmd post)))))).exists
  refine ⟨B,by omega,fun a b rect hr => ?_⟩
  have hroute := RegisterSelect.within_mono hN _ (route a b rect hr)
  exact ⟨within_restoring three ⟨hpre,hroute⟩,within_restoring three
    (RegisterSelect.within_mono hM _ (mask rect hr)),hpost,hroute⟩

variable {I : Type} {t s : I → ℕ} {h fwd rev u v w z : I → Tree}
  {pre post rect : Cmd} {mid : Template} {a b : ℕ}

/-- The child endpoint bound also bounds the array parked during projection. -/
private theorem projected {p c : Cmd} {key : I → Tree} (project : Runs p t s h key)
    (child : Runs c t s (fun i => .fork (key i) (u i)) v) :
    Runs ((leftCmd p).join c) t s (fun i => .fork (h i) (u i)) v := by
  have lifted : Runs (leftCmd p) t (fun i => s i+(u i).count)
      (fun i => .fork (h i) (u i)) (fun i => .fork (key i) (u i)) :=
    command_contract (leftCmd p) from project.task.left u
  obtain ⟨C,run⟩ := child
  apply Runs.sequence (c := leftCmd p) _ (show Runs c t s _ _ from ⟨C,run⟩)
  apply lifted.bound 1 (C+1) (fun _ => by simp)
  intro i
  obtain ⟨_,_,bare⟩ := run i [] (fun _ => []) 0 (fun _ => le_rfl)
  have cap := bare.start 0
  rw [letters_here,List.length_append,Tree.spell_length] at cap
  change (key i).count+(u i).count+1+0 ≤ 0+C*(s i+1) at cap
  change s i+(u i).count+1 ≤ (C+1)*(s i+1)
  rw [Nat.succ_mul]
  omega

private theorem retain {c : Cmd} (K : ℕ) (small : ∀ i, (h i).count ≤ K*(t i+1))
    (go : Runs c t s (fun i => .fork (h i) (u i)) v) :
    Runs (restoring c) t s (fun i => .fork (h i) (u i)) (fun i => .fork (h i) (v i)) := by
  apply go.retainHeader.bound (K+1) 1 _ (fun _ => by simp)
  intro i
  have bound := small i
  change (h i).count+t i+1 ≤ (K+1)*(t i+1)
  rw [Nat.succ_mul]
  omega

/-- A common time and arena bound for the actual table calls, header projections
and mask suffices for the entire command. -/
theorem run (K : ℕ) (small : ∀ i, (h i).count ≤ K*(t i+1))
    (preRun : Runs pre t s h rev) (postRun : Runs post t s h fwd)
    (place : Runs (routeCmd a b rect) t s (fun i => .fork (rev i) (u i)) v)
    (mask : Runs (mid.eval rect) t s (fun i => .fork (h i) (v i)) w)
    (undo : Runs (routeCmd a b rect) t s (fun i => .fork (fwd i) (w i)) z) :
    Runs (compile pre post mid a b rect) t s (fun i => .fork (h i) (u i)) z :=
  (retain K small (projected preRun place)).sequence
    ((retain K small mask).sequence (projected postRun undo))

/-- Correctness at arbitrary reserve guesses follows on the very same file.
Each of the five calls may initially supply its own time and arena bounds. -/
theorem runsSome
    (preRun : ∃ t s, Runs pre t s h rev) (postRun : ∃ t s, Runs post t s h fwd)
    (place : ∃ t s, Runs (routeCmd a b rect) t s (fun i => .fork (rev i) (u i)) v)
    (mask : ∃ t s, Runs (mid.eval rect) t s (fun i => .fork (h i) (v i)) w)
    (undo : ∃ t s, Runs (routeCmd a b rect) t s (fun i => .fork (fwd i) (w i)) z) :
    ∃ t s, Runs (compile pre post mid a b rect) t s (fun i => .fork (h i) (u i)) z := by
  obtain ⟨ta,sa,ha⟩ := preRun
  obtain ⟨tb,sb,hb⟩ := postRun
  obtain ⟨tc,sc,hc⟩ := place
  obtain ⟨td,sd,hd⟩ := mask
  obtain ⟨te,se,he⟩ := undo
  let clock i := (h i).count+ta i+tb i+tc i+td i+te i
  let arena i := sa i+sb i+sc i+sd i+se i
  refine ⟨clock,arena,run 1 (fun i => by simp only [clock,Nat.one_mul]; omega)
    (ha.mono ?_ ?_) (hb.mono ?_ ?_) (hc.mono ?_ ?_) (hd.mono ?_ ?_) (he.mono ?_ ?_)⟩
  all_goals intro i; dsimp only [clock,arena]; omega

end
end Controlled.Effective.BatchCmd

end NearSquareRoot
end Computability
end OAI

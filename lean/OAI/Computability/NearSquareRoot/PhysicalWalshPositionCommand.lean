import OAI.Computability.NearSquareRoot.PhysicalWalshPositionCommandRate
import OAI.Computability.NearSquareRoot.PhysicalWalshPositionCloth
import OAI.Computability.NearSquareRoot.PhysicalWalshSelectedCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps
import OAI.Computability.NearSquareRoot.CRTControlledReserveNative

/-! # The named native position router on physical Walsh records

The forward native read at an output address agrees with the inverse numeric
bit-address permutation. The selected Walsh program therefore supplies its
position table directly to the native command. Each film conversion scans the
record array once, regardless of the supplied command's time bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code Space FixedPoint Controlled Controlled.Reflections
open Adic Strip PositionCloth CommonRegisters KernelEffectiveFamily GeneratorSyntax Filter
open private native_encode ties_size from OAI.Computability.NearSquareRoot.PhysicalWalshPositionCloth

noncomputable section

abbrev NativeInput (K : ℕ) := {v : PositionInput // K ≤ v.k}

private def packWords (v : Table × List Dusk.Pair) := (v.1,v.2.map Dusk.tie)
private theorem packWords_easy : Easy packWords := Easy.fst.pair (Easy.snd.compose Dusk.tie_easy.mapping)

/-- Pack equal-width components, execute the chosen native command, and split
both components back out at each returned film's midpoint. -/
def positionCmd (native : Cmd) : Cmd :=
  (packWords_easy.choose.join native).join easy_untie.mapping.choose

theorem positionCmd_effective {J : Type} [Primcodable J] {r : J → Cmd} (hr : Effective ltr r) :
    Effective ltr (fun j => positionCmd (r j)) :=
  ((effective_const _ _).join hr).join (effective_const _ _)

theorem positionCmd_within (R : ℕ) : ∃ S, 0 < S ∧ ∀ n, Within R n → Within S (positionCmd n) := by
  obtain ⟨S,hS,hp,hu⟩ := ((eventually_gt_atTop R).and
    ((RegisterSelect.within_eventually packWords_easy.choose).and
     (RegisterSelect.within_eventually easy_untie.mapping.choose))).exists
  exact ⟨S,by omega,fun n hn => ⟨⟨hp,RegisterSelect.within_mono hS.le n hn⟩,hu⟩⟩

/-- The physical route acts on the table and (2^k) equal-length films.
`read` is the native source block for each target block. -/
def NativeAt (native : Cmd) {K : ℕ} (t r : NativeInput K → ℕ)
    (read : (q : NativeInput K) → Equiv.Perm (Block 2 q.val.k)) :=
  let k (q : NativeInput K) := q.val.k
  let row (q : NativeInput K) := q.val.row
  EffectiveBoundedTask.Runs native t r
    (fun q => .fork (send (table q.val.positions))
      (nativeRows k (fun q a => row q (flatAddress 2 (k q) a)) q))
    (nativeRows k (fun q a => row q (flatAddress 2 (k q) (read q a))))

/-- The native clock counts complete traversals of both component words. -/
abbrev NativePositionAt (native : Cmd) (ρ : ℝ) (K : ℕ) := NativeAt native
  (fun q : NativeInput K => nativeVolume q.val.k*(PositionProgram.positionFactor ρ q.val.k+1))
  (fun q => nativeVolume q.val.k) (fun q => flatBitPullback q.val.positions)

theorem filmRun {native : Cmd} {K : ℕ} {t r : NativeInput K → ℕ}
    (read : (q : NativeInput K) → Equiv.Perm (Block 2 q.val.k))
    (p : (q : NativeInput K) → Equiv.Perm (Fin (2^q.val.k)))
    (numeric : ∀ q a, flatAddress 2 q.val.k (read q a) = p q (flatAddress 2 q.val.k a))
    (h : NativeAt native t r read) :
    EffectiveBoundedTask.Runs (positionCmd native) (fun q => t q+Odd.volume q.val.k)
      (fun q => r q+Odd.volume q.val.k) (fun q => send (table q.val.positions,Odd.words q.val.row))
      (fun q => send (Odd.words (q.val.row ∘ p q))) := by
  let k (q : NativeInput K) := q.val.k
  let x (q : NativeInput K) := q.val.row
  let y (q : NativeInput K) := x q ∘ p q
  let v (q : NativeInput K) := (table q.val.positions, Odd.words (x q))
  have dest (q : NativeInput K) : nativeRows k (fun q a => x q (flatAddress 2 (k q) (read q a))) q =
      send (filmRows (y q)) := by
    simpa only [numeric,k,y,Function.comp_def] using native_encode k y q
  have transfer : EffectiveBoundedTask.Runs native t r (fun q => send (table q.val.positions,filmRows (x q)))
      (fun q => send (filmRows (y q))) := by
    apply AgendaOps.conform h (fun _ => rfl) (fun _ => rfl) _ dest
    intro q
    dsimp only
    rw [native_encode]
    rfl
  have pre := AgendaOps.easy packWords_easy v
  have post := AgendaOps.easy easy_untie.mapping (fun q => filmRows (y q))
  have recover q : (filmRows (y q)).map untie = Odd.words (y q) := by
    simp [filmRows,Odd.words,Function.comp_def]
  simp only [recover] at post
  have run := AgendaOps.compose (AgendaOps.compose pre transfer) post
  apply run.bound 900 900 <;> intro q
  all_goals
    have ht := table_volume q.val.positions
    have hx := row_volume (x q)
    have hy := (ties_size (Odd.words (y q))).trans (row_volume (y q))
    change size (filmRows (y q)) ≤ 400*Odd.volume q.val.k+1 at hy
  · change size (v q)+t q+size (filmRows (y q))+1 ≤ 900*(t q+Odd.volume q.val.k+1)
    simp only [v,size_prod]; omega
  · change max (max (size (v q)+size (v q)) (r q)) (size (filmRows (y q))+size (filmRows (y q)))+1 ≤ _
    simp only [v,size_prod]; omega

/-- The forward native route is correct for arbitrary physical budgets. This
variant also applies to templates whose reserve guesses give a larger clock. -/
theorem positionCmd_runs {native : Cmd} {K : ℕ} {t r : NativeInput K → ℕ}
    (h : NativeAt native t r (fun q => flatBitPullback q.val.positions)) :
    EffectiveBoundedTask.Runs (positionCmd native) (fun q => t q+Odd.volume q.val.k)
      (fun q => r q+Odd.volume q.val.k) (fun q => send (table q.val.positions,Odd.words q.val.row))
      (fun q => send (Odd.words (q.val.row ∘ (BoxFin.bitAddress q.val.positions).symm))) := by
  apply filmRun _ _ _ h
  intro q a
  simpa only [permuteNative_pullback,BoxFin.bitAddress_symm] using flat_native q.val.positions a

/-- Physical routing on the native line yields the required original-order
Walsh record router with the same command for every large width and table. -/
theorem positionRunsAt_of_native {native : Cmd} {ρ : ℝ} {K : ℕ} (hr : 0 ≤ ρ)
    (h : NativePositionAt native ρ K) : PositionRunsAt (positionCmd native) ρ K := by
  have t := positionCmd_runs h
  obtain ⟨B,hB⟩ := native_sparse_bounds hr
  exact t.bound B B (fun q => (hB q.val.k).1) (fun q => (hB q.val.k).2)

end
end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI

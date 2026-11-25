import OAI.Computability.NearSquareRoot.PhysicalWalshGrouped
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Fixed commands on the boundary of the grouped Walsh sweep

The six record operations use one command each across all widths, arities
and input arrays. The proofs instantiate each operation on its full input
type before specializing the resource bound to a caller.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GroupedCommand

open IntegerMultiplication Code Space FixedPoint
open EffectiveBoundedTask (Runs)

private abbrev Header := (Tally × Tally) × Tally
private abbrev Row := List Dusk.Pair

private noncomputable def easyCmd {α β : Type} [Codec α] [Codec β] {f : α → β} (hf : Easy f) : Cmd :=
  (BoundedTask.of_time hf).choose

private theorem easyRuns {α β I : Type} [Codec α] [Codec β] {f : α → β} (hf : Easy f) (xs : I → α) :
    EffectiveBoundedTask.Runs (easyCmd hf) (fun i => size (xs i)) (fun i => size (xs i)+size (xs i))
      (fun i => send (xs i)) (fun i => send (f (xs i))) :=
  (EffectiveBoundedTask.Runs.on (BoundedTask.of_time hf).choose_spec xs)

noncomputable def beginCmd := easyCmd Pieces.easy_begin
noncomputable def enterCmd := easyCmd Pieces.easy_enter
noncomputable def leaveCmd := easyCmd Pieces.easy_leave

theorem beginRuns {I : Type} (xs : I → Header × Row) :
    EffectiveBoundedTask.Runs beginCmd (fun i => size (xs i)) (fun i => size (xs i)+size (xs i))
      (fun i => send (xs i)) (fun i => send (Pieces.beginPass (xs i))) :=
  easyRuns Pieces.easy_begin xs

theorem enterRuns {I : Type} (xs : I → Header × (Tally × Row)) :
    EffectiveBoundedTask.Runs enterCmd (fun i => size (xs i)) (fun i => size (xs i)+size (xs i))
      (fun i => send (xs i)) (fun i => send (Pieces.enter (xs i))) :=
  easyRuns Pieces.easy_enter xs

theorem leaveRuns {I : Type} (xs : I → Header × Row) :
    EffectiveBoundedTask.Runs leaveCmd (fun i => size (xs i)) (fun i => size (xs i)+size (xs i))
      (fun i => send (xs i)) (fun i => send (Pieces.leavePass (xs i))) :=
  easyRuns Pieces.easy_leave xs

private structure TrimInput where
  w : ℕ
  n : ℕ
  ys : List (Dusk.Grain w)
  fits : n ≤ ys.length

noncomputable def trimCmd := (Padding.truncate TrimInput.w TrimInput.n TrimInput.ys TrimInput.fits).choose

theorem trimRuns {I : Type} (w n : I → ℕ) (ys : (i : I) → List (Dusk.Grain (w i)))
    (fits : ∀ i, n i ≤ (ys i).length) :
    let V i := ((ys i).length+1)*(w i+1)
    EffectiveBoundedTask.Runs trimCmd V V (fun i => send (tally (n i),(ys i).map Dusk.mark))
      (fun i => send (((ys i).take (n i)).map Dusk.mark)) :=
  EffectiveBoundedTask.Runs.on (Padding.truncate TrimInput.w TrimInput.n TrimInput.ys TrimInput.fits).choose_spec
    (fun i => ⟨w i,n i,ys i,fits i⟩)

private structure GridInput where
  k : ℕ
  s : ℕ
  sel : s ≤ k
  row : ℕ → Record k

noncomputable def makeWidthCmd := (Pieces.makeWidth GridInput.k GridInput.s GridInput.sel GridInput.row).choose
noncomputable def oddCmd := (Odd.bounded_range GridInput.k GridInput.s GridInput.sel GridInput.row).choose

theorem makeWidthRuns {I : Type} (k s : I → ℕ) (sel : ∀ i, s i ≤ k i) (x : (i : I) → ℕ → Record (k i)) :
    EffectiveBoundedTask.Runs makeWidthCmd (Odd.volume ∘ k) (Odd.volume ∘ k)
      (fun i => send ((tally (k i),tally (s i)),Pieces.words (2^k i) (x i)))
      (fun i => send (((tally (k i),tally (s i)),tally (componentBits (k i)+1)),Pieces.words (2^k i) (x i))) :=
  EffectiveBoundedTask.Runs.on (Pieces.makeWidth GridInput.k GridInput.s GridInput.sel GridInput.row).choose_spec
    (fun i => ⟨k i,s i,sel i,x i⟩)

theorem oddRuns {I : Type} (k s : I → ℕ) (sel : ∀ i, s i ≤ k i) (x : (i : I) → ℕ → Record (k i)) :
    EffectiveBoundedTask.Runs oddCmd (Odd.time ∘ k) (Odd.volume ∘ k)
      (fun i => send ((tally (k i),tally (s i)),(List.range (2^k i)).map (Dusk.mark ∘ x i)))
      (fun i => send (Odd.words (Odd.finish (s i) (fun j => x i j.val)))) :=
  EffectiveBoundedTask.Runs.on (Odd.bounded_range GridInput.k GridInput.s GridInput.sel GridInput.row).choose_spec
    (fun i => ⟨k i,s i,sel i,x i⟩)

end PhysicalWalsh.GroupedCommand

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.VPVNP.RankCoordinateReaderSpace
import OAI.Computability.VPVNP.RankQueryRoutineSpace

/-! # Returning a Cramer quotient to the native evaluator

Both determinant programs and the quotient arithmetic run inside a finite
workspace. After the quotient has been copied into the evaluator's scalar
operand, one pass clears every workspace stack, including the two determinant
results and any registers left by the coefficient readers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.NativeReader

open RAMTape UniversalCountStack SliceArithmetic
open Cramer SchurPair

variable {A H K L : Type}

/-- The scalar reader's public ports with separate auxiliary banks for advice and writable
workspace. -/
abbrev Bus (A H : Type) := Reader.Port (A ⊕ H)
/-- The denominator, numerator, and quotient working banks of the paired Schur query. -/
abbrev Workspace (K L : Type) := SchurPair.Host K L

/-- Embed one stack of the Schur-pair workspace in the writable portion of the scalar-reader
bus. -/
def port (host : Workspace K L ↪ H) (i : Workspace K L) : Bus A H :=
  .aux (.inr (host i))

theorem port_injective (host : Workspace K L ↪ H) : Function.Injective (port (A := A) host) := by
  intro x y h; exact host.injective (Sum.inr.inj (Reader.Port.aux.inj h))

/-- The multiplication accumulator containing the final numerator divided by the denominator. -/
def quotient : Workspace K L := .inr (.inr (.inl (.inl (.inr .acc))))

/-- Combine the label, live basis ordinals, scalar result, immutable advice, and writable
workspace into one reader state. -/
def state (label current next result : List Bool) (advice : Stacks A) (work : Stacks H) :=
  Reader.bank label current next result (Sum.elim advice work)

variable [DecidableEq A] [DecidableEq H] [Fintype H]

/-- Copy the completed quotient to the public scalar result and reclaim the reader's working
stacks. -/
noncomputable def finish (host : Workspace K L ↪ H) (scratch : H) : FiniteRoutine (Bus A H) :=
  (SuccessorFields.prependCopy (port host quotient) .result (.aux (.inr scratch))).followedBy Reader.reclaim

/-- Bound the final result copy and cleanup scan using the workspace's port count and peak
stack height. -/
def returnClock (H : Type) [Fintype H] (peak : ℕ) := 5*peak+2 + (Fintype.card H*(peak+1)+1)

theorem finish_bounded (host : Workspace K L ↪ H) (scratch : H) (disjoint : ∀ i, host i ≠ scratch)
    (label current next : List Bool) (advice : Stacks A) (work : Stacks H) (answer : List Bool)
    (peak : ℕ) (start : ∀ i, (state label current next [] advice work i).length ≤ peak)
    (hs : work scratch = []) (hq : work (host quotient) = answer) :
    ∃ t ≤ returnClock H peak, (finish host scratch).BoundedRun (peak+returnClock H peak) t
      (state label current next [] advice work)
      (state label current next answer advice (fun _ => [])) := by
  let initial := state label current next [] advice work
  let copied := state label current next answer advice work
  have hcopy := SuccessorFields.prependCopy_runs (port (A := A) host quotient) .result (.aux (.inr scratch))
    (fun h => by contradiction) (fun h => disjoint quotient (Sum.inr.inj (Reader.Port.aux.inj h)))
    (fun h => by contradiction) initial hs
  have hcopied : Function.update initial .result (initial (port host quotient) ++ initial .result) = copied := by
    funext i; cases i <;> first | rfl | (change work (host quotient) ++ [] = answer; rw [hq,List.append_nil])
  rw [hcopied] at hcopy
  obtain ⟨t,ht,hclean⟩ := Reader.reclaim_runs label current next answer advice work peak (fun h => start (.aux (.inr h)))
  have combined := hcopy.followedBy hclean
  have hb : 5*(initial (port host quotient)).length+2+t ≤ returnClock H peak :=
    Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (start _)) _) ht
  exact ⟨_,hb,spaceRun_of_steps combined (fun k => Nat.add_le_add (start k) hb)⟩

/-- Prepare the live arguments, evaluate the Schur pair on its mounted workspace, then return
the quotient and clean up. -/
noncomputable def core (host : Workspace K L ↪ H) (scratch : H) (prepare : FiniteRoutine (Bus A H))
    (a : Engine.Actions K) (b : Engine.Actions L) : FiniteRoutine (Bus A H) :=
  (prepare.followedBy ((SchurPair.query a b).onPorts (port host))).followedBy (finish host scratch)

variable [DecidableEq K] [DecidableEq L]

/-- Execute a prepared physical determinant pair and return with precisely
the same label, basis indices and persistent advice. -/
theorem core_bounded (host : Workspace K L ↪ H) (scratch : H) (disjoint : ∀ i, host i ≠ scratch)
    (prepare : FiniteRoutine (Bus A H)) (a : Engine.Actions K) (b : Engine.Actions L)
    (label current next : List Bool) (advice : Stacks A) (work : Stacks H) (hs : work scratch = [])
    (before after : Stacks (Workspace K L)) (hin : ∀ i, work (host i) = before i)
    (answer : List Bool) (hq : after quotient = answer) {peak setup query : ℕ}
    (hsetup : prepare.BoundedRun peak setup (state label current next [] advice (fun _ => []))
      (state label current next [] advice work))
    (hquery : (SchurPair.query a b).BoundedRun peak query before after) :
    ∃ t ≤ setup+query+returnClock H peak,
      (core host scratch prepare a b).BoundedRun (peak+returnClock H peak) t
        (state label current next [] advice (fun _ => []))
        (state label current next answer advice (fun _ => [])) := by
  let out := installStacks host work after
  have hrun : ((SchurPair.query a b).onPorts (port host)).BoundedRun peak query
      (state label current next [] advice work) (state label current next [] advice out) := by
    apply FiniteRoutine.BoundedRun.framed (port_injective host) hquery hsetup.final_cap hin
    · exact fun i => installStacks_at host.injective work after i
    · intro i hi
      cases i with
      | aux i =>
        rcases i with i|i
        · rfl
        · exact installStacks_outside work after (fun k hk => hi k (congrArg (fun z => Reader.Port.aux (Sum.inr z : A ⊕ H)) hk))
      | _ => rfl
  have hq' : out (host quotient) = answer := (installStacks_at host.injective work after _).trans hq
  have hs' : out scratch = [] := (installStacks_outside work after disjoint).trans hs
  obtain ⟨n,hn,hr⟩ := finish_bounded host scratch disjoint label current next advice out answer peak hrun.final_cap hs' hq'
  exact ⟨_,Nat.add_le_add_left hn _,((hsetup.followedBy hrun).enlarge (Nat.le_add_right ..)).followedBy hr⟩

end RankQuery.Stack.Coordinate.NativeReader

end VPVNP
end Computability
end OAI

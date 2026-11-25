import OAI.Computability.BorderVNP.DiagonalTaggedRound
import OAI.Computability.BorderVNP.DiagonalPowerCopies
import OAI.Computability.BorderVNP.ShortenPlacedStep

/-! # Conditioned input entries on the very same step as the physical pack geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening Packing PlacedStep
open scoped BigOperators Classical

variable {D b m : ℕ} {P : Type} {bits : P → ℕ} {Team Param Gadget E : Type*}
    [Fintype Team] [Fintype Param]

/-- The conditioned table and its original power words, on a prescribed
public network. The choice of the underlying network is external to the
private entries and is fixed by the adaptive geometry. -/
structure Tracked (Team Param Gadget : Type*) [Fintype Team] [Fintype Param] (b : ℕ)
    (N : Network D P bits) where
  /-- The passing or rejection record and scalar counts at every local input. -/
  tags : N.Tables (Entry Param Gadget)
  /-- Individual original power positions remain available at their owning boxes. -/
  words : PowerWords Team Param Gadget b N tags

namespace Tracked

variable {N : Network D P bits}

private theorem univ_eq {X : Type*} (f g : Fintype X) :
    @Finset.univ X f = @Finset.univ X g :=
  congrArg (@Fintype.elems X) (Subsingleton.elim f g)

/-- A conditioned public pack interpreted over its true parameter ring. -/
noncomputable def valued [CommSemiring E] (values : Gadget → E)
    (t : Tracked Team Param Gadget b N) : Pack D P bits (MvPolynomial Param E) :=
  ⟨N, fun v z x => interpret values (t.tags v z x)⟩

variable {k : ℕ} {I : Type} [Fintype I] {B : Type} [Fintype B] {l l' : ℕ}
    [Field E] [NeZero D] (e : PaidIdentity E D m) (position : e.Entry → Gadget)
    {child : Fin k → PlacedPack D P bits E I l} (step : PlacedStep m B l' child)
    (input : ∀ i, Tracked Team Param Gadget b (child i).pack.layout)

/-- The same move, permuted bins, selected prefixes and profile choices as
the given physical step, now evaluating the conditioned private tables. -/
noncomputable def output (q : step.Index e) :
    Tracked (Fin k × Team) Param Gadget b (step.result e q).pack.layout := by
  let src := parallelPacks (fun i => (⟨(child i).pack.layout,(input i).tags⟩ :
    Pack D P bits (Entry Param Gadget)))
  let w := PowerWords.parallel (fun i => (input i).tags) (fun i => (input i).words)
  exact ⟨(roundTags src step.bin step.perm e position step.positive (0,false) q).table,
    roundWords src step.bin step.perm e position step.positive (0,false) w q⟩

set_option maxHeartbeats 1500000 in
/-- Each attained histogram gets exactly its mathematical weight after
conditioning. In particular the admissible histogram indices do not depend
on the private factors, the live pin, or the scalar values they read. -/
theorem sum_output (values : Gadget → E) (lookup : ∀ i, values (position i) = e.entry i)
    (x : Ports fun z : Fin k × P => bits z.2) :
    (∏ i, ((input i).valued values).tensor (fun p => x (i,p))) =
      ∑ q : step.Index e, ((output e position step input q).valued values).tensor x := by
  let src := parallelPacks (fun i => (⟨(child i).pack.layout,(input i).tags⟩ :
    Pack D P bits (Entry Param Gadget)))
  refine (Network.parallel_value (fun i => (child i).pack.layout)
    (fun i v z y => interpret values ((input i).tags v z y)) x).symm.trans ?_
  refine (roundTags_sum src step.bin step.perm e position step.positive (0,false) values lookup x).trans ?_
  apply Finset.sum_congr _ (fun _ _ => rfl)
  exact univ_eq _ _

end Tracked
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI

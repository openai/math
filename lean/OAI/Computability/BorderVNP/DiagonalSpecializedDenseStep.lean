import OAI.Computability.BorderVNP.ShortenRetable
import OAI.Computability.BorderVNP.PackedHistoryDenseStep

/-! # Specialized profile expansion in the serializer's actual row order

The native stage sorts all incoming cables by stable row ID before choosing
interval endpoints. Apply the crossing on that very layout, then reindex
the successor by its physical output storage. All layouts and history
indices belong to the reference field, whereas the scalar entries used by
the private tables can lie in the finite field of the chosen branch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.DenseReplay

open Crossing Shortening Adaptive Packing PackedHistoryCircuit.Normalized
open scoped BigOperators Classical

set_option maxHeartbeats 2000000

variable {D m k d next exp : ℕ} [NeZero D] {I P B : Type} [Fintype I] [Fintype B]
    {bits : P → ℕ} {Team Param Gadget K E : Type} [Fintype Team] [Fintype Param]
    [Field K] [Field E] {child : Fin k → PlacedPack D P bits K I d}

variable (s : Stage m B next child) (input : ∀ i, Tracked Team Param Gadget exp (child i).pack.layout)

/-- Merge the child tags with the child index retained on every power position. -/
noncomputable def merged : Tracked (Fin k × Team) Param Gadget exp (raw child).layout :=
  ⟨Network.parallelTables (fun i => (child i).pack.layout) (fun i => (input i).tags),
    PowerWords.parallel (fun i => (input i).tags) (fun i => (input i).words)⟩

/-- The tagged input at the slots where the public interval allocator reads it. -/
noncomputable def ordered : Tracked (Fin k × Team) Param Gadget exp s.input.layout :=
  (Storage.dense (raw child).layout s.slot).tracked (merged input)

variable (e : PaidIdentity K D m) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)

/-- The tags and full power words on the sorted-stage output at this public profile. -/
noncomputable def stageOutput (q : s.Index e) :
    Tracked (Fin k × Team) Param Gadget exp (s.result e q).pack.layout := by
  let tags := ordered s input
  let src : Pack D (Fin k × P) (fun z => bits z.2) (Entry Param Gadget) := ⟨s.input.layout,tags.tags⟩
  exact ⟨(roundTags src s.label s.perm (e.specialize y hy) pos s.orient (0,false) q).table,
    roundWords src s.label s.perm (e.specialize y hy) pos s.orient (0,false) tags.words q⟩

/-- Sum of the actual sorted-profile outputs over the specialized field. -/
theorem stage_sum (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (x : Ports fun z : Fin k × P => bits z.2) :
    (∏ i, ((input i).valued values).tensor (fun p => x (i,p))) =
      ∑ q : s.Index e, ((stageOutput s input e y hy pos q).valued values).tensor x := by
  let tags := ordered s input
  let src : Pack D (Fin k × P) (fun z => bits z.2) (Entry Param Gadget) := ⟨s.input.layout,tags.tags⟩
  refine (Network.parallel_value (fun i => (child i).pack.layout)
    (fun i v z p => interpret values ((input i).tags v z p)) x).symm.trans ?_
  refine ((Storage.dense (raw child).layout s.slot).tracked_tensor (merged input) values x).symm.trans ?_
  refine (roundTags_sum src s.label s.perm (e.specialize y hy) pos s.orient (0,false) values lookup x).trans ?_
  apply Finset.sum_congr _ (fun _ _ => rfl)
  exact congrArg (@Fintype.elems (s.Index e)) (Subsingleton.elim _ _)

end Diagonal.CellEntries.DenseReplay

end BorderVNP
end Computability
end OAI

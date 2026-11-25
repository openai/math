import OAI.Computability.NearSquareRoot.CRTTableStageHeader
import OAI.Computability.NearSquareRoot.CRTTableRelocate
import OAI.Computability.NearSquareRoot.CRTTablePackedRun

/-! # The CRT queries of a prepared physical Beneš stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication IntegerMultiplication.Code

abbrev PreparedSeed := HeaderSeed × List Tally × List Tally

/-- Compute the complete natural plan before selecting the physical batch and
transporting the bit positions to the prepared prefix. -/
def preparedPlan (p : PreparedSeed) := relocate (stageHeader p.1,p.2)

theorem preparedPlan_poly : Poly preparedPlan :=
  (((Easy.fst (X := HeaderSeed) (Y := List Tally × List Tally)).poly.compose stageHeader_poly).pair
    Easy.snd.poly).compose relocate_poly

/-- A charged regime may compute the prepared header directly from the
three small values its geometry preprocessor supplies. -/
theorem preparedPlan_has {X : Type} {r : IntegerMultiplication.Strip.Regime X}
    {seed : X → HeaderSeed} {dir blocks : X → List Tally}
    (hs : r.Has seed) (hd : r.Has dir) (hb : r.Has blocks) :
    r.Has (fun x => preparedPlan (seed x,dir x,blocks x)) :=
  (hs.pair (hd.pair hb)).thenDo preparedPlan_poly

/-- Literal header used at a charged stage after physical placement. -/
theorem preparedPlan_makePlan {d m : ℕ} (a w : Fin d → ℕ) (n : ℕ)
    (hn : n ≤ Nat.clog 2 d) (inv side : Bool) (stage : ℕ)
    (dir : List Tally) (lift : ℕ → ℕ) (subset : Fin m → Fin (targetOrder d n).length)
    (ho : ∀ k ∈ levelPositions w (List.finRange d) n, Iter.pick [] (dir,k) = tally (lift k.length))
    (hi : ∀ b : Fin m, let g := targetAxis d n (targetRank d n (subset b))
      ∀ k : Fin (w g), Iter.pick [] (dir,tally (fieldPosition w (List.finRange d) g k)) =
        tally (lift (fieldPosition w (List.finRange d) g k))) :
    let chosen := fun b => targetRank d n (subset b)
    let g := fun b => targetAxis d n (chosen b)
    preparedPlan (((side,tally stage),inv,tally n,(List.finRange d).map (descriptor a w)),
        dir,List.ofFn fun b => tally (subset b).val) =
      Benes.makePlan side stage ((levelPositions w (List.finRange d) n).map (fun k => tally (lift k.length)))
        (fun b => w (g b)) (fun b => tagAt a w n (chosen b).1.val (chosen b).2.val inv)
        (fun b k => lift (fieldPosition w (List.finRange d) (g b) k)) := by
  dsimp only
  rw [preparedPlan,stageHeader_makePlan a w n hn inv side stage]
  exact relocate_makePlan _ _ _ _ dir lift subset side stage ho hi

/-- All actual switch queries emitted after reading one prepared prefix. -/
def preparedQueries (p : PreparedSeed × List Bool) :=
  Benes.buildBatch targetWordRows (preparedPlan p.1,p.2)

theorem preparedQueries_poly : Poly preparedQueries :=
  (((Easy.fst (X := PreparedSeed) (Y := List Bool)).poly.compose preparedPlan_poly).pair
    Easy.snd.poly).compose (Benes.buildBatch_poly (([],[]),false,[],[]) targetWordRows targetWordRows_poly)

/-- Correct table invariant for a physical header that relocated its external
bit positions. Only the selected control bits need to remain observable in the
prepared prefix. Target words may vary independently within the batch. -/
theorem preparedTable_represents {d : ℕ} (a w : Fin d → ℕ) [∀ j, NeZero (a j)]
    (hw : ∀ j, a j ≤ 2^w j) (hdense : ∀ j, 2^w j ≤ 2*a j)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (n : ℕ) (hn : n < Nat.clog 2 d)
    (inv : Bool) (y : (g : Fin d) → AxisValue a w g) (b : TargetIndex d n)
    (prepared : List Bool) (lift : ℕ → ℕ)
    (hmove : ∀ k ∈ levelPositions w (List.finRange d) n,
      Benes.prefixBit (prepared,tally (lift k.length)) =
      Benes.prefixBit (packFields (addressField a w (fun _ => id) y) (List.finRange d),k)) :
    Benes.RawRepresents (blockPerm a w hw n hn inv ((packAddress a w hw n y).1) b)
      (targetWordRows (tagAt a w n b.1.val b.2.val inv,Benes.prefixBits
        (prepared,(levelPositions w (List.finRange d) n).map (fun k => tally (lift k.length))))) := by
  have widths (j : Fin d) (_ : j ∈ List.finRange d) :
      (addressField a w (fun _ => id) y j).length = w j := by simp [addressField,Bits.phrase_length]
  rw [prefixBits_transport _ _ _ _ hmove,prefixBits_levelPositions _ _ _ widths,
    blockPerm_on a w hw n hn inv y b]
  exact targetWordRows_represents a w (fun _ => id) hw hdense hcop n hn b.1 y inv b.2

end CRTTable

end NearSquareRoot
end Computability
end OAI

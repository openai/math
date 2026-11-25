import OAI.Computability.NearSquareRoot.CRTTableStageSlots
import OAI.Computability.NearSquareRoot.CRTTablePrefixProgram
import OAI.Computability.NearSquareRoot.CRTTableBenesQuery

/-! # Physical generation of complete batch headers for CRT switch layers -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication.Code

/-- Switch direction and bit rank, followed by CRT direction, depth, and
the full width/modulus field directory. -/
abbrev HeaderSeed := (Bool × Tally) × Bool × Tally × List ControlAxis
private abbrev HeaderFields := (Bool × Tally × List ControlAxis) × List (List Tally)

private def blockHeader (s : HeaderFields × Slot) : Benes.BlockPlan TargetTag :=
  let field := Iter.pick [] (s.1.2,s.2.2)
  ((s.2.1,s.1.1),ruler field,field)

private theorem blockHeader_poly : Poly blockHeader := by
  let X := HeaderFields × Slot
  have f := (show Poly (fun s : X => (s.1.2,s.2.2)) by fun_prop).compose
    (Iter.facile ([] : List Tally)).poly
  exact (show Poly (fun s : X => (s.2.1,s.1.1)) by fun_prop).pair
    ((f.compose (Easy.ruler Easy.identity).poly).pair f)

/-- Emit the actual batch encoding from the box and the two stage
indices. This program computes all target tags, supplies their exact widths
and natural bit positions, and writes the full external-control position list. -/
def stageHeader (p : HeaderSeed) : Benes.BatchPlan TargetTag :=
  ((p.1.1,p.1.2,externalPositions p.2.2),
    polyPush blockHeader ((p.2,positionFields p.2.2.2),targetListing p.2.2))

theorem stageHeader_poly : Poly stageHeader := by
  let X := HeaderSeed
  have depth := (show Poly (fun p : X => p.2.2) by fun_prop)
  have outer := depth.compose externalPositions_poly
  have fields := (show Poly (fun p : X => p.2.2.2) by fun_prop).compose positionFields_poly
  have ctx := (Easy.snd (X := Bool × Tally) (Y := Bool × Tally × List ControlAxis)).poly.pair fields
  have body := (ctx.pair (depth.compose targetListing_poly)).compose
    (Poly.push ((false,[],[]),[]) (([],[]),[]) blockHeader_poly)
  exact ((show Poly (fun p : X => p.1.1) by fun_prop).pair
    ((show Poly (fun p : X => p.1.2) by fun_prop).pair outer)).pair body

private theorem listing_eq_of_length {d : ℕ} (xs : List ControlAxis) (he : xs.length = d) (n : ℕ)
    (hn : n ≤ Nat.clog 2 d) : targetListing (tally n,xs) = (targetOrder d n).map slotOf := by
  subst d
  exact targetListing_eq xs n hn

variable {d : ℕ} (a w : Fin d → ℕ)

/-- Relate each of the fields emitted by the single finite coded program
to the parameters of the physical masked-switch implementation. The list
of target ports enumerates every (node, local target) exactly once. -/
theorem stageHeader_makePlan (n : ℕ) (hn : n ≤ Nat.clog 2 d) (inv side : Bool) (stage : ℕ) :
    let slots := targetRank d n
    let g := fun b => targetAxis d n (slots b)
    stageHeader ((side,tally stage),inv,tally n,(List.finRange d).map (descriptor a w)) =
      Benes.makePlan side stage (levelPositions w (List.finRange d) n)
        (fun b => w (g b))
        (fun b => tagAt a w n (slots b).1.val (slots b).2.val inv)
        (fun b k => fieldPosition w (List.finRange d) (g b) k) := by
  let xs := List.finRange d
  let desc := descriptor a w
  have widths (j : Fin d) (_ : j ∈ xs) : (desc j).1.length = w j := by simp [desc,descriptor]
  have selected := listing_eq_of_length (xs.map desc) (show (xs.map desc).length = d by simp [xs]) n hn
  have fields := positionFields_spec w xs (List.nodup_finRange _) desc widths
  have outer := externalPositions_spec w xs (List.nodup_finRange _) desc widths n (by simpa [xs] using hn)
  dsimp only
  rw [stageHeader,outer,fields,selected]
  unfold Benes.makePlan
  congr 1
  simp only [polyPush,List.map_map]
  apply List.ext_getElem
  · simp
  · intro r hr hr'
    let b := (targetOrder d n)[r]'(by simpa using hr)
    let g := targetAxis d n b
    have pick := Iter.search (xs.map (fun v => List.ofFn (fun k => tally (fieldPosition w xs v k))))
      ([] : List Tally) g.val (by simp [xs])
    simp only [List.getElem_map] at pick
    have key : xs[g.val]'(by simp [xs]) = g := by simp [xs]
    rw [key] at pick
    simp only [List.getElem_map,List.getElem_ofFn]
    change ((_,_),ruler (Iter.pick _ (_,tally g.val)), Iter.pick _ (_,tally g.val)) = _
    rw [pick, ← recover_tally (ruler (List.ofFn (fun k => tally (fieldPosition w xs g k)))),
      ruler_length, List.length_ofFn]
    rfl

end CRTTable

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.NearSquareRoot.FourierBatchDirectory
import OAI.Computability.NearSquareRoot.PermutationLayoutDirectory
import OAI.Computability.NearSquareRoot.CRTControlledBenesMask

/-! # Physical prefix lookups for a selected Fourier batch of raw switch tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication IntegerMultiplication.Code

abbrev Directory := List (Tally × RawTable)
abbrev Positions := List Tally
abbrev Context := Directory × Positions
abbrev Input := (Bool × Tally) × Context × List Tally

def widths (d : Directory) : List Tally := d.map Prod.fst

@[fun_prop] theorem widths_poly : Poly widths := Poly.maps _ Easy.fst.poly

/-- Consult the inverse position table at every natural port of the full selected word,
including the active port (whose value is ignored by the switch queries). -/
def row (x : Context × Tally) : BlockPlan RawTable :=
  let r := Iter.pick (([],[]) : Tally × RawTable) (x.1.1,x.2)
  let natural := FieldDirectory.ports (widths x.1.1,x.2)
  (r.2,r.1,polyPush (Iter.pick ([] : Tally)) (x.1.2,natural))

@[fun_prop] theorem row_poly : Poly row := by
  let X := Context × Tally
  have pick := (show Poly (fun x : X => (x.1.1,x.2)) by fun_prop).compose
    (Iter.facile (([],[]) : Tally × RawTable)).poly
  have src := (show Poly (fun x : X => (widths x.1.1,x.2)) by fun_prop).compose FieldDirectory.ports_poly
  have rel := ((show Poly (fun x : X => x.1.2) by fun_prop).pair src).compose
    (Poly.push [] [] (Iter.facile ([] : Tally)).poly)
  exact pick.sndCompose.pair (pick.fstCompose.pair rel)

def plan (x : Input) : BatchPlan RawTable :=
  ((x.1.1,x.1.2,[]),polyPush row (x.2.1,x.2.2))

theorem plan_poly : Poly plan := by
  let e : Context := ([],[])
  exact (show Poly (fun x : Input => (x.1.1,x.1.2,([] : List Tally))) by fun_prop).pair
    ((show Poly (fun x : Input => x.2) by fun_prop).compose (Poly.push e [] row_poly))

theorem plan_eq {d b k : ℕ} (w : Fin d → ℕ) (t : Fin d → RawTable) (subset : Fin b → Fin d)
    (port : (q : Fin d) → Fin (w q) → Fin k)
    (natural : ∀ q i, (port q i).val = FieldDirectory.position w q i)
    (relative : Fin k → ℕ) (side : Bool) (j : ℕ) :
    plan ((side,tally j),
      (List.ofFn (fun q => (tally (w q),t q)),List.ofFn fun z => tally (relative z)),
      List.ofFn fun q => tally (subset q).val) =
    makePlan side j [] (fun q => w (subset q)) (fun q => t (subset q))
      (fun q i => relative (port (subset q) i)) := by
  simp only [plan,makePlan,polyPush,List.map_ofFn,Prod.mk.injEq,true_and]
  apply congrArg List.ofFn
  funext q
  simp only [Function.comp_apply,row,Iter.entry,widths,List.map_ofFn,Prod.mk.injEq,true_and]
  rw [show (Prod.fst ∘ fun q => (tally (w q),t q)) = (fun q => tally (w q)) from rfl]
  rw [FieldDirectory.ports_eq]
  simp only [polyPush,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,← natural,Iter.entry]

/-- The runtime prefix serves only as a source of local address bits. A Fourier
permutation row uses the same precomputed raw tables at every external setting. -/
def queries (x : Input × List Bool) := buildBatch (Prod.fst : RawTable × List Bool → RawTable) (plan x.1,x.2)

theorem queries_poly : Poly queries :=
  ((Easy.fst.poly.compose plan_poly).pair Easy.snd.poly).compose
    (buildBatch_poly ([] : RawTable) Prod.fst Easy.fst.poly)

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI

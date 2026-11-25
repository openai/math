import OAI.Computability.NearSquareRoot.CRTTableNativePlanGeometry
import OAI.Computability.NearSquareRoot.CRTTablePrepared
import OAI.Computability.NearSquareRoot.PermutationLayoutDirectory
import OAI.Computability.NearSquareRoot.CRTControlledRowControls

/-! # Compiling the native masked-XOR directory for a CRT subbatch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable.Native
open IntegerMultiplication Code Strip
open Controlled PermutationLayout

/-- Stage, low reserve and guard stride, address width, and selected target ordinals. -/
abbrev Seed := HeaderSeed × (Tally × Tally) × Tally × List Tally

/-- Switch ports in the numbering of the original little-endian tape address. -/
def naturalPlan (x : Seed) :=
  preparedPlan (x.1,(Iter.lineup x.2.2.1).reverse,x.2.2.2)

theorem naturalPlan_poly : Poly naturalPlan :=
  ((show Poly (fun x : Seed => x.1) by fun_prop).pair
    (((show Poly (fun x : Seed => x.2.2.1) by fun_prop).compose Iter.poly_line).rev.pair
      (show Poly (fun x : Seed => x.2.2.2) by fun_prop))).compose preparedPlan_poly

def banks (p : Benes.BatchPlan TargetTag) : List Tally × List Tally :=
  let fields := polyPush Benes.FieldDirectory.split (p.1.2.1,p.2.map (fun z => z.2.2))
  ((fields.map Prod.fst).flatten,p.1.2.2 ++ (fields.map Prod.snd).flatten)

theorem banks_poly : Poly banks := by
  have rows := (show Poly (fun p : Benes.BatchPlan TargetTag => p.2) by fun_prop).compose
    (Poly.maps _ (show Poly (fun z : Benes.BlockPlan TargetTag => z.2.2) by fun_prop))
  have fx := ((show Poly (fun p : Benes.BatchPlan TargetTag => p.1.2.1) by fun_prop).pair rows).compose
    (Poly.push [] [] Benes.FieldDirectory.split_easy.poly)
  have a := fx.compose (Poly.maps _ (Easy.fst (X := List Tally) (Y := List Tally)).poly) |>.compose Easy.flatten.poly
  have b := fx.compose (Poly.maps _ (Easy.snd (X := List Tally) (Y := List Tally)).poly) |>.compose Easy.flatten.poly
  exact a.pair (((show Poly (fun p : Benes.BatchPlan TargetTag => p.1.2.2) by fun_prop).pair b).compose Easy.append.poly)

/-- Both reflected permutations, and the prepared prefix offsets indexed in
the native record's little-endian numbering. -/
def placement (x : Seed) :=
  directory (x.2.2.1,x.2.1,banks (naturalPlan x))

theorem placement_poly : Poly placement :=
  ((show Poly (fun x : Seed => x.2.2.1) by fun_prop).pair
    ((show Poly (fun x : Seed => x.2.1) by fun_prop).pair (naturalPlan_poly.compose banks_poly))).compose
      directory_poly

/-- Both direction tables and the CRT-specific query program normalized to
the fixed high prefix of the prepared row. -/
def prepare (x : Seed) :=
  let p := placement x
  (p.1,preparedPlan (x.1,p.2.reverse,x.2.2.2))

theorem prepare_poly : Poly prepare :=
  placement_poly.fstCompose.pair (((show Poly (fun x : Seed => x.1) by fun_prop).pair
    (placement_poly.sndCompose.rev.pair (show Poly (fun x : Seed => x.2.2.2) by fun_prop))).compose
      preparedPlan_poly)

def rowMask (p : Benes.BatchPlan TargetTag × List Bool) : List Bool :=
  (Benes.buildBatch targetWordRows p).map Benes.queryBit

theorem rowMask_poly : Poly rowMask :=
  (Benes.buildBatch_poly (([],[]),false,[],[]) targetWordRows targetWordRows_poly).compose
    (Poly.maps _ Benes.queryBit_poly)

/-- The global regime supplies the CRT seed. A fixed high row supplies its
own prefix bits, so its machine computes the whole control vector. -/
theorem mask_has {X : Type} {r : Regime X} (A : X → ℕ) (hA : r.Has (tally ∘ A))
    {seed : X → Seed} (hs : r.Has seed) :
    (fixedRowRegime r A hA).Has (fun z => rowMask ((prepare (seed z.1)).2,List.ofFn (Controlled.prefixBit z.2))) :=
  ((fixedRowGlobal A hA (hs.thenDo prepare_poly.sndCompose)).pair (fixedRowBits A hA)).thenDo rowMask_poly

theorem prepare_has {X : Type} {r : Regime X} {seed : X → Seed} (hs : r.Has seed) :
    r.Has (prepare ∘ seed) := hs.thenDo prepare_poly

end CRTTable.Native

end NearSquareRoot
end Computability
end OAI

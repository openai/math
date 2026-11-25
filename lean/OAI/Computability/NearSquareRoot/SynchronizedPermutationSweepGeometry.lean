import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveSeed

/-! # Explicit dimensions at a variable-reserve Fourier pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1200000
namespace Benes.PackedBatchHeader

open IntegerMultiplication Code Staff Strip Carry Controlled ShortFourier.BatchWord

/-- Full width, prepared prefix width, guard parameter, live block count and low reserve. -/
abbrev Geometry := Tally × Tally × Tally × Tally × Tally
abbrev PlacedHeader := Geometry × Staging

private def params (X : Type) [Codec X] : Regime X := ⟨Code.size,send,Dom.base _⟩

private theorem scalar {X : Type} [Codec X] (f : X → Tally) (P : Poly f) :
    Realizes (params X) (fun x => (f x).length) := by
  change Poly (fun x : X => tally (f x).length)
  simpa only [recover_tally] using P

def geometry (x : Seed) : Geometry :=
  let k := x.1.2.2
  let G := x.1.2.1.2.length
  let low := x.1.2.1.1
  let b := x.2.2.length
  (k,tally (k.length-(2*((b+1)*G)+low.length)),tally (G-1),tally b,low)

theorem geometry_poly : Poly geometry := by
  have k : Poly (fun x : Seed => x.1.2.2) := by fun_prop
  have low : Poly (fun x : Seed => x.1.2.1.1) := by fun_prop
  have G := scalar (fun x : Seed => x.1.2.1.2) (by fun_prop)
  have b : Realizes (params Seed) (fun x => x.2.2.length) := by
    change Poly (fun x : Seed => tally x.2.2.length)
    simpa only [ruler,tally,List.map_const'] using
      (show Easy (fun x : Seed => ruler x.2.2) from Easy.ruler Easy.snd.sndCompose).poly
  have H := G.minused (.fix 1)
  have padded := (Realizes.fix 2).times ((b.plus (.fix 1)).times G)
  have high := (scalar _ k).minused (padded.plus (scalar _ low))
  exact k.pair (Regime.Has.pair (r := params Seed) high (Regime.Has.pair H (Regime.Has.pair b low)))

private def preparedGeometry (x : Seed) : PlacedHeader := (geometry x, prepare x)

private theorem preparedGeometry_poly : Poly preparedGeometry := geometry_poly.pair prepare_poly

/-- The single header contains all masks, relocations and the rulers used by
the physical rearrangement, including when the selected batch is empty. -/
def placedHeader (q : Tally × RowPass) : PlacedHeader :=
  preparedGeometry (rowSeed q.1.length q.2)

theorem placedHeader_poly : Poly placedHeader :=
  Code.Poly.compose (f := fun q : Tally × RowPass => rowSeed q.1.length q.2)
    (g := preparedGeometry) jointRowSeed_poly preparedGeometry_poly

theorem placedHeader_fixed (D : ℕ) : Poly (fun z : RowPass => placedHeader (tally D,z)) :=
  ((Code.Poly.const (tally D)).pair Code.Poly.identity).compose placedHeader_poly

/-- True dimensions are read from the full width, guard stride and the enumerated
active row length, even if the finite switch plan contains no entries. -/
theorem geometry_eq {k L : ℕ} (hb : BoxShape.Valid k L (CoprimeBox.box k)) (D : ℕ) (dir : Bool)
    (row : Tally) (side : Bool) (j β : ℕ) :
    let w := BoxFin.physicalWidth (box := CoprimeBox.box k)
    let b := (FieldDirectory.activeBlocks k β j w).length
    let G := guardWidth k
    let B := payloadBits D k
    let z : RowPass := ((dir,tally k,row),(side,tally j),tally β)
    placedHeader (tally D,z) =
      ((tally k,tally (k-(2*((b+1)*G)+B)),tally (G-1),tally b,tally B),fullHeader D z) := by
  dsimp only
  rw [placedHeader,tally_length,rowSeed_eq hb,preparedGeometry]
  apply Prod.ext
  · simp only [geometry,tally_length,List.length_ofFn]
  · exact congrArg prepare (rowSeed_eq hb D dir row side j β).symm

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI

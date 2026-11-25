import OAI.Computability.NearSquareRoot.SynchronizedPermutationPrepare
import OAI.Computability.NearSquareRoot.CRTControlledRowControls

/-! # Literal compiled switch controls and their action on every native Fourier record -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication Adic Code Strip Controlled Controlled.PermutationLayout BoxFin

/-- Read all controls from the batch header and the actual scanned address prefix. -/
def maskBits (q : Staging × List Bool) :=
  (buildBatch (Prod.fst : RawTable × List Bool → RawTable) (q.1.2,q.2)).map queryBit

@[fun_prop] theorem maskBits_poly : Poly maskBits := by
  exact ((show Poly (fun q : Staging × List Bool => (q.1.2,q.2)) by fun_prop).compose
    (buildBatch_poly [] Prod.fst Easy.fst.poly)).compose (Poly.maps queryBit queryBit_poly)

/-- Run the generated mask on the fixed-row regime of the actual rectangular sweep. -/
theorem maskBits_has {X : Type} {r : Regime X} (a : X → ℕ) (ha : r.Has (tally ∘ a))
    (header : X → Staging) (h : r.Has header) :
    (fixedRowRegime r a ha).Has fun z => maskBits (header z.1,List.ofFn (Controlled.prefixBit z.2)) :=
  ((fixedRowGlobal a ha h).pair (fixedRowBits a ha)).thenDo maskBits_poly

variable {p b G low L : ℕ} {box : List (ℕ × ℕ)} [∀ i, NeZero (modulus box i)]
  (hb : BoxShape.Valid (maskWidth p b G low) L box) (hd : 4 ≤ box.length)
  (tables : Fin (box.length/4) → RawTable) (active : Fin b → Fin (box.length/4))
  (hinj : Function.Injective active) (which : Fin (box.length/4) → ℕ) (stage : Bool × ℕ)
  (batch : ℕ) (wide : ∀ q, stage.2 < physicalWidth (box:=box) (active q))
  (selected : ∀ q, which (active q) = batch)
  (complete : ∀ j, which j = batch → stage.2 < physicalWidth (box:=box) j → ∃ q, active q = j)
  (pos : 0<G) (fit : low+2*((b+1)*G)+FieldDirectory.controlCount
    (physicalWidth (box:=box)) active stage.2 ≤ maskWidth p b G low)
  (cert : ∀ q, ∃ f : Equiv.Perm (Word (physicalWidth (box:=box) (active q))),
    RawRepresents f (tables (active q)))

include hinj wide selected complete pos fit cert in
/-- The two scanned position tables are inverse, and between the two permutations the
literal polynomial mask program performs precisely the prescribed block switches. -/
theorem native_seed :
    let w := physicalWidth (box:=box)
    let k := maskWidth p b G low
    let out := prepare (seed w tables active stage.1 stage.2 k G low)
    ∃ π : Equiv.Perm (Fin k), ∃ ctrl : Block 2 p → Fin b → Bool,
      out.1 = (Reflections.table π,Reflections.table π.symm) ∧
      (∀ z, maskBits (out,List.ofFn (Controlled.prefixBit z)) = List.ofFn (ctrl z)) ∧
      ∀ y, packedRecord hb hd (flatAddress 2 _ (naturalStage π ctrl y)) =
        batchStage which w (fun _ : Unit => tables) stage batch
          (packedRecord hb hd (flatAddress 2 _ y)) := by
  let w := physicalWidth (box:=box)
  let total := sum_physicalWidth hb hd
  obtain ⟨π,targ,others,out⟩ := prepare_spec w total active hinj tables stage.1 stage.2 wide pos fit
  let inv := fun (q : Fin (box.length/4)) (i : Fin (w q)) =>
    PermutationLayout.offset π G low b (packedPort hb hd ⟨q,i⟩)
  let ctrl := switchControl w tables active inv stage.1 stage.2 (p:=p)
  refine ⟨π,ctrl,congrArg Prod.fst out,?_,?_⟩
  · intro z
    rw [maskBits,out,buildBatch_plan]
    simp only [List.map_ofFn]
    rfl
  · exact execute_batch hb hd pos fit π which tables stage batch active wide selected complete targ others cert

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI

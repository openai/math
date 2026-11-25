import OAI.Computability.NearSquareRoot.SynchronizedPermutationPrepared
import OAI.Computability.NearSquareRoot.SynchronizedPermutationActivePorts

/-! # Generate both physical address permutations and every switch query from one batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication Code Controlled Controlled.PermutationLayout

/-- Direction and switch depth, low reserve and stride, total address width, the
emitted local switch tables, and the active block indices. -/
abbrev Seed := ((Bool × Tally) × (Tally × Tally) × Tally) × Directory × List Tally
abbrev Staging := (Reflections.Table × Reflections.Table) × BatchPlan RawTable

private def fields (x : Seed) :=
  FieldDirectory.batch ((widths x.2.1,x.1.1.2),x.2.2)

private theorem fields_poly : Poly fields :=
  (show Poly (fun x : Seed => ((widths x.2.1,x.1.1.2),x.2.2)) by fun_prop).compose FieldDirectory.batch_poly

private def placement (x : Seed) :=
  PermutationLayout.directory (x.1.2.2,x.1.2.1,
    ((fields x).map Prod.fst).flatten,((fields x).map Prod.snd).flatten)

private theorem placement_poly : Poly placement := by
  have a := (fields_poly.compose (Poly.maps _ (Easy.fst (X:=List Tally) (Y:=List Tally)).poly)).compose Easy.flatten.poly
  have b := (fields_poly.compose (Poly.maps _ (Easy.snd (X:=List Tally) (Y:=List Tally)).poly)).compose Easy.flatten.poly
  exact ((show Poly (fun x : Seed => x.1.2.2) by fun_prop).pair
    ((show Poly (fun x : Seed => x.1.2.1) by fun_prop).pair (a.pair b))).compose PermutationLayout.directory_poly

def prepare (x : Seed) : Staging :=
  let v := placement x
  (v.1, plan (x.1.1,(x.2.1,v.2),x.2.2))

@[fun_prop] theorem prepare_poly : Poly prepare := by
  have ctx := (show Poly (fun x : Seed => x.2.1) by fun_prop).pair placement_poly.sndCompose
  exact placement_poly.fstCompose.pair (((show Poly (fun x : Seed => x.1.1) by fun_prop).pair
    (ctx.pair (show Poly (fun x : Seed => x.2.2) by fun_prop))).compose plan_poly)

def seed {d b : ℕ} (w : Fin d → ℕ) (t : Fin d → RawTable) (sel : Fin b → Fin d)
    (side : Bool) (j k G low : ℕ) : Seed :=
  (((side,tally j),(tally low,tally G),tally k),
    List.ofFn (fun u => (tally (w u),t u)), List.ofFn fun q => tally (sel q).val)

variable {d b k G low : ℕ} (w : Fin d → ℕ) (total : ∑ q, w q = k) (sel : Fin b → Fin d)
  (inj : Function.Injective sel) (tables : Fin d → RawTable) (side : Bool) (j : ℕ) (wide : ∀ q, j < w (sel q))
  (pos : 0<G) (fit : low+2*((b+1)*G)+FieldDirectory.controlCount w sel j ≤ k)

include inj
set_option maxHeartbeats 1200000 in
/-- The actual emitted staging data spells the preparatory permutation and its inverse,
and all local switch details in the new physical prefix. Every live switch has its target
in the sparse bank and all its other inputs in the prefix. -/
theorem prepare_spec :
    ∃ π : Equiv.Perm (Fin k),
      (∀ q, π (targetPos pos fit q) = FieldDirectory.finitePort w total ⟨sel q,⟨j,wide q⟩⟩) ∧
      (∀ q (i : Fin (w (sel q))), i.val ≠ j →
        ∃ a, π (controlPos fit a) = FieldDirectory.finitePort w total ⟨sel q,i⟩) ∧
      prepare (seed w tables sel side j k G low) =
        ((Reflections.table π,Reflections.table π.symm),makePlan side j [] (w ∘ sel) (tables ∘ sel)
          (fun q i => PermutationLayout.offset π G low b (FieldDirectory.finitePort w total ⟨sel q,i⟩))) := by
  have ha := FieldDirectory.targetBank_injective w total sel j inj wide
  have hb := FieldDirectory.controlBank_injective w total sel j inj
  have hc := FieldDirectory.target_ne_control w total sel j wide
  obtain ⟨π,ht,hs,_,out⟩ := directory_spec ha hb hc pos fit
  refine ⟨π,ht,?_,?_⟩
  · intro q i hi
    obtain ⟨a,e⟩ := FieldDirectory.covered w total sel j q i hi
    exact ⟨a,(hs a).trans e⟩
  · have fs : fields (seed w tables sel side j k G low) = FieldDirectory.selectedRows w sel j := by
      simp [fields,seed,widths,FieldDirectory.selectedRows,List.map_ofFn,Function.comp_def]
    have place : placement (seed w tables sel side j k G low) =
         ((Reflections.table π,Reflections.table π.symm),List.ofFn fun j => tally (PermutationLayout.offset π G low b j)) := by
      unfold placement
      rw [fs,FieldDirectory.batch_targets w total sel j wide,FieldDirectory.batch_controls w total sel j wide]
      exact out
    rw [prepare,place]
    congr 1
    exact plan_eq w tables sel (fun q i => FieldDirectory.finitePort w total ⟨q,i⟩)
      (FieldDirectory.finitePort_val w total) _ side j

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI

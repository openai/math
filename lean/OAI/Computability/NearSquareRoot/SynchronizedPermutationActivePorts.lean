import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectoryOffsets

/-! # Physical target and control ports emitted for an active batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.FieldDirectory
open IntegerMultiplication Code
variable {d b k : ℕ} (w : Fin d → ℕ) (total : ∑ u, w u = k) (sel : Fin b → Fin d) (j : ℕ)

private def rest (u : Fin d) := (List.finRange (w u)).eraseIdx j

private theorem mem_rest (u : Fin d) (r : Fin (w u)) : r ∈ rest w j u ↔ r.val ≠ j := by
  rw [rest,List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨i,hi,hne,e⟩
    have hv : i = r.val := by simpa using congrArg Fin.val e
    exact hv ▸ hne
  · exact fun h => ⟨r.val,by simp,h,Fin.ext (by simp)⟩

private def remaining := (List.ofFn sel).sigma (rest w j)

def controlCount := (remaining w sel j).length

def controlBank (i : Fin (controlCount w sel j)) : Fin k :=
  finitePort w total ((remaining w sel j).get i)

def targetBank (wide : ∀ q, j < w (sel q)) (q : Fin b) : Fin k :=
  finitePort w total ⟨sel q,⟨j,wide q⟩⟩

theorem targetBank_injective (hsel : Function.Injective sel) (wide : ∀ q, j < w (sel q)) :
    Function.Injective (targetBank w total sel j wide) := by
  intro x y h
  exact hsel (congrArg Sigma.fst ((finitePort w total).injective h))

theorem controlBank_injective (hsel : Function.Injective sel) :
    Function.Injective (controlBank w total sel j) := by
  apply (finitePort w total).injective.comp
  apply List.nodup_iff_injective_get.mp
  apply List.Nodup.sigma
  · exact List.nodup_ofFn.mpr hsel
  · intro u
    exact (List.eraseIdx_sublist _ _).nodup (List.nodup_finRange _)

theorem target_ne_control (wide : ∀ q, j < w (sel q)) (q : Fin b) (i : Fin (controlCount w sel j)) :
    targetBank w total sel j wide q ≠ controlBank w total sel j i := by
  intro e
  have h := (finitePort w total).injective e
  have hm := (remaining w sel j).get_mem i
  rw [← h] at hm
  exact (mem_rest w j _ _).mp (List.mem_sigma.mp hm).2 rfl

theorem covered (q : Fin b) (r : Fin (w (sel q))) (hne : r.val ≠ j) :
    ∃ i, controlBank w total sel j i = finitePort w total ⟨sel q,r⟩ := by
  have hm : ⟨sel q,r⟩ ∈ remaining w sel j :=
    List.mem_sigma.mpr ⟨List.mem_ofFn.mpr ⟨q,rfl⟩,(mem_rest w j _ _).mpr hne⟩
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
  exact ⟨i,congrArg (finitePort w total) hi⟩

theorem controlCount_eq (wide : ∀ q, j < w (sel q)) :
    controlCount w sel j = ∑ q, (w (sel q)-1) := by
  simp only [controlCount,remaining,List.sigma,List.length_flatMap,List.length_map,List.map_ofFn,
    Function.comp_apply,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro q _
  rw [rest,List.length_eraseIdx_of_lt (by simpa using wide q),List.length_finRange]

def selectedRows :=
  batch ((List.ofFn (fun u => tally (w u)), tally j), List.ofFn (fun q => tally (sel q).val))

private theorem selectedRows_eq (wide : ∀ q, j < w (sel q)) :
    selectedRows w sel j = List.ofFn fun q =>
      ([tally (targetBank w total sel j wide q).val],
        (rest w j (sel q)).map (fun r => tally (position w (sel q) r))) := by
  unfold selectedRows
  rw [show (List.ofFn fun q => tally (sel q).val) = (List.ofFn sel).map (fun x => tally x.val)
    by simp [Function.comp_def], batch_eq,List.map_ofFn]
  apply congrArg List.ofFn
  funext q
  change split (tally j,List.ofFn (fun i => tally (position w (sel q) i))) = _
  rw [split_active _ _ (by simpa using wide q)]
  simp only [targetBank,finitePort_val,List.getElem_ofFn,Prod.mk.injEq,true_and]
  rw [← List.eraseIdx_eq_take_drop_succ,List.ofFn_eq_map,List.eraseIdx_map]
  rfl

theorem batch_targets (wide : ∀ q, j < w (sel q)) :
    ((selectedRows w sel j).map Prod.fst).flatten =
      List.ofFn (fun q => tally (targetBank w total sel j wide q).val) := by
  rw [selectedRows_eq w total sel j wide]
  simp only [List.ofFn_eq_map,List.map_map]
  induction List.finRange b with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem batch_controls (wide : ∀ q, j < w (sel q)) :
    ((selectedRows w sel j).map Prod.snd).flatten =
      List.ofFn (fun i => tally (controlBank w total sel j i).val) := by
  rw [selectedRows_eq w total sel j wide]
  have image : List.ofFn (fun i => tally (controlBank w total sel j i).val) =
      (remaining w sel j).map (fun z => tally (finitePort w total z).val) := by
    rw [← List.ofFn_get (remaining w sel j),List.map_ofFn]
    rfl
  rw [image]
  simp [remaining,List.sigma,List.flatMap,List.ofFn_eq_map,Function.comp_def]

end Benes.FieldDirectory

end NearSquareRoot
end Computability
end OAI

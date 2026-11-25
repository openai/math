import OAI.Computability.NearSquareRoot.CRTTableNumericPorts
import OAI.Computability.NearSquareRoot.SynchronizedPermutationActivePorts

/-! # Distinct natural bit ports for a physical CRT subbatch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable.Native
open IntegerMultiplication Code Benes.FieldDirectory

noncomputable section

abbrev Port {d : ℕ} (w : Fin d → ℕ) := (g : Fin d) × Fin (w g)

/-- External fields occur in descending axis order and MSF port order. -/
def externalSlots {d : ℕ} (w : Fin d → ℕ) (n : ℕ) : List (Port w) :=
  (CRTTree.controls n (List.finRange d)).reverse.sigma (fun g => List.finRange (w g))

theorem externalSlots_nodup {d : ℕ} (w : Fin d → ℕ) (n : ℕ) : (externalSlots w n).Nodup :=
by
  apply List.Nodup.sigma
  · simpa using (CRTTree.controls_sublist n _).nodup (List.nodup_finRange d)
  · exact fun _ => List.nodup_finRange _

theorem externalSlots_mem {d : ℕ} {w : Fin d → ℕ} {n : ℕ} (p : Port w) :
    p ∈ externalSlots w n ↔ p.1 ∉ Set.range (targetAxis d n) := by
  obtain ⟨g,i⟩ := p
  simp [externalSlots, mem_controls_iff_external]

theorem externalSlots_eq {d : ℕ} (w : Fin d → ℕ) (n : ℕ) :
    levelPositions w (List.finRange d) n =
      (externalSlots w n).map fun p => tally (fieldPosition w (List.finRange d) p.1 p.2) := by
  simp [levelPositions,selectionPositions,externalSlots,List.sigma,List.map_flatMap,List.ofFn_eq_map,
    List.map_map,Function.comp_def]

abbrev Chosen {d b n : ℕ} (sel : Fin b → Fin (targetOrder d n).length) (q : Fin b) :=
  targetAxis d n (targetRank d n (sel q))

/-- The remaining word ports of the selected fields, in batch order. -/
def localSlots {d b n : ℕ} (w : Fin d → ℕ) (sel : Fin b → Fin (targetOrder d n).length)
    (j : ℕ) : List (Port w) :=
  (List.ofFn (Chosen sel)).sigma fun g => (List.finRange (w g)).eraseIdx j

private theorem rest_mem {v : ℕ} (r : Fin v) (j : ℕ) :
    r ∈ (List.finRange v).eraseIdx j ↔ r.val ≠ j := by
  rw [List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨i,hi,hne,e⟩
    have hv : i = r.val := by simpa using congrArg Fin.val e
    exact hv ▸ hne
  · exact fun h => ⟨r.val,by simp,h,Fin.ext (by simp)⟩

theorem localSlots_mem {d b n : ℕ} {w : Fin d → ℕ} (sel : Fin b → Fin (targetOrder d n).length)
    (j : ℕ) (p : Port w) :
    p ∈ localSlots w sel j ↔ (∃ q, Chosen sel q = p.1) ∧ p.2.val ≠ j := by
  obtain ⟨g,i⟩ := p
  simp [localSlots,List.mem_sigma,rest_mem]

variable {d b k n : ℕ} (w : Fin d → ℕ) (total : ∑ g, w g = k)
    (sel : Fin b → Fin (targetOrder d n).length) (j : ℕ)

def controlSlots : List (Port w) := externalSlots w n ++ localSlots w sel j

def controls (i : Fin (controlSlots w sel j).length) : Fin k :=
  finitePort w total ((controlSlots w sel j).get i)

def targets (wide : ∀ q, j < w (Chosen sel q)) (q : Fin b) : Fin k :=
  finitePort w total ⟨Chosen sel q,⟨j,wide q⟩⟩

theorem targets_injective (hinj : Function.Injective sel) (wide : ∀ q, j < w (Chosen sel q)) :
    Function.Injective (targets w total sel j wide) :=
  targetBank_injective _ _ _ _ ((targetAxis_injective d n).comp ((targetRank d n).injective.comp hinj)) wide

theorem controls_injective (hinj : Function.Injective sel) : Function.Injective (controls w total sel j) := by
  apply (finitePort w total).injective.comp
  apply List.Nodup.injective_get
  apply List.nodup_append.mpr
  refine ⟨externalSlots_nodup _ _, ?_, ?_⟩
  · apply List.Nodup.sigma
    · exact List.nodup_ofFn.mpr ((targetAxis_injective d n).comp ((targetRank d n).injective.comp hinj))
    · intro g
      exact (List.eraseIdx_sublist _ _).nodup (List.nodup_finRange _)
  · intro x hx y hy he
    subst y
    obtain ⟨⟨q,hq⟩,_⟩ := (localSlots_mem sel j x).mp hy
    exact (externalSlots_mem x).mp hx ⟨_,hq⟩

theorem targets_ne_controls (wide : ∀ q, j < w (Chosen sel q)) (q : Fin b)
    (i : Fin (controlSlots w sel j).length) : targets w total sel j wide q ≠ controls w total sel j i := by
  intro h
  have eq := (finitePort w total).injective h
  have hm := (controlSlots w sel j).get_mem i
  rw [← eq] at hm
  rcases List.mem_append.mp hm with he | hl
  · exact (externalSlots_mem _).mp he ⟨_,rfl⟩
  · exact ((localSlots_mem _ _ _).mp hl).2 rfl

theorem controls_covers {p : Port w} (hp : p ∈ controlSlots w sel j) :
    ∃ i, controls w total sel j i = finitePort w total p := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
  exact ⟨i,congrArg (finitePort _ _) hi⟩

end
end CRTTable.Native

end NearSquareRoot
end Computability
end OAI

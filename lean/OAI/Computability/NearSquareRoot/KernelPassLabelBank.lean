import OAI.Computability.NearSquareRoot.KernelPassFrequency

/-! # Local row operations on many independently indexed labels
The row mixes and finite value tables are gathered and scattered by label.
Spectral conversion charges each physical check row exactly once. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Plan

variable {A h i o N K U : ℕ} {L : Type*}

def groupIndex (e : L ≃ Fin N) (w : ℕ) : L × Fin w ≃ Fin (N*w) :=
  (e.prodCongr (.refl _)).trans finProdFinEquiv

/-- Extract one label's row bank from the physical numbering. -/
def groupRows (e : L × Fin i ≃ Fin K) (v : L) (x : Bank A h K) : Bank A h i :=
  fun j => x (e (v,j))

/-- Group-local operations with no child transforms may be synthesized a row
at a time. The output enumeration is independent of the input enumeration. -/
def localGroups (ei : L × Fin i ≃ Fin K) (eo : L × Fin o ≃ Fin U)
    (p : L → Plan A i o) : Plan A K U :=
  collect U fun b =>
    let v := (eo.symm b).1
    let j := (eo.symm b).2
    (route (fun _ : Fin 1 => j)).seq ((p v).seq (route (fun k => ei (v,k))))

theorem groupRows_localGroups (ei : L × Fin i ≃ Fin K) (eo : L × Fin o ≃ Fin U)
    (p : L → Plan A i o) (v : L) (x : Bank A h K) :
    groupRows eo v ((localGroups ei eo p).applyAt h x) = (p v).applyAt h (groupRows ei v x) := by
  funext j
  simp [groupRows, localGroups, applyAt_collect, applyAt_seq, applyAt_route, Function.comp_def]
  rfl

theorem calls_localGroups (ei : L × Fin i ≃ Fin K) (eo : L × Fin o ≃ Fin U)
    (p : L → Plan A i o) (hp : ∀ v, (p v).calls = 0) :
    (localGroups ei eo p).calls = 0 := by
  simp [localGroups, calls, hp]

theorem groupRows_frequency (e : L × Fin i ≃ Fin K) (v : L) (x : Bank A h K) :
    groupRows e v (frequency x) = frequency (groupRows e v x) := rfl

/-- Apply the same row numbering separately in the left and right check banks. -/
def doubleIndex (e : L × Fin i ≃ Fin K) : L × Fin (i+i) ≃ Fin (K+K) :=
  ((Equiv.refl _).prodCongr finSumFinEquiv.symm).trans
    ((Equiv.prodSumDistrib _ _ _).trans ((e.sumCongr e).trans finSumFinEquiv))

theorem doubleIndex_left (e : L × Fin i ≃ Fin K) (v : L) (j : Fin i) :
    doubleIndex e (v,Fin.castAdd i j) = Fin.castAdd K (e (v,j)) := by
  change finSumFinEquiv ((e.sumCongr e) ((Equiv.prodSumDistrib _ _ _) (v,
    finSumFinEquiv.symm (finSumFinEquiv (.inl j))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem doubleIndex_right (e : L × Fin i ≃ Fin K) (v : L) (j : Fin i) :
    doubleIndex e (v,Fin.natAdd i j) = Fin.natAdd K (e (v,j)) := by
  change finSumFinEquiv ((e.sumCongr e) ((Equiv.prodSumDistrib _ _ _) (v,
    finSumFinEquiv.symm (finSumFinEquiv (.inr j))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem groupRows_append (e : L × Fin i ≃ Fin K) (v : L) (x z : Bank A h K) :
    groupRows (doubleIndex e) v (Fin.append x z) = Fin.append (groupRows e v x) (groupRows e v z) := by
  funext j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;>
    simp only [groupRows, doubleIndex_left, doubleIndex_right, Fin.append_left, Fin.append_right]

theorem groupRows_leftPart (e : L × Fin i ≃ Fin K) (v : L) (x : Bank A h (K+K)) :
    groupRows e v (leftPart x) = leftPart (groupRows (doubleIndex e) v x) := by
  funext j
  simp only [groupRows, leftPart, Function.comp_apply, doubleIndex_left]

theorem groupRows_rightPart (e : L × Fin i ≃ Fin K) (v : L) (x : Bank A h (K+K)) :
    groupRows e v (rightPart x) = rightPart (groupRows (doubleIndex e) v x) := by
  funext j
  simp only [groupRows, rightPart, Function.comp_apply, doubleIndex_right]

/-- Share the two bank conversions across local tables with label-specific
per-column signature queries. -/
def groupTable {m : ℕ} (e : L × Fin i ≃ Fin K) (test : L → Column A → Fin m → ZMod 2)
    (T : (Fin m → ZMod 2) → Fin i → Fin i → Coefficient) : Plan A K K :=
  (convertBank A K).seq ((localGroups e e (fun v => matrixTable (test v) T)).seq (convertBank A K))

theorem calls_groupTable {m : ℕ} (e : L × Fin i ≃ Fin K)
    (test : L → Column A → Fin m → ZMod 2) (T : (Fin m → ZMod 2) → Fin i → Fin i → Coefficient) :
    (groupTable e test T).calls = K*A+K*A := by
  simp only [groupTable, calls, calls_convertBank, calls_localGroups _ _ _ (fun _ => calls_matrixTable ..),
    zero_add]

theorem groupRows_groupTable {m : ℕ} (e : L × Fin i ≃ Fin K)
    (test : L → Column A → Fin m → ZMod 2) (T : (Fin m → ZMod 2) → Fin i → Fin i → Coefficient)
    (v : L) (x : Bank A h K) :
    groupRows e v ((groupTable e test T).applyAt h x) =
      (spectralTable (test v) T).applyAt h (groupRows e v x) := by
  simp only [groupTable, spectralTable, applyAt_seq, applyAt_convertBank,
    groupRows_frequency, groupRows_localGroups]

end KernelPass.Plan

end NearSquareRoot
end Computability
end OAI

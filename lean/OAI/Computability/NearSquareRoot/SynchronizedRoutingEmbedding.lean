import OAI.Computability.NearSquareRoot.SynchronizedRoutingTable

/-! # Completing the active pairs specified by an injective address placement -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RoutingTable

/-- Active endpoint rows of a batch in the supplied spectator enumeration. -/
def activePairs {m n : ℕ} (e : Fin 2 × Fin m ↪ Fin n) : List (Fin n × Fin n) :=
  List.ofFn (fun i => (e (0,i),e (1,i)))

private def interleaved {m : ℕ} : Fin (m*2) ≃ Fin 2 × Fin m :=
  finProdFinEquiv.symm.trans (Equiv.prodComm ..)

theorem activePairs_nodup {m n : ℕ} (e : Fin 2 × Fin m ↪ Fin n) :
    (endpoints (activePairs e)).Nodup := by
  have ht : endpoints (activePairs e) = List.ofFn (fun j : Fin (m*2) => e (interleaved j)) := by
    apply List.ext_getElem?; intro j
    by_cases hj : j < m*2
    · let r : Fin (m*2) := ⟨j,hj⟩
      obtain ⟨⟨b,i⟩,hr⟩ := interleaved.symm.surjective r
      have he : 2*i.val+b.val = j := by
        simpa [interleaved,finProdFinEquiv,Nat.add_comm] using congrArg Fin.val hr
      let i' : Fin (activePairs e).length := ⟨i.val,by simp [activePairs]⟩
      have hp := endpoints_get (activePairs e) i' b
      change (endpoints (activePairs e))[2*i.val+b.val]? = _ at hp
      rw [he] at hp
      rw [hp,List.getElem?_eq_getElem (by simpa using hj), List.getElem_ofFn]
      change _ = some (e (interleaved r))
      rw [← hr, Equiv.apply_symm_apply]
      fin_cases b <;> simp [activePairs,i']
    · rw [List.getElem?_eq_none (by simp [activePairs,Nat.mul_comm];omega),
        List.getElem?_eq_none (by simp;omega)]
  rw [ht,List.nodup_ofFn]
  exact e.injective.comp interleaved.injective

theorem pairAt {m n : ℕ} (e : Fin 2 × Fin m ↪ Fin n) (he : Even n) (b : Fin 2) (i : Fin m) :
    ∃ hi : i.val < n/2,
      matching he (activePairs e) (activePairs_nodup e) (b,⟨i.val,hi⟩) = e (b,i) := by
  let i' : Fin (activePairs e).length := ⟨i.val,by simp [activePairs]⟩
  obtain ⟨hi,h⟩ := matching_active he (activePairs e) (activePairs_nodup e) i' b
  refine ⟨hi,?_⟩
  rw [show (⟨i.val,hi⟩ : Fin (n/2)) = ⟨i'.val,hi⟩ from rfl,h]
  fin_cases b <;> simp [activePairs,i']

end ShortFourier.RoutingTable

end NearSquareRoot
end Computability
end OAI

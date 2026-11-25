import OAI.Computability.BorderVNP.FragmentBucketLayout

/-! # Running a native counting-sort pass over its actual finite input bound -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Start the actual loop index at zero; the pass body advances it by one. -/
def forEach (idx limit : Reg) (step : Code) : Code :=
  (Code.constant idx 0).seq (.whileLt idx limit step)

/-- Execute a complete bounded native pass with a common constant row charge. -/
theorem forEach_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (idx limit : Reg) (step : Code) (n ticks : ℕ) (I : ℕ → NatState → Prop)
    (s : Bank w) (m : Memory w)
    (init : I 0 ((Code.constant idx 0).fixedEval (readings pub) (.ofWords s m)))
    (fields : ∀ i z, I i z → z.reg idx = i ∧ z.reg limit = n)
    (advance : ∀ i : Fin n, ∀ t : Bank w, ∀ mt : Memory w, I i.val (.ofWords t mt) →
      BoundedRun pub macros step t mt ticks (I (i.val+1))) :
    BoundedRun pub macros (forEach idx limit step) s m (2+n*(ticks+1)) (I n) := by
  have zero := (Code.constant idx 0).runFixed pub macros s m (by
    simp [Code.fixedSafe,Code.safeReadOnly])
  obtain ⟨es,t,mt,first,hcost,eq⟩ := zero
  obtain ⟨fs,u,mu,rest,done,sc⟩ := Transmission.loop_runs idx limit step n (fun _ => ticks)
    (fun i t mt => I i (.ofWords t mt)) (fun i t mt => fields i (.ofWords t mt))
    (fun i hi t mt h => by obtain ⟨fs,u,mu,hr,ht,hp⟩ := advance ⟨i,hi⟩ t mt h; exact ⟨fs,u,mu,hr,hp,ht⟩)
    0 (Nat.zero_le _) t mt (eq ▸ init)
  refine ⟨es++fs,u,mu,.seq first rest,?_,done⟩
  change traceCost es ≤ 1 at hcost
  rw [Transmission.cost_append]
  simp only [Nat.Ico_zero_eq_range,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at sc
  omega

end FragmentBucket

end BorderVNP
end Computability
end OAI

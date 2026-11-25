import OAI.Hierarchy.DescentPackedPhaseResident

namespace OAI
/-! # Bit selectors of the fixed global ordinary-stage ROM calendar -/

namespace Hierarchy.DescentPackedColony.Phase.Arena
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {n w W : ℕ} {Pin : Type*}

/-- Ordinary epoch blocks, including all temporary and output buffers, can
be allocated before any stage has selected its multiplier or paint. -/
def prefixStart (base : ℕ) (size : Fin n→ℕ) (i : Fin n) :=
  base+∑j : Fin n,if j < i then size j else 0

theorem prefix_disjoint (base : ℕ) (size : Fin n→ℕ) (i j : Fin n) (before : i<j) :
    prefixStart base size i+size i≤prefixStart base size j := by
  have term (u : Fin n) : (if u < i then size u else 0)+(if u=i then size u else 0)≤(if u<j then size u else 0) := by
    by_cases same:u=i
    · subst u;simp [before]
    by_cases lower:u < i
    · simp [lower,same,lower.trans before]
    · simp [lower,same]
  have all:=Finset.sum_le_sum (s:=Finset.univ) (fun u _=>term u)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at all
  dsimp [prefixStart];omega

/-- Each bit of the complete original RAM header is one original external
bit or one fixed Boolean, uniformly over the later choices. -/
def schedulePin (schedule : Fin n→Image w) (bits : Word w→Fin W→Bool) (old : ℕ→Fin W→Pin ⊕ Bool)
    (address : ℕ) (bit : Fin W) : Pin ⊕ Bool :=
  if hit : ∃i,(schedule i).low≤address ∧ address<(schedule i).stop then .inr (bits ((schedule hit.choose).value address) bit)
  else old address bit

theorem schedulePin_at (schedule : Fin n→Image w) (bits : Word w→Fin W→Bool) (old : ℕ→Fin W→Pin ⊕ Bool)
    (raw : (Pin→Bool)→Memory w) (faithful : ∀sel u v,Sum.elim sel id (old u v)=bits (raw sel u) v)
    (sel : Pin→Bool) (address : ℕ) (bit : Fin W) :
    Sum.elim sel id (schedulePin schedule bits old address bit)=
      bits (mountSchedule schedule (raw sel) address) bit := by
  unfold mountSchedule schedulePin
  split <;> simp_all

/-- An initial finite source extent is exact when every future roster table
lies below it and the original public input is zero beyond it. -/
theorem schedule_initialMemory (schedule : Fin n→Image w) (old : Memory w) (length : ℕ)
    (bounded : ∀i,(schedule i).stop≤length) (outside : ∀z,length≤z→ old z=0) :
    initialMemory length (mountSchedule schedule old)=mountSchedule schedule old := by
  funext z
  by_cases h:z<length
  · simp [initialMemory,h]
  · have keep := schedule_frame schedule old z (fun i=>Or.inr ((bounded i).trans (Nat.le_of_not_gt h)))
    simp [initialMemory,h,keep,outside _ (Nat.le_of_not_gt h)]

end
end Hierarchy.DescentPackedColony.Phase.Arena

end OAI

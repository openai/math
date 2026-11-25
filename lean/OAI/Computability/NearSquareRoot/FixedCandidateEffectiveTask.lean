import OAI.Computability.NearSquareRoot.FixedCandidateGuard
import OAI.Computability.NearSquareRoot.FixedCandidateFrame
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect

/-! # Effective families with simultaneous time and live-stack bounds -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveBoundedTask

open IntegerMultiplication Code CommonRegisters GeneratorSyntax Space Filter

/-- The bounded task contract for one specified command. -/
def Runs {I : Type*} (c : Cmd) (t s : I → ℕ) (u v : I → Tree) : Prop :=
  ∃ C, ∀ i env r base, (∀ a, (letters r a).length ≤ base) →
    BoundedFits env c (pile 0 (u i) r) (pile 0 (v i) r)
      (C*(t i+1)) (base+C*(s i+1)) (C*(s i+1))

/-- The program file is computed from the outer parameter. Its register names
have a common bound even though its complexity constant may vary by parameter. -/
def Family {P : Type} [Primcodable P] {I : P → Type}
    (t s : ∀ p, I p → ℕ) (u v : ∀ p, I p → Tree) : Prop :=
  ∃ (c : P → Cmd) (R : ℕ), Effective ltr c ∧ 0 < R ∧
    ∀ p, Within R (c p) ∧ Runs (c p) (t p) (s p) (u p) (v p)

namespace Runs

variable {I : Type} {c d : Cmd} {t s : I → ℕ} {u v w z : I → Tree}

theorem task (h : Runs c t s u v) : BoundedTask t s u v := ⟨c,h⟩

theorem sequence (f : Runs c t s u v) (g : Runs d t s v w) : Runs (c.join d) t s u w :=
  command_contract (c.join d) from FixedCandidate.sequence f.task g.task

theorem pairCalls (ht : ∀ i, s i ≤ t i) (f : Runs c t s u v) (g : Runs d t s w z)
    (room : ∀ i, (w i).count ≤ 75000*(s i+1) ∧ (v i).count ≤ 75000*(s i+1)) :
    Runs ((KernelEffectiveFamily.leftCmd c).join (KernelEffectiveFamily.rightCmd d)) t s
      (fun i => .fork (u i) (w i)) (fun i => .fork (v i) (z i)) :=
  command_contract ((KernelEffectiveFamily.leftCmd c).join (KernelEffectiveFamily.rightCmd d))
    from FixedCandidate.pairCalls ht f.task g.task room

theorem control {t s : I → ℕ} {u v : I → Tree} (tag : I → Bool)
    (hf : Runs c (fun i : {i // tag i = false} => t i.val) (fun i => s i.val)
      (fun i => u i.val) (fun i => v i.val))
    (ht : Runs d (fun i : {i // tag i = true} => t i.val) (fun i => s i.val)
      (fun i => u i.val) (fun i => v i.val)) :
    Runs (decodeBit c d) t (fun i => s i + (u i).count) (fun i => .fork (.atom (tag i)) (u i)) v :=
  command_contract (decodeBit c d) from BoundedTask.control tag hf.task ht.task

theorem bound {t' s' : I → ℕ} (h : Runs c t s u v) (T S : ℕ)
    (ht : ∀ i, t i+1 ≤ T*(t' i+1)) (hs : ∀ i, s i+1 ≤ S*(s' i+1)) :
    Runs c t' s' u v :=
  command_contract c from h.task.bound T S ht hs

theorem on {J : Type*} (h : Runs c t s u v) (f : J → I) :
    Runs c (t ∘ f) (s ∘ f) (u ∘ f) (v ∘ f) := by
  obtain ⟨C,h⟩ := h
  exact ⟨C,fun j => h (f j)⟩

theorem mono {t' s' : I → ℕ} (h : Runs c t s u v)
    (ht : ∀ i, t i ≤ t' i) (hs : ∀ i, s i ≤ s' i) : Runs c t' s' u v :=
  h.bound 1 1 (fun i => by simpa using ht i) (fun i => by simpa using hs i)

theorem of_time (h : ∃ C, ∀ x env, Fits.value env c 0 (u x) (v x) (C*(t x+1))) :
    Runs c t (fun i => (u i).count+t i) u v :=
  command_contract c from BoundedTask.of_time (show Task t u v from ⟨c,h⟩)

end Runs

namespace Family

variable {P : Type} [Primcodable P] {I J : P → Type} {t s : ∀ p, I p → ℕ}
  {u v w z : ∀ p, I p → Tree}

theorem fixed_run (c : Cmd) (h : ∀ p, Runs c (t p) (s p) (u p) (v p)) : Family t s u v := by
  obtain ⟨R,hR,hr⟩ : ∃ R, 0 < R ∧ Within R c :=
    ((eventually_gt_atTop (0:ℕ)).and (RegisterSelect.within_eventually c)).exists
  exact ⟨fun _ => c,R,effective_const _ _,hR,fun p => ⟨hr,h p⟩⟩

/-- A single task on all indices and inputs supplies a constant emitter. -/
theorem joint (h : BoundedTask (fun x : Sigma I => t x.1 x.2) (fun x => s x.1 x.2)
    (fun x => u x.1 x.2) (fun x => v x.1 x.2)) : Family t s u v := by
  obtain ⟨c,C,hc⟩ := h
  exact fixed_run c fun p => ⟨C,fun i => hc ⟨p,i⟩⟩

theorem on (h : Family t s u v) (f : ∀ p, J p → I p) :
    Family (fun p => t p ∘ f p) (fun p => s p ∘ f p)
      (fun p => u p ∘ f p) (fun p => v p ∘ f p) := by
  obtain ⟨c,R,he,hR,hc⟩ := h
  exact ⟨c,R,he,hR,fun p => ⟨(hc p).1,(hc p).2.on (f p)⟩⟩

theorem conform {t' s' : ∀ p, I p → ℕ} {u' v' : ∀ p, I p → Tree} (h : Family t s u v)
    (ht : ∀ p i, t p i = t' p i) (hs : ∀ p i, s p i = s' p i)
    (hu : ∀ p i, u p i = u' p i) (hv : ∀ p i, v p i = v' p i) : Family t' s' u' v' :=
  (funext (fun p => funext (ht p))) ▸ (funext (fun p => funext (hs p))) ▸
    (funext (fun p => funext (hu p))) ▸ (funext (fun p => funext (hv p))) ▸ h

theorem mono {t' s' : ∀ p, I p → ℕ} (h : Family t s u v)
    (ht : ∀ p i, t p i ≤ t' p i) (hs : ∀ p i, s p i ≤ s' p i) : Family t' s' u v := by
  obtain ⟨c,R,he,hR,hc⟩ := h
  exact ⟨c,R,he,hR,fun p => ⟨(hc p).1,(hc p).2.mono (ht p) (hs p)⟩⟩

theorem sequence (f : Family t s u v) (g : Family t s v w) : Family t s u w := by
  obtain ⟨c,R,ce,hR,hc⟩ := f
  obtain ⟨d,S,de,_,hd⟩ := g
  exact ⟨fun p => (c p).join (d p),max R S,ce.join de,hR.trans_le (le_max_left ..),
    fun p => ⟨⟨RegisterSelect.within_mono (le_max_left ..) _ (hc p).1,
      RegisterSelect.within_mono (le_max_right ..) _ (hd p).1⟩,(hc p).2.sequence (hd p).2⟩⟩

theorem pairCalls (h : ∀ p i, s p i ≤ t p i) (f : Family t s u v) (g : Family t s w z)
    (room : ∀ p i, (w p i).count ≤ 75000*(s p i+1) ∧ (v p i).count ≤ 75000*(s p i+1)) :
    Family t s (fun p i => .fork (u p i) (w p i)) (fun p i => .fork (v p i) (z p i)) := by
  obtain ⟨c,R,ce,_,hc⟩ := f
  obtain ⟨d,S,de,_,hd⟩ := g
  let W := max 3 (max R S)
  have h₃ : 3 ≤ W := le_max_left ..
  have rW : R ≤ W := (le_max_left R S).trans (le_max_right ..)
  have sW : S ≤ W := (le_max_right R S).trans (le_max_right ..)
  refine ⟨_,W,(KernelEffectiveFamily.effective_left ce).join (KernelEffectiveFamily.effective_right de),
    by omega,fun p => ⟨⟨?_,?_⟩,(hc p).2.pairCalls (h p) (hd p).2 (room p)⟩⟩
  · exact KernelEffectiveFamily.within_left (by omega) (RegisterSelect.within_mono rW _ (hc p).1)
  · exact KernelEffectiveFamily.within_right h₃ (RegisterSelect.within_mono sW _ (hd p).1)

theorem control (tag : ∀ p, I p → Bool)
    (hf : Family (fun p (i : {i // tag p i = false}) => t p i.val) (fun p i => s p i.val)
      (fun p i => u p i.val) (fun p i => v p i.val))
    (ht : Family (fun p (i : {i // tag p i = true}) => t p i.val) (fun p i => s p i.val)
      (fun p i => u p i.val) (fun p i => v p i.val)) :
    Family t (fun p i => s p i+(u p i).count) (fun p i => .fork (.atom (tag p i)) (u p i)) v := by
  obtain ⟨c,R,ce,hR,hc⟩ := hf
  obtain ⟨d,S,de,_,hd⟩ := ht
  let W := max R S
  have hp : 0 < W := hR.trans_le (le_max_left ..)
  refine ⟨fun p => decodeBit (c p) (d p),W,?_,hp,fun p => ⟨?_,(hc p).2.control (tag p) (hd p).2⟩⟩
  · apply KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
    apply KernelEffectiveFamily.effective_splitRoot _ _ (effective_const _ _)
    intro b
    cases b
    · exact ce
    · exact de
  · apply RegisterWitness.splitRoot_within.mpr
    refine ⟨hp,trivial,trivial,RegisterWitness.splitRoot_within.mpr ⟨hp,?_,?_,trivial⟩⟩
    · exact RegisterSelect.within_mono (le_max_left ..) _ (hc p).1
    · exact RegisterSelect.within_mono (le_max_right ..) _ (hd p).1

end Family
end EffectiveBoundedTask

end NearSquareRoot
end Computability
end OAI

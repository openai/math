import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveHeader
import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineWidthRestore
import OAI.Computability.NearSquareRoot.BoundedProductRight

/-! # Retaining the short directory header through generated batch programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveBoundedTask

open IntegerMultiplication Code CommonRegisters GeneratorSyntax Space
open InterchangeROMAddress.Affine

variable {P : Type} [Primcodable P] {I : P → Type}
variable {t s : ∀ p, I p → ℕ} {u v w z header : ∀ p, I p → Tree}

/-- Park a first field while a generated command acts on the second. Only the
parked field crosses the two auxiliary registers. -/
theorem Family.right (h : Family t s u v) (f : ∀ p, I p → Tree) :
    Family (fun p i => (f p i).count + t p i) (fun p i => s p i + (f p i).count)
      (fun p i => .fork (f p i) (u p i)) (fun p i => .fork (f p i) (v p i)) := by
  obtain ⟨c,R,e,_,hc⟩ := h
  exact ⟨_,max 3 R,KernelEffectiveFamily.effective_right e,by omega,fun p => ⟨
    KernelEffectiveFamily.within_right (le_max_left ..) (RegisterSelect.within_mono (le_max_right ..) _ (hc p).1),
    command_contract (KernelEffectiveFamily.rightCmd (c p)) from (hc p).2.task.right (f p)⟩⟩

private theorem bare_count (x : Tree) :
    (letters (pile 0 x (fun _ => [])) 0).length = x.count := by
  rw [letters_here,List.length_append,Tree.spell_length]
  rfl

/-- Preserve the header consumed by a named command. The space of the original command
already covers the stored header, input and output, as witnessed by its endpoints. -/
theorem Runs.retainHeader {J : Type} {c : Cmd} {clock arena : J → ℕ} {h x y : J → Tree}
    (run : Runs c clock arena (fun i => .fork (h i) (x i)) y) :
    Runs (restoring c) (fun i => (h i).count + clock i) arena
      (fun i => .fork (h i) (x i)) (fun i => .fork (h i) (y i)) := by
  obtain ⟨C,hc⟩ := run
  refine ⟨100*(C+1),fun i env d b hd => ?_⟩
  let u : Usage := ⟨C*(clock i+1),C*(arena i+1),C*(arena i+1)⟩
  have inner := restoring_bounded c (h i) (x i) (y i) u env (hc i env) d b hd
  obtain ⟨_,_,bare⟩ := hc i env (fun _ => []) 0 (fun _ => le_rfl)
  have first := bare.start 0
  have last := bare.finish 0
  rw [bare_count, Nat.zero_add] at first last
  change ((h i).fork (x i)).count ≤ C*(arena i+1) at first
  have head : (h i).count ≤ C*(arena i+1) := by simp only [Tree.count] at first; omega
  have ht : 100*(C+1)*((h i).count + clock i+1) =
      100*(h i).count + 100*(clock i+1) + 100*C*(h i).count + 100*(C*(clock i+1)) := by ring
  have hs : 100*(C+1)*(arena i+1) = 100*(C*(arena i+1))+100*(arena i+1) := by ring
  apply inner.mono
  · simp only [restoreUsage,u,ht]
    omega
  · simp only [restoreUsage,u,hs,Nat.add_le_add_iff_left,max_le_iff]
    omega
  · simp only [restoreUsage,u,hs,max_le_iff]
    omega

theorem within_restoring {c : Cmd} {R : ℕ} (hR : 3 ≤ R) (hc : Within R c) : Within R (restoring c) := by
  simp [restoring,parkHeader,returnHeader,RegisterWitness.splitRoot_within,Within,clone,move,forward,
    forwardBody,flood,pack,give,hc]
  omega

theorem Family.retainHeader (child : Family t s (fun p i => .fork (header p i) (u p i)) v) :
    Family (fun p i => (header p i).count + t p i) s
      (fun p i => .fork (header p i) (u p i)) (fun p i => .fork (header p i) (v p i)) := by
  obtain ⟨c,R,e,_,hc⟩ := child
  exact ⟨_,max 3 R,effective_restoring e,by omega,fun p => ⟨
    within_restoring (le_max_left ..) (RegisterSelect.within_mono (le_max_right ..) _ (hc p).1),
    (hc p).2.retainHeader⟩⟩

/-- Project the header for a primitive while the array remains parked. The primitive's
input endpoint supplies the array size bound in the original workspace. -/
theorem Family.projectHeader {childHeader : ∀ p, I p → Tree}
    (project : Family t s header childHeader)
    (child : Family t s (fun p i => .fork (childHeader p i) (u p i)) v) :
    Family t s (fun p i => .fork (header p i) (u p i)) v := by
  obtain ⟨c,R,e,hR,hc⟩ := project.left u
  obtain ⟨d,S,f,hS,hd⟩ := child
  have prepared : Family t s (fun p i => .fork (header p i) (u p i))
      (fun p i => .fork (childHeader p i) (u p i)) := by
    refine ⟨c,R,e,hR,fun p => ⟨(hc p).1,?_⟩⟩
    obtain ⟨C,run⟩ := (hd p).2
    apply (hc p).2.bound 1 (C+1) (fun _ => by simp)
    intro i
    obtain ⟨_,_,bare⟩ := run i [] (fun _ => []) 0 (fun _ => le_rfl)
    have cap := bare.start 0
    rw [bare_count,Nat.zero_add] at cap
    dsimp only [Tree.count] at cap
    dsimp only
    rw [Nat.succ_mul]
    omega
  exact prepared.sequence ⟨d,S,f,hS,hd⟩

/-- Run forward relocation, the masked stage, and backward relocation with one
physical copy of the original header at each call boundary. -/
theorem Family.threeStages (small : ∀ p i, (header p i).count ≤ t p i)
    (forward : Family t s (fun p i => .fork (header p i) (u p i)) v)
    (middle : Family t s (fun p i => .fork (header p i) (v p i)) w)
    (backward : Family t s (fun p i => .fork (header p i) (w p i)) z) :
    Family t s (fun p i => .fork (header p i) (u p i)) z := by
  have keep {a b : ∀ p, I p → Tree} (child : Family t s (fun p i => .fork (header p i) (a p i)) b) :
      Family t s (fun p i => .fork (header p i) (a p i)) (fun p i => .fork (header p i) (b p i)) := by
    obtain ⟨c,R,e,hR,hc⟩ := child.retainHeader
    exact ⟨c,R,e,hR,fun p => ⟨(hc p).1,(hc p).2.bound 2 1
      (fun i => by dsimp only; have := small p i; omega) (fun _ => by simp)⟩⟩
  exact ((keep forward).sequence (keep middle)).sequence backward

end EffectiveBoundedTask

end NearSquareRoot
end Computability
end OAI

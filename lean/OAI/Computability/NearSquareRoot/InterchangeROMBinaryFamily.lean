import OAI.Computability.NearSquareRoot.InterchangeROMBinaryInterface
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBank
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # Compiling the native binary rectangular program

The radix literal is attached to the compact geometry at the left of the
input, leaving the dense record stripe in place. The padding scan produces a
native request and keeps a compact ticket for the final cropping scan.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary.Family
open IntegerMultiplication Code Space CommonRegisters GeneratorSyntax KernelEffectiveFamily PhysicalWalsh

/-- Push a unary radix on the existing description. -/
def put (b : ℕ) : Cmd := (Task.prepare 0 (send (tally b))).join (pack 0)

/-- The radix and the native program are the two varying parts of this file. -/
def command (b : ℕ) (pre core post : Cmd) : Cmd :=
  (((leftCmd (put b)).join pre).join (rightCmd core)).join post

theorem effective {J : Type} [Primcodable J] {b : J → ℕ} {c : J → Cmd}
    (hb : Computable b) (hc : Effective ltr c) (pre post : Cmd) :
    Effective ltr (fun j => command (b j) pre (c j) post) := by
  have num : Effective ltr (fun j => Task.prepare 0 (send (tally (b j)))) := PhysicalWalshCompile.effective_tally_prepare.comp hb
  have literal := num.join (effective_const ltr (pack 0))
  exact (((effective_left literal).join (effective_const ltr pre)).join (effective_right hc)).join (effective_const ltr post)

theorem within {R : ℕ} {pre core post : Cmd} (r : 3 ≤ R)
    (hp : Within R pre) (hc : Within R core) (hq : Within R post) (b : ℕ) :
    Within R (command b pre core post) :=
  ⟨⟨⟨within_left (by omega) ⟨(RegisterWitness.prepare_within _).mpr (by omega),by exact (show 0 < R by omega)⟩,hp⟩,
    within_right r hc⟩,hq⟩

private theorem putRuns {I : Type} (b : ℕ) (h : I → Tree) :
    EffectiveBoundedTask.Runs (put b) (fun _ => 0) (fun i => (h i).count+0) h
      (fun i => .fork (send (tally b)) (h i)) := by
  apply EffectiveBoundedTask.Runs.of_time
  refine ⟨5*(send (tally b)).count+3,fun i env deck => ?_⟩
  apply ((Task.fits_prepare 0 (send (tally b)) env (pile 0 (h i) deck)).join
    (fits_pack (send (tally b)) (h i) deck 0 env)).mono
  omega

/-- Compose the exact named programs under any clock and arena. The saved
crop ticket is accounted for through the padding program's actual output. -/
theorem runs {I : Type} {T S : I → ℕ} (ht : ∀ i, S i ≤ T i) (b : ℕ)
    {pre core post : Cmd} {description stripe saved issue reply out : I → Tree}
    (decode : ClosedRuns pre T S (fun i => .fork (.fork (send (tally b)) (description i)) (stripe i))
      (fun i => .fork (saved i) (issue i)))
    (native : ClosedRuns core T S issue reply)
    (encode : ClosedRuns post T S (fun i => .fork (saved i) (reply i)) out) :
    ClosedRuns (command b pre core post) T S (fun i => .fork (description i) (stripe i)) out := by
  have first : EffectiveBoundedTask.Runs pre T S _ _ := decode
  have mid : EffectiveBoundedTask.Runs core T S _ _ := native
  obtain ⟨C,room⟩ := first.task.endpointSize
  have enough (i : I) : (description i).count+(stripe i).count ≤ C*(S i+1) ∧ (saved i).count ≤ C*(S i+1) := by
    have h := room i
    change max (((send (tally b)).count+(description i).count+1)+(stripe i).count+1)
      ((saved i).count+(issue i).count+1) ≤ C*(S i+1) at h
    omega
  have raw := AgendaOps.left (putRuns b description) stripe
  have add := raw.bound (t':=T) (s':=S) 1 (C+1) (fun _ => by simp)
    (fun i => by have h := (enough i).1;change (description i).count+0+(stripe i).count+1 ≤ _;rw [Nat.succ_mul];omega)
  have parked : EffectiveBoundedTask.Runs (rightCmd core) (fun i => (saved i).count+T i) (fun i => S i+(saved i).count)
      (fun i => .fork (saved i) (issue i)) (fun i => .fork (saved i) (reply i)) :=
    command_contract (rightCmd core) from mid.task.right saved
  have close := parked.bound (t':=T) (s':=S) (C+1) (C+1)
    (fun i => by have h : (saved i).count ≤ C*(T i+1) := (enough i).2.trans (Nat.mul_le_mul_left C (Nat.succ_le_succ (ht i)));rw [Nat.succ_mul];omega)
    (fun i => by have h := (enough i).2;rw [Nat.succ_mul];omega)
  exact ((add.sequence first).sequence close).sequence encode

/-- Generate a single uniformly register-bounded family from named native
requests and their two fixed physical adapters. No cost degree is used when
emitting the file. -/
theorem compile {J : Type} [Primcodable J] (b : J → ℕ) (hb : Computable b) (core : J → Cmd)
    (he : Effective ltr core) (R : ℕ) (hc : ∀ j, Within R (core j)) (pre post : Cmd)
    (ρ : J → ℝ) (D : J → ℕ) (nonneg : ∀ j, 0 ≤ ρ j)
    (saved issue reply : J → Packet → Tree)
    (decode : ∀ j, let S := Packet.mass (D j); let T x := time (ρ j) (S x) x.n
      ClosedRuns pre T S (fun x => .fork (.fork (send (tally (b j))) x.description) (IntegerMultiplication.Strip.stripe x.rows (send ∘ x.bits)))
        (fun x => .fork (saved j x) (issue j x)))
    (native : ∀ j, let S := Packet.mass (D j); let T x := time (ρ j) (S x) x.n
      ClosedRuns (core j) T S (issue j) (reply j))
    (encode : ∀ j, let S := Packet.mass (D j); let T x := time (ρ j) (S x) x.n
      ClosedRuns post T S (fun x => .fork (saved j x) (reply j x)) Packet.output) :
    ∃ M : ℕ, Effective ltr (fun j => command (b j) pre (core j) post) ∧
      ∀ j, Within M (command (b j) pre (core j) post) ∧ RectPhysical (command (b j) pre (core j) post) (ρ j) (D j) := by
  obtain ⟨M,hm,r,p,q⟩ := (Filter.eventually_ge_atTop 3 |>.and ((Filter.eventually_ge_atTop R).and
    ((RegisterSelect.within_eventually pre).and (RegisterSelect.within_eventually post)))).exists
  refine ⟨M,effective hb he pre post,fun j => ⟨within hm p (RegisterSelect.within_mono r _ (hc j)) q _,?_⟩⟩
  apply runs (b:=b j) _ (decode j) (native j) (encode j)
  intro x
  apply (Nat.cast_le (α:=ℝ)).mp
  exact (le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow
    (by exact_mod_cast Nat.le_add_left 1 x.n) (nonneg j))).trans (Nat.le_ceil _)

end InterchangeROMBinary.Family

end NearSquareRoot
end Computability
end OAI

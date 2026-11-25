import OAI.Computability.BorderVNP.DiagonalNativeSequence
import OAI.Computability.BorderVNP.RoutingISACallProof

/-! # External state after successful private cell calls

A private burst consumes choices and may reject or contribute a negative sign. On any
successful path it has the same effect on the external bank and memory as a no-op. This
lets the native subtotal and residue continuation see one fixed post-dispatch state for
all accepting choices made privately by the cells.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Erase the external event of a private call for the purpose of comparing post-states. -/
def Code.eraseCalls : Code → Code
  | .call .. => .nop
  | .seq a b => .seq a.eraseCalls b.eraseCalls
  | .ifEq x y a b => .ifEq x y a.eraseCalls b.eraseCalls
  | .ifLt x y a b => .ifLt x y a.eraseCalls b.eraseCalls
  | .choose a b => .choose a.eraseCalls b.eraseCalls
  | .whileLt x y a => .whileLt x y a.eraseCalls
  | c => c

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Erasing successful calls preserves the exact final registers and external words.
The erased program is only used to compare states of already returning native paths. -/
theorem Runs.eraseCalls {c : Code} {s m es t mt} (r : Runs pub mac c s m es t mt) :
    ∃ fs, Runs pub mac c.eraseCalls s m fs t mt := by
  induction r with
  | @atom c s m a t z bits hc ha hs =>
    have original := Runs.atom hc ha hs
    cases c <;> try exact ⟨_,original⟩
    case call =>
      obtain ⟨_,rfl,hm,_⟩ := CellDispatch.private_iff.mp original
      rw [hm]
      exact ⟨_,Runs.localStep m rfl rfl⟩
    all_goals simp [Code.isAtom] at hc
  | seq _ _ ih ih' =>
    obtain ⟨fs,a⟩ := ih
    obtain ⟨gs,b⟩ := ih'
    exact ⟨_,a.seq b⟩
  | ifEq _ ih =>
    obtain ⟨fs,h⟩ := ih
    exact ⟨_,.ifEq (by simpa only [apply_ite Code.eraseCalls] using h)⟩
  | ifLt _ ih =>
    obtain ⟨fs,h⟩ := ih
    exact ⟨_,.ifLt (by simpa only [apply_ite Code.eraseCalls] using h)⟩
  | choose bit _ ih =>
    obtain ⟨fs,h⟩ := ih
    exact ⟨_,.choose bit (by simpa only [apply_ite Code.eraseCalls] using h)⟩
  | whileDone h => exact ⟨_,.whileDone h⟩
  | whileStep g _ _ ih ih' =>
    obtain ⟨fs,a⟩ := ih
    obtain ⟨gs,b⟩ := ih'
    exact ⟨_,.whileStep g a b⟩

/-- All private directory outcomes on fixed input yield the same complete continuation
state, even when they have different tapes, runtimes and signs. -/
theorem CellDispatch.same_post {s m es t mt fs z mz} (r : Runs pub mac callOwnedCells s m es t mt)
    (r' : Runs pub mac callOwnedCells s m fs z mz) : t = z ∧ mt = mz := by
  obtain ⟨_,a⟩ := r.eraseCalls
  obtain ⟨_,b⟩ := r'.eraseCalls
  exact (a.unique_of_deterministic (by decide) b).2

end RoutingISA

end BorderVNP
end Computability
end OAI

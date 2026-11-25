import OAI.Computability.BorderVNP.CellProfileAux
import OAI.Computability.BorderVNP.CellTermCost

/-!
# Private flag blocks with local scope

A sparse row guesses its own auxiliary block, checks the flags, then restores
the data bank before the next row. All following instructions, including
arbitrary further guesses, keep their original addressing convention.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro (Op)
open scoped Classical

/-- A local scratch block around a private checker, encoded using two loops.
The loop bodies have constant description length. -/
def localFlags (len : ℕ) (checker : Stmt) : Stmt :=
  .seq (.loop (.lit len) (.fixed .guess))
    (.seq checker (.loop (.lit len)
      (.seq (.fixed (.literal false)) (.seq (.fixed .nand) (.fixed .guard)))))

/-- The loops expand to the actual nondeterministic pushes and deterministic pops. -/
theorem expand_localFlags (len : ℕ) (checker : Stmt) (env : List ℕ) :
    (localFlags len checker).expand env =
      List.replicate len .guess ++ checker.expand env ++ CellMacro.discardBlock len := by
  simp [localFlags, Stmt.expand, NatExpr.eval, CellMacro.discardBlock,
    List.flatMap_def, List.map_const', List.append_assoc]

/-- Allocating and discharging `len` flags adds exactly thirteen binary
instruction symbols per slot to the private stream. -/
theorem work_localFlags (len : ℕ) (checker : Stmt) (env : List ℕ) :
    work (localFlags len checker) env = work checker env + 13 * len := by
  simp [localFlags, work_loop, NatExpr.eval, CellMacro.Op.bits, List.map_const']
  omega

/-- If passing flags imply validity, and a valid data bank has exactly one
passing finite flag vector, the scoped checker is an ordinary multiplicity-one
guard. It leaves both the sign and the original wire bank intact. -/
theorem localFlags_checks (len : ℕ) (checker : Stmt) (env : List ℕ)
    (aux pass : (ℕ → Bool) → Prop) (hchecker : Profile.Tests checker env aux)
    (hsound : ∀ (v : List Bool) (x : Fin len → Bool), aux (lookup (List.ofFn x ++ v)) → pass (lookup v))
    (hunique : ∀ v : List Bool, pass (lookup v) → ∃! x : Fin len → Bool, aux (lookup (List.ofFn x ++ v))) :
    Profile.Tests (localFlags len checker) env pass := by
  intro ops f v
  obtain ⟨canonical, he⟩ : ∃ canonical : Fin len → Bool, ∀ x : Fin len → Bool,
      aux (lookup (List.ofFn x ++ v)) ↔ pass (lookup v) ∧ x = canonical := by
    by_cases h : pass (lookup v)
    · obtain ⟨c, hc, hu⟩ := hunique v h
      exact ⟨c, fun x => ⟨fun hx => ⟨h, hu x hx⟩, fun ⟨_, hx⟩ => hx.symm ▸ hc⟩⟩
    · exact ⟨fun _ => false, fun x => by simp [h, mt (hsound v x) h]⟩
  rw [expand_localFlags, CellMacro.value_uniqueBlock len canonical (pass (lookup v))]
  · by_cases h : pass (lookup v)
    · cases f
      simp [h]
    · simp [h, CellMacro.value_failed]
  · intro x tail
    simpa only [he] using hchecker tail f (List.ofFn x ++ v)

/-- Compact scoped checker for a complete profile record. Auxiliary arrays
are never carried across a record boundary. -/
def profileRow (copies : ℕ) (selector : Port) (w : ℕ) (hist : List ℕ) (routes : List Route) : Stmt :=
  let len := Profile.auxSize copies hist.length
  localFlags len (Profile.profileGen 0 len copies selector w hist routes)

/-- Exact semantics of the scoped profile generator under arbitrary continuations. -/
theorem profileRow_checks (copies : ℕ) (selector : Port) (w : ℕ) (hist : List ℕ)
    (routes : List Route) (env : List ℕ) :
    Profile.Tests (profileRow copies selector w hist routes) env
      (fun bank => profileValid bank copies selector w hist routes) := by
  apply localFlags_checks _ _ _ _ _ (Profile.profileGen_checks 0 (Profile.auxSize copies hist.length) copies selector w hist routes env)
  · intro v x h
    exact ((Profile.accept_stack_iff copies selector w hist routes v x).mp h).1
  · intro v h
    let c := Profile.canonicalAux (lookup v) copies hist.length selector w
    refine ⟨c, (Profile.accept_stack_iff ..).mpr ⟨h, rfl⟩, ?_⟩
    intro x hx
    exact ((Profile.accept_stack_iff ..).mp hx).2

end CellSparse

end BorderVNP
end Computability
end OAI

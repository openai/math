import OAI.Computability.NearSquareRoot.InterchangeSupportCompile
import OAI.Computability.NearSquareRoot.InterchangeAddress
import OAI.Computability.NearSquareRoot.InterchangeStageRoute

/-!
# Realizing full field permutations in the physical address domain

P192's square records the two field arrays and the prefix, gap and suffix.
Conjugating a field permutation by this square keeps all three spectators and
identifies its execution with the native recreation of its lag instructions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Support
open IntegerMultiplication.Port IntegerMultiplication.Loom IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic

variable {b : ℕ} [NeZero b] {J : Type} (P G B : Tape) {f : ℕ}

noncomputable def extendDomain (e : Equiv.Perm (Duplex J (Tower b f))) :
    Equiv.Perm (Keys P G B J (Block b f)) := Optic.field square e

@[simp] theorem square_extendDomain (e : Equiv.Perm (Duplex J (Tower b f)))
    (x : Keys P G B J (Block b f)) :
    square (extendDomain P G B e x) = (e (chase x), watcher x) := by
  simp only [extendDomain, Optic.field, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply]; rfl

@[simp] theorem chase_extendDomain (e : Equiv.Perm (Duplex J (Tower b f)))
    (x : Keys P G B J (Block b f)) : chase (extendDomain P G B e x) = e (chase x) :=
  congrArg Prod.fst (square_extendDomain P G B e x)

@[simp] theorem watcher_extendDomain (e : Equiv.Perm (Duplex J (Tower b f)))
    (x : Keys P G B J (Block b f)) : watcher (extendDomain P G B e x) = watcher x :=
  congrArg Prod.snd (square_extendDomain P G B e x)

@[simp] theorem extendDomain_refl : extendDomain P G B (Equiv.refl (Duplex J (Tower b f))) =
    Equiv.refl _ := by
  apply Equiv.ext; intro x; apply square.injective
  rw [square_extendDomain]; rfl

@[simp] theorem extendDomain_trans (d e : Equiv.Perm (Duplex J (Tower b f))) :
    (extendDomain P G B d).trans (extendDomain P G B e) = extendDomain P G B (d.trans e) := by
  apply Equiv.ext; intro x; apply square.injective
  simp

@[simp] theorem extendDomain_symm (d : Equiv.Perm (Duplex J (Tower b f))) :
    (extendDomain P G B d).symm = extendDomain P G B d.symm := by
  apply Equiv.ext; intro x; rfl

variable {L Bx Q H : Type} {r : Bx → Rectangle L}

/-- Lift the whole stage diagram, including its two commuting triangles, to
native addresses. -/
noncomputable def extendLayout (g : StageRoute.Layout r Q (Duplex J (Tower b f))) :
    StageRoute.Layout r Q (Keys P G B J (Block b f)) where
  S j v := extendDomain P G B (g.S j v)
  T j v := extendDomain P G B (g.T j v)
  C j k := extendDomain P G B (g.C j k)
  prepareSrc e := extendDomain P G B (g.prepareSrc e)
  prepareDst e := extendDomain P G B (g.prepareDst e)
  localSrc j e := extendDomain P G B (g.localSrc j e)
  localDst j e := extendDomain P G B (g.localDst j e)
  source_triangle j e := by simp only [extendDomain_trans, g.source_triangle]
  target_triangle j e := by simp only [extendDomain_trans, g.target_triangle]

@[simp] theorem extendLayout_perm {u v : H → L} (g : StageRoute.Layout r Q (Duplex J (Tower b f)))
    (op : StageRoute.Move r Q u v) :
    (extendLayout P G B g).perm op = extendDomain P G B (g.perm op) := by
  cases op with
  | idle => exact (extendDomain_refl P G B).symm
  | prepare | align => rfl
  | restore | unalign => exact extendDomain_symm _ _ _ _
  | gather _ term => rcases term with ⟨i,_ | q⟩ <;> rfl
  | distribute _ term => rcases term with ⟨i,_ | q⟩ <;> exact extendDomain_symm _ _ _ _

theorem extendLayout_diagonal (g : StageRoute.Layout r Q (Duplex J (Tower b f))) (j : Q) (x : L)
    {e : Equiv.Perm (Duplex J (Tower b f))} (h : (g.S j x).trans (g.T j x).symm = e) :
    ((extendLayout P G B g).S j x).trans ((extendLayout P G B g).T j x).symm =
      extendDomain P G B e := by
  change (extendDomain P G B _).trans (extendDomain P G B _).symm = _
  rw [extendDomain_symm, extendDomain_trans, h]

variable {n : ℕ} [DecidableEq J] (ord : J ≃ Fin n)

/-- The same paid legal list works for every address width and every choice
of spectator tapes. -/
theorem Runs.domain {k : ℕ} {E : (f : ℕ) → Duplex J (Tower b f) ≃ₗ[Tower b f] Duplex J (Tower b f)}
    (h : Runs (ranking ord) k E) :
    ∃ (ops : List (Lag J b)) (legal : ∀ u ∈ ops, u.legal (ranking ord)),
      (ops.map Lag.prices).sum ≤ k ∧ ∀ (P G B : Tape) (f : ℕ),
      recreation ord P G B f ops legal = extendDomain P G B (E f).toEquiv := by
  obtain ⟨ops,legal,price,eval⟩ := h
  refine ⟨ops,legal,price,fun P G B f => ?_⟩
  apply Equiv.ext; intro x; apply square.injective
  rw [fore, square_extendDomain, eval]; rfl

end Interchange.Support

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.NearSquareRoot.NamedPackedRate
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # A fixed binary decoder for named packed commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open NamedPacked Space CommonRegisters GeneratorSyntax

def branchCmd (pre left right : Cmd) := pre.join (decodeBit left right)

theorem effective_branchCmd {P : Type} [Primcodable P] {left right : P → Cmd}
    (pre : Cmd) (hl : Effective ltr left) (hr : Effective ltr right) :
    Effective ltr (fun p => branchCmd pre (left p) (right p)) := by
  apply (effective_const ltr pre).join
  apply KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
  apply KernelEffectiveFamily.effective_splitRoot _ _ (effective_const _ _)
  intro b; cases b <;> assumption

theorem within_branchCmd {pre left right : Cmd} {R : ℕ} (hR : 0 < R)
    (hp : Within R pre) (hl : Within R left) (hr : Within R right) :
    Within R (branchCmd pre left right) := by
  refine ⟨hp,RegisterWitness.splitRoot_within.mpr ⟨hR,trivial,trivial,?_⟩⟩
  exact RegisterWitness.splitRoot_within.mpr ⟨hR,hl,hr,trivial⟩

private theorem decodeAt {X : Type} (tag : X → Bool) (a : X → ℝ) (u v : X → Tree)
    (pos : ∀ x, 1 ≤ a x) (vol : Volume a (together (send ∘ tag) u))
    (left right : Cmd)
    (lc : CarriesAt left (a ∘ Subtype.val) (u ∘ Subtype.val) (v ∘ Subtype.val) (X := {x // tag x = false}))
    (rc : CarriesAt right (a ∘ Subtype.val) (u ∘ Subtype.val) (v ∘ Subtype.val) (X := {x // tag x = true})) :
    CarriesAt (decodeBit left right) a (together (send ∘ tag) u) v := by
  let t x := ⌈a x⌉₊
  have go : EffectiveTask.Runs (decodeBit left right) t (together (send ∘ tag) u) v :=
    command_contract (decodeBit left right) from
      Task.control tag (a := t) (f := u) (g := v) (show Task _ _ _ from ⟨left,lc.release⟩)
        (show Task _ _ _ from ⟨right,rc.release⟩)
  refine ⟨pos,⟨t,go,3,fun x => ?_⟩,vol⟩
  have h := Nat.ceil_lt_add_one (a := a x) (by linarith [pos x])
  change (⌈a x⌉₊ : ℝ)+1 ≤ 3*(a x)
  linarith [pos x]

/-- Choose the fixed decoder once. Only the two child commands depend on the
outer routing parameter. -/
theorem namedBranch {X : Type} {r : Regime X} {n w : X → ℕ} {u v : X → Tree}
    (tag : X → Bool) (prep : Rip r n w u (together (send ∘ tag) u)) :
    ∃ pre : Cmd, ∀ (rate : X → ℝ) (left right : Cmd),
      BreezeAt left (rate ∘ Subtype.val) (r.pull Subtype.val) (n ∘ Subtype.val) (w ∘ Subtype.val)
        (u ∘ Subtype.val) (v ∘ Subtype.val) (X := {x // tag x = false}) →
      BreezeAt right (rate ∘ Subtype.val) (r.pull Subtype.val) (n ∘ Subtype.val) (w ∘ Subtype.val)
        (u ∘ Subtype.val) (v ∘ Subtype.val) (X := {x // tag x = true}) →
      BreezeAt (branchCmd pre left right) rate r n w u v := by
  obtain ⟨pre,hpre⟩ := BreezeAt.launch (f:=fun _ => (1:ℝ)) prep (fun _ => le_rfl)
  refine ⟨pre,?_⟩
  intro rate left right hl hr
  have pos (x : X) : 1 ≤ rate x := by
    cases h : tag x
    · exact hl.1 ⟨x,h⟩
    · exact hr.1 ⟨x,h⟩
  obtain ⟨_,a,head⟩ := hpre.raise pos
  obtain ⟨_,b,l⟩ := hl
  obtain ⟨_,d,h⟩ := hr
  let D := a+b+d
  let budget := runrate rate r n w D
  have head' : CarriesAt pre budget u (together (send ∘ tag) u) :=
    head.larger (fun i => rate_higher i (pos i) (by dsimp [D]; omega))
  have l' : CarriesAt left (budget ∘ Subtype.val) _ _ (X:={x // tag x = false}) :=
    l.larger (fun i => rate_higher (r:=r) (n:=n) (l:=w) i.val (pos _) (by dsimp [D]; omega))
  have h' : CarriesAt right (budget ∘ Subtype.val) _ _ (X:={x // tag x = true}) :=
    h.larger (fun i => rate_higher (r:=r) (n:=n) (l:=w) i.val (pos _) (by dsimp [D]; omega))
  exact ⟨pos,D,head'.next (decodeAt tag budget u v head'.budget head'.forget.out left right l' h')⟩

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI

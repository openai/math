import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxTransition

/-! # Primitive recursiveness of compiled stack transitions

The control row is computed from the finite list of encoded sites and the finite
tuple of symbols at the stack heads. The row can then be projected to any individual
register by its numerical name.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Transition

variable {X : Type*} [Primcodable X]

private theorem primrec_fields : Primrec fields :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private theorem primrec_idx {B : Type*} [Primcodable B] [DecidableEq B] [BEq B] [LawfulBEq B] :
    Primrec₂ (fun (a : B) (l : List B) => l.idxOf a) := by
  apply Primrec.list_idxOf.of_eq
  intro a l
  induction l with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : b = a <;> simp_all

private theorem primrec_resolve : Primrec₂ resolve :=
  (Primrec.ite
    (Primrec.nat_lt.comp (primrec_idx.comp Primrec.snd Primrec.fst)
      (Primrec.list_length.comp Primrec.fst))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂

private theorem primrec_go : Primrec go :=
  Primrec.option_some.comp (Primrec.id.pair (Primrec.const none))

private theorem primrec_act {i : X → ℕ} {a : X → Option Symbol} {q : X → Option Site}
    (hi : Primrec i) (ha : Primrec a) (hq : Primrec q) :
    Primrec fun x => act (i x) (a x) (q x) :=
  Primrec.option_some.comp (hq.pair (Primrec.option_some.comp (hi.pair ha)))

private theorem primrec_getLeft : Primrec (Sum.getLeft? : Symbol → Option ℕ) :=
  (Primrec.sumCasesOn Primrec.id (Primrec.option_some.comp Primrec.snd).to₂
    (Primrec₂.const none)).of_eq (by rintro (a|s) <;> rfl)

private theorem primrec_getRight : Primrec (Sum.getRight? : Symbol → Option Site) :=
  (Primrec.sumCasesOn Primrec.id (Primrec₂.const none)
    (Primrec.option_some.comp Primrec.snd).to₂).of_eq (by rintro (a|s) <;> rfl)

private theorem primrec_ret : Primrec ret :=
  Primrec.option_bind
    ((Primrec.option_bind₁ primrec_getRight).comp
      ((Primrec.list_getD none).comp Primrec.id (Primrec.const 0)))
    (primrec_act (Primrec.const 0) (Primrec.const none)
      (Primrec.option_some.comp Primrec.snd)).to₂

private theorem primrec_elim {A B : Type*} [Primcodable A] [Primcodable B]
    {o : X → Option A} {z : X → B} {g : X → A → B}
    (ho : Primrec o) (hz : Primrec z) (hg : Primrec₂ g) :
    Primrec fun x => (o x).elim (z x) (g x) :=
  (Primrec.option_casesOn ho hz hg).of_eq (fun x => by cases o x <;> rfl)

private theorem primrec_select {options : X → List (Option ℕ)} {sites : X → List Site}
    {scope branches : X → List ℕ} {v : X → Option ℕ} (ho : Primrec options)
    (hs : Primrec sites) (hc : Primrec scope) (hb : Primrec branches) (hv : Primrec v) :
    Primrec fun x => go (resolve (sites x)
      (scope x, (branches x).getD ((options x).idxOf (v x)) 0)) :=
  primrec_go.comp (primrec_resolve.comp hs
    (hc.pair ((Primrec.list_getD 0).comp hb (primrec_idx.comp hv ho))))

private theorem primrec_look {options : X → List (Option ℕ)} {sites : X → List Site}
    {heads : X → Heads} {scope branches : X → List ℕ} {i : X → ℕ}
    (ho : Primrec options) (hs : Primrec sites) (hh : Primrec heads) (hc : Primrec scope)
    (hi : Primrec i) (hb : Primrec branches) :
    Primrec fun x => look (options x) (sites x) (heads x) (scope x) (i x) (branches x) :=
  primrec_elim ((Primrec.list_getD none).comp hh (Primrec.succ.comp hi))
    (primrec_select ho hs hc hb (Primrec.const none))
    (Primrec.option_bind (primrec_getLeft.comp Primrec.snd)
      (primrec_select (ho.comp (Primrec.fst.comp Primrec.fst))
        (hs.comp (Primrec.fst.comp Primrec.fst)) (hc.comp (Primrec.fst.comp Primrec.fst))
        (hb.comp (Primrec.fst.comp Primrec.fst)) (Primrec.option_some.comp Primrec.snd)).to₂).to₂

private theorem primrec_instruction {options : X → List (Option ℕ)} {sites : X → List Site}
    {heads : X → Heads} {scope args : X → List ℕ} (ho : Primrec options) (hs : Primrec sites)
    (hh : Primrec heads) (hc : Primrec scope) (ha : Primrec args) :
    Primrec fun x => instruction (options x) (sites x) (heads x) (scope x) (args x) := by
  have field (j : ℕ) := (Primrec.list_getD 0).comp ha (Primrec.const j)
  have test (j : ℕ) := Primrec.eq.comp (field 0) (Primrec.const j)
  exact Primrec.ite (test 0) (Primrec.const (go none)) <|
    Primrec.ite (test 1)
      (primrec_act (Primrec.succ.comp (field 1))
        (Primrec.option_some.comp (Primrec.sumInl.comp (field 2))) (Primrec.const none)) <|
    Primrec.ite (test 2)
      (primrec_act (Primrec.succ.comp (field 1)) (Primrec.const none) (Primrec.const none)) <|
    Primrec.ite (test 3)
      (primrec_look ho hs hh hc (field 1) (Primrec.list_drop.comp (Primrec.const 2) ha)) <|
    Primrec.ite (test 4)
      (Primrec.option_bind (primrec_resolve.comp hs (hc.pair (field 2)))
        (primrec_act (Primrec.const 0) (Primrec.option_some.comp (Primrec.sumInr.comp Primrec.snd))
          ((primrec_resolve.comp hs (hc.pair (field 1))).comp Primrec.fst)).to₂) <|
    Primrec.ite (test 5)
      (primrec_go.comp (primrec_resolve.comp hs ((Primrec.list_cons.comp (field 1) hc).pair (field 1)))) <|
    Primrec.ite (test 6)
      (Primrec.option_bind (Primrec.list_getElem?.comp hc (field 1))
        (primrec_go.comp (primrec_resolve.comp (hs.comp Primrec.fst)
          (((Primrec.list_drop.comp (field 1) hc).comp Primrec.fst).pair Primrec.snd))).to₂)
      (Primrec.const none)

/-- Compute the full stack-machine transition, including every kind of structured instruction. -/
theorem primrec_step {options : X → List (Option ℕ)} {sites : X → List Site}
    {heads : X → Heads} {q : X → Option Site} (ho : Primrec options) (hs : Primrec sites)
    (hh : Primrec heads) (hq : Primrec q) :
    Primrec fun x => step (options x) (sites x) (heads x) (q x) :=
  primrec_elim hq (primrec_ret.comp hh)
    (primrec_instruction (ho.comp Primrec.fst) (hs.comp Primrec.fst) (hh.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd) (primrec_fields.comp (Primrec.snd.comp Primrec.snd))).to₂

/-- Computable code, heads, and program counters suffice to compute a transition. -/
theorem computable_step {options : X → List (Option ℕ)} {sites : X → List Site}
    {heads : X → Heads} {q : X → Option Site} (ho : Computable options) (hs : Computable sites)
    (hh : Computable heads) (hq : Computable q) :
    Computable fun x => step (options x) (sites x) (heads x) (q x) :=
  (primrec_step Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp.comp (ho.pair (hs.pair (hh.pair hq)))

/-- Project the sparse update to the command for a chosen register. -/
theorem primrec_rowAt : Primrec₂ rowAt :=
  (Primrec.option_map Primrec.fst
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.option_bind (Primrec.snd.comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)).to₂)).to₂).to₂

end GeneratorSyntax.Transition

end NearSquareRoot
end Computability
end OAI

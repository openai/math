import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackOutput

/-! # Primitive recursive packing of sparse compiler output -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open Transition Generator.SyntaxAddress CommonAlphabet

variable {X : Type} [Primcodable X]

private theorem elimOption {B C : Type} [Primcodable B] [Primcodable C]
    {o : X → Option B} {f : X → C} {g : X → B → C} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun x => (o x).elim (f x) (g x) :=
  (Primrec.option_casesOn ho hf hg).of_eq fun x => by cases o x <;> rfl

theorem primrec_stateDigit {sites : X → List Site} {q : X → Option Site}
    (hs : Primrec sites) (hq : Primrec q) : Primrec fun x => stateDigit (sites x) (q x) :=
  elimOption hq (Primrec.const 0) (Primrec.succ.comp
    (primrec_rank.comp (hs.comp Primrec.fst) Primrec.snd)).to₂

theorem primrec_symbolDigit {aSize : X → ℕ} {sites : X → List Site} {s : X → Symbol}
    (ha : Primrec aSize) (hs : Primrec sites) (hr : Primrec s) :
    Primrec fun x => symbolDigit (aSize x) (sites x) (s x) :=
  (Primrec.sumCasesOn hr Primrec₂.right
    (Primrec.nat_add.comp (ha.comp Primrec.fst) (primrec_rank.comp (hs.comp Primrec.fst) Primrec.snd)).to₂).of_eq
    fun x => by cases s x <;> rfl

theorem primrec_actionDigit {aSize : X → ℕ} {sites : X → List Site} {c : X → Option (Option Symbol)}
    (ha : Primrec aSize) (hs : Primrec sites) (hc : Primrec c) :
    Primrec fun x => actionDigit (aSize x) (sites x) (c x) :=
  elimOption hc (Primrec.const 0) (elimOption Primrec.snd (Primrec.const 1)
    (Primrec.nat_add.comp (primrec_symbolDigit (ha.comp (Primrec.fst.comp Primrec.fst))
      (hs.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd) (Primrec.const 2)).to₂).to₂

theorem primrec_stackNames : Primrec stackNames :=
  Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_map
    (primrec_dedup.comp primrec_registerNames) (Primrec.succ.comp Primrec.snd).to₂)

theorem primrec_changeAt : Primrec₂ changeAt :=
  Primrec.option_bind Primrec.fst (Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)).to₂

theorem primrec_output {aSize : X → ℕ} {sites : X → List Site} {r : X → Result}
    (ha : Primrec aSize) (hs : Primrec sites) (hr : Primrec r) :
    Primrec fun x => output (aSize x) (sites x) (r x) := by
  apply Primrec.option_map hr
  apply Primrec.pair
  · exact primrec_stateDigit (hs.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  · apply Numbering.primrec_encodeBase.comp
    · exact Primrec.nat_add.comp (Primrec.nat_add.comp (ha.comp Primrec.fst)
        (primrec_size.comp (hs.comp Primrec.fst))) (Primrec.const 2)
    · exact Primrec.list_map (primrec_stackNames.comp (hs.comp Primrec.fst))
        (primrec_actionDigit (ha.comp (Primrec.fst.comp Primrec.fst)) (hs.comp (Primrec.fst.comp Primrec.fst))
          (primrec_changeAt.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI

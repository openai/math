import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackInput

/-! # Effective decoding of packed stack readings -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open CommonAlphabet Generator.SyntaxAddress

variable {X : Type} [Primcodable X]

theorem primrec_decodePC : Primrec₂ decodePC := by
  apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none)
  exact primrec_read.comp Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))

theorem primrec_decodeTop {aSize : X → ℕ} {sites : X → List Site} {n : X → ℕ}
    (ha : Primrec aSize) (hs : Primrec sites) (hn : Primrec n) :
    Primrec fun x => decodeTop (aSize x) (sites x) (n x) := by
  let j (x : X) := n x - 1
  have hj : Primrec j := Primrec.nat_sub.comp hn (Primrec.const 1)
  apply Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) (Primrec.const none)
  apply Primrec.ite (Primrec.nat_lt.comp hj ha) (Primrec.option_some.comp (Primrec.sumInl.comp hj))
  exact Primrec.option_map (primrec_read.comp hs (Primrec.nat_sub.comp hj ha))
    (Primrec.sumInr.comp Primrec.snd).to₂

theorem primrec_slot : Primrec₂ slot := by
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.succ.comp (primrec_rank.comp Primrec.fst
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))))

theorem primrec_heads {aSize : X → ℕ} {sites : X → List Site} {packed : X → ℕ}
    (ha : Primrec aSize) (hs : Primrec sites) (hr : Primrec packed) :
    Primrec fun x => heads (aSize x) (sites x) (packed x) := by
  have names := primrec_registerNames.comp hs
  have maxName := Primrec.list_foldr names (Primrec.const 0) (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  have base := Primrec.succ.comp (Primrec.nat_add.comp ha (primrec_size.comp hs))
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp maxName (Primrec.const 2)))
  exact (primrec_decodeTop (ha.comp Primrec.fst) (hs.comp Primrec.fst)
    (Numbering.primrec_digit (base.comp Primrec.fst) (hr.comp Primrec.fst)
      (primrec_slot.comp (names.comp Primrec.fst) Primrec.snd))).to₂

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI

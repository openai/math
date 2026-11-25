import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPadding
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackOutputEffective

/-! # Computability of padding a variable tape set into a fixed register bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Padding

open CommonAlphabet IntegerMultiplication

variable {X : Type} [Primcodable X]

theorem primrec_positions : Primrec positions :=
  Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_map Pack.primrec_stackNames (Primrec.succ.comp Primrec.snd).to₂)

theorem primrec_extract {b r : X → ℕ} {ps : X → List ℕ} (hb : Primrec b) (hp : Primrec ps)
    (hr : Primrec r) : Primrec fun x => extract (b x) (ps x) (r x) :=
  Numbering.primrec_encodeBase.comp hb (Primrec.list_map hp
    (Numbering.primrec_digit (hb.comp Primrec.fst) (hr.comp Primrec.fst) Primrec.snd).to₂)

theorem primrec_one {b r a j : X → ℕ} {ps : X → List ℕ} (hb : Primrec b) (hp : Primrec ps)
    (hr : Primrec r) (ha : Primrec a) (hj : Primrec j) :
    Primrec fun x => one (b x) (ps x) (r x) (a x) (j x) :=
  Primrec.ite (Primrec.nat_lt.comp (Primrec.list_idxOf.comp hj hp) (Primrec.list_length.comp hp))
    (Numbering.primrec_digit (Primrec.nat_mul.comp hb (Primrec.const 3)) ha
      (Primrec.list_idxOf.comp hj hp))
    (Primrec.nat_add.comp (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.const 3)
      (Numbering.primrec_digit hb hr hj)))

theorem primrec_expand {b n r a : X → ℕ} {ps : X → List ℕ} (hb : Primrec b) (hn : Primrec n)
    (hp : Primrec ps) (hr : Primrec r) (ha : Primrec a) :
    Primrec fun x => expand (b x) (n x) (ps x) (r x) (a x) :=
  Numbering.primrec_encodeBase.comp (Primrec.nat_mul.comp hb (Primrec.const 3))
    (Primrec.list_map (Primrec.list_range.comp hn)
      (primrec_one (hb.comp Primrec.fst) (hp.comp Primrec.fst) (hr.comp Primrec.fst)
        (ha.comp Primrec.fst) Primrec.snd).to₂)

private theorem computable_extract {b r : X → ℕ} {ps : X → List ℕ}
    (hb : Computable b) (hp : Computable ps) (hr : Computable r) :
    Computable fun x => extract (b x) (ps x) (r x) :=
  (primrec_extract Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp.comp
    (hb.pair (hp.pair hr))

private theorem computable_expand {b n r a : X → ℕ} {ps : X → List ℕ} (hb : Computable b)
    (hn : Computable n) (hp : Computable ps) (hr : Computable r) (ha : Computable a) :
    Computable fun x => expand (b x) (n x) (ps x) (r x) (a x) :=
  (primrec_expand Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to_comp.comp
      (hb.pair (hn.pair (hp.pair (hr.pair ha))))

theorem computable_row {b n : X → ℕ} {ps : X → List ℕ} {orig : X → ℕ × ℕ → Option (ℕ × ℕ)}
    (hb : Computable b) (hn : Computable n) (hp : Computable ps) (ho : Computable₂ orig) :
    Computable₂ fun x => row (b x) (n x) (ps x) (orig x) := by
  let X' := X × (ℕ × ℕ)
  have reads : Computable fun v : X' => v.2.2 := Computable.snd.comp Computable.snd
  have request : Computable fun v : X' => (v.2.1, extract (b v.1) (ps v.1) v.2.2) :=
    (Computable.fst.comp Computable.snd).pair (computable_extract (hb.comp Computable.fst)
      (hp.comp Computable.fst) reads)
  apply Computable.option_map (ho.comp Computable.fst request)
  have idx : Computable fun z : X' × (ℕ × ℕ) => z.1.1 := Computable.fst.comp Computable.fst
  exact ((Computable.fst.comp Computable.snd).pair
    (computable_expand (hb.comp idx) (hn.comp idx) (hp.comp idx) (reads.comp Computable.fst)
      (Computable.snd.comp Computable.snd))).to₂

/-- Pad an effectively generated family of bounded-register programs. The state
and alphabet numberings pass through, and all members now share the same tapes. -/
theorem padded_family {A : Type} [Fintype A] (a : Numbering A) {p : X → Prog A}
    (eff : Effective (Pack.letter a) p) {R : ℕ} (hR : 0 < R)
    (bound : ∀ k, CommonRegisters.Within R (p k))
    {B Q : X → Type} (b : ∀ k, Numbering (B k)) (q : ∀ k, Numbering (Q k))
    (m : ∀ k, TM.Rule (B k) (Q k) (Option (Prog.Ix (Prog.sites [] (p k)))))
    (orig : X → ℕ × ℕ → Option (ℕ × ℕ)) (hb : Computable fun k => (b k).size)
    (ho : Computable₂ orig)
    (source : ∀ k s r, orig k (((q k).equiv s).val,
        (((Pack.stacks (Prog.sites [] (p k))).option.arrow (b k)).equiv r).val) =
      (m k s r).map fun z => (((q k).equiv z.1).val,
        (((Pack.stacks (Prog.sites [] (p k))).option.arrow ((b k).prod Numbering.move)).equiv z.2).val)) :
    let rows k := row (b k).size (R+2) (positions ((file (Pack.letter a) (p k)).2)) (orig k)
    Computable₂ rows ∧ ∀ k s r, rows k (((q k).equiv s).val,(((fixed R).arrow (b k)).equiv r).val) =
      (CommonTapes.rule (CommonRegisters.indexEmbedding hR (bound k)) (m k) s r).map fun z =>
        (((q k).equiv z.1).val, (((fixed R).arrow ((b k).prod Numbering.move)).equiv z.2).val) :=
  ⟨computable_row hb (Computable.const _) (primrec_positions.to_comp.comp (Computable.snd.comp eff)) ho,
    fun k => padded a hR (bound k) (b k) (q k) (m k) (orig k) (source k)⟩

end GeneratorSyntax.Padding

end NearSquareRoot
end Computability
end OAI

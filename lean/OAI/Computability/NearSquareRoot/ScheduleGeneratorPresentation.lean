import OAI.Computability.NearSquareRoot.ScheduleGeneratorAlphabetDigits

/-! # Uniform computable presentations for families of finite alphabets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator

open CommonAlphabet

/-- A fixed computable representation for the elements of varying numbered types.
Encoding and decoding agree with the specified enumeration on actual elements. -/
structure Presentation {T : ℕ → Type} (N : ∀ j, Numbering (T j))
    (R : Type) [Primcodable R] where
  view (j : ℕ) : T j → R
  size_eff : Computable (fun j => (N j).size)
  encode : ℕ → R → ℕ
  encode_eff : Computable₂ encode
  decode : ℕ → ℕ → R
  decode_eff : Computable₂ decode
  encode_view : ∀ j x, encode j (view j x) = ((N j).equiv x).val
  decode_rank : ∀ j x, decode j ((N j).equiv x).val = view j x

namespace Presentation

variable {T U : ℕ → Type} {N : ∀ j, Numbering (T j)} {M : ∀ j, Numbering (U j)}
variable {R S : Type} [Primcodable R] [Primcodable S]

/-- Use each label's ordinal itself as its representation. -/
def scalar (N : ∀ j, Numbering (T j)) (hn : Computable fun j => (N j).size) :
    Presentation N ℕ where
  view j x := ((N j).equiv x).val
  size_eff := hn
  encode _ x := x
  encode_eff := Computable.snd
  decode _ x := x
  decode_eff := Computable.snd
  encode_view _ _ := rfl
  decode_rank _ _ := rfl

/-- Products use the right-hand cardinality as the radix for the pair of labels. -/
def prod (a : Presentation N R) (b : Presentation M S) :
    Presentation (fun j => (N j).prod (M j)) (R × S) where
  view j x := (a.view j x.1, b.view j x.2)
  size_eff := Primrec.nat_mul.to_comp.comp a.size_eff b.size_eff
  encode j x := b.encode j x.2 + (M j).size * a.encode j x.1
  encode_eff := Primrec.nat_add.to_comp.comp
    (b.encode_eff.comp Computable.fst (Computable.snd.comp Computable.snd))
    (Primrec.nat_mul.to_comp.comp (b.size_eff.comp Computable.fst)
      (a.encode_eff.comp Computable.fst (Computable.fst.comp Computable.snd)))
  decode j c := (a.decode j (c / (M j).size), b.decode j (c % (M j).size))
  decode_eff := by
    have size := b.size_eff.comp (Computable.fst (α := ℕ) (β := ℕ))
    exact (a.decode_eff.comp Computable.fst (Primrec.nat_div.to_comp.comp Computable.snd size)).pair
      (b.decode_eff.comp Computable.fst (Primrec.nat_mod.to_comp.comp Computable.snd size))
  encode_view j x := by
    dsimp only
    rw [a.encode_view, b.encode_view]
    rfl
  decode_rank j x := by
    have digits := finProdFinEquiv.symm_apply_apply ((N j).equiv x.1, (M j).equiv x.2)
    exact (congrArg (fun p : Fin (N j).size × Fin (M j).size =>
      (a.decode j p.1.val, b.decode j p.2.val)) digits).trans
      (Prod.ext (a.decode_rank j x.1) (b.decode_rank j x.2))

/-- The right summand follows all labels in the left summand. -/
def sum (p : Presentation N R) (q : Presentation M S) :
    Presentation (fun j => (N j).sum (M j)) (R ⊕ S) where
  view j := Sum.map (p.view j) (q.view j)
  size_eff := Primrec.nat_add.to_comp.comp p.size_eff q.size_eff
  encode j x := Sum.casesOn x (p.encode j) (fun t => (N j).size + q.encode j t)
  encode_eff := (Computable.sumCasesOn Computable.snd
    (p.encode_eff.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
    (Primrec.nat_add.to_comp.comp (p.size_eff.comp (Computable.fst.comp Computable.fst))
      (q.encode_eff.comp (Computable.fst.comp Computable.fst) Computable.snd)).to₂).to₂
  decode j k := bif decide (k < (N j).size) then Sum.inl (p.decode j k)
    else Sum.inr (q.decode j (k - (N j).size))
  decode_eff := (Computable.cond
    (Primrec.nat_lt.decide.to_comp.comp Computable.snd (p.size_eff.comp Computable.fst))
    (Computable.sumInl.comp p.decode_eff)
    (Computable.sumInr.comp (q.decode_eff.comp Computable.fst
      (Primrec.nat_sub.to_comp.comp Computable.snd (p.size_eff.comp Computable.fst))))).to₂
  encode_view j x := by
    cases x with
    | inl a => exact p.encode_view j a
    | inr b => exact congrArg ((N j).size + ·) (q.encode_view j b)
  decode_rank j x := by
    cases x with
    | inl a =>
      rw [show (((N j).sum (M j)).equiv (Sum.inl a)).val = ((N j).equiv a).val from rfl]
      simp [((N j).equiv a).isLt, p.decode_rank]
    | inr b =>
      rw [show (((N j).sum (M j)).equiv (Sum.inr b)).val = (N j).size + ((M j).equiv b).val from rfl]
      simp [q.decode_rank]

end Presentation
end Generator

end NearSquareRoot
end Computability
end OAI

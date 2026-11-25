import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxComplete

/-! # Effective families of physical stack machines with an output copy -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.CompleteRows

open IntegerMultiplication CommonAlphabet Numbering

variable {X : Type*} [Primcodable X]

private theorem primrec_pack {b n : X → ℕ} {f : X → ℕ → ℕ}
    (hb : Primrec b) (hn : Primrec n) (hf : Primrec₂ f) :
    Primrec fun x => pack (b x) (n x) (f x) :=
  primrec_encodeBase.comp hb (Primrec.list_map (Primrec.list_range.comp hn) hf)

private theorem primrec_oldReads {b n r : X → ℕ} (hb : Primrec b) (hn : Primrec n) (hr : Primrec r) :
    Primrec fun x => oldReads (b x) (n x) (r x) :=
  primrec_pack hb hn (primrec_digit (hb.comp Primrec.fst) (hr.comp Primrec.fst)
    (Primrec.succ.comp Primrec.snd)).to₂

private theorem primrec_keep {b r j : X → ℕ} (hb : Primrec b) (hr : Primrec r) (hj : Primrec j) :
    Primrec fun x => keep (b x) (r x) (j x) :=
  Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 3) (primrec_digit hb hr hj))

private theorem primrec_oldCmd {b r acts j : X → ℕ} (hb : Primrec b) (hr : Primrec r)
    (ha : Primrec acts) (hj : Primrec j) : Primrec fun x => oldCmd (b x) (r x) (acts x) (j x) :=
  Primrec.ite (Primrec.eq.comp hj (Primrec.const 0)) (primrec_keep hb hr hj)
    (primrec_digit (Primrec.nat_mul.comp hb (Primrec.const 3)) ha (Primrec.nat_sub.comp hj (Primrec.const 1)))

private theorem primrec_copyCmd {b k r j : X → ℕ} (hb : Primrec b) (hk : Primrec k)
    (hr : Primrec r) (hj : Primrec j) : Primrec fun x => copyCmd (b x) (k x) (r x) (j x) :=
  Primrec.ite (Primrec.eq.comp hj (Primrec.const 0))
    (Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 3)
      (primrec_digit hb hr (Primrec.succ.comp hk))))
    (Primrec.ite (Primrec.eq.comp hj (Primrec.succ.comp hk)) (Primrec.const 2) (primrec_keep hb hr hj))

private def finish (b n k q r : ℕ) (old : Option (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  if q = 0 then
    if digit b r (k+1) = 0 then none else some (0, pack (b*3) (n+1) (copyCmd b k r))
  else old.elim (some (0,pack (b*3) (n+1) (keep b r)))
    (fun z => some (z.1+1,pack (b*3) (n+1) (oldCmd b r z.2)))

private theorem primrec_finish {b n k q r : X → ℕ} {o : X → Option (ℕ × ℕ)}
    (hb : Primrec b) (hn : Primrec n) (hk : Primrec k) (hq : Primrec q)
    (hr : Primrec r) (ho : Primrec o) :
    Primrec fun x => finish (b x) (n x) (k x) (q x) (r x) (o x) := by
  have base := Primrec.nat_mul.comp hb (Primrec.const 3)
  have count := Primrec.succ.comp hn
  apply Primrec.ite (Primrec.eq.comp hq (Primrec.const 0))
  · exact Primrec.ite (Primrec.eq.comp (primrec_digit hb hr (Primrec.succ.comp hk)) (Primrec.const 0))
      (Primrec.const none) (Primrec.option_some.comp ((Primrec.const 0).pair
        (primrec_pack base count
          (primrec_copyCmd (hb.comp Primrec.fst) (hk.comp Primrec.fst) (hr.comp Primrec.fst) Primrec.snd).to₂)))
  · apply (Primrec.option_casesOn ho _ _).of_eq
    · intro x
      cases o x <;> rfl
    · exact Primrec.option_some.comp ((Primrec.const 0).pair (primrec_pack base count
        (primrec_keep (hb.comp Primrec.fst) (hr.comp Primrec.fst) Primrec.snd).to₂))
    · exact (Primrec.option_some.comp ((Primrec.succ.comp (Primrec.fst.comp Primrec.snd)).pair
        (primrec_pack (base.comp Primrec.fst) (count.comp Primrec.fst)
          (primrec_oldCmd (hb.comp (Primrec.fst.comp Primrec.fst)) (hr.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂))).to₂

private abbrev Frame := ℕ × ℕ × ℕ × ℕ × ℕ × Option (ℕ × ℕ)

private theorem finishFrame : Primrec (fun p : Frame =>
    finish p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
  primrec_finish Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

set_option maxHeartbeats 500000 in
/-- Vary the alphabet, stack count, designated register, and original row function together. -/
theorem computable_row {b n k : ℕ → ℕ} {orig : ℕ → ℕ × ℕ → Option (ℕ × ℕ)}
    (hb : Computable b) (hn : Computable n) (hk : Computable k) (ho : Computable₂ orig) :
    Computable₂ fun j p => row (b j) (n j) (k j) (orig j) p := by
  let X := ℕ × (ℕ × ℕ)
  have t : Computable (fun p : X => p.2.2) := Computable.snd.comp Computable.snd
  have s : Computable (fun p : X => p.2.1) := Computable.fst.comp Computable.snd
  have hreads : Computable fun p : X => oldReads (b p.1) (n p.1) p.2.2 :=
    (primrec_oldReads Primrec.fst (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to_comp.comp
      ((hb.comp Computable.fst).pair ((hn.comp Computable.fst).pair t))
  let prev (p : X) := orig p.1 (p.2.1-1,oldReads (b p.1) (n p.1) p.2.2)
  have old : Computable prev :=
    ho.comp Computable.fst ((Primrec.nat_sub.to_comp.comp s (Computable.const 1)).pair hreads)
  let bundle (p : X) : Frame := (b p.1,n p.1,k p.1,p.2.1,p.2.2,prev p)
  have packed : Computable bundle := (hb.comp Computable.fst).pair ((hn.comp Computable.fst).pair
    ((hk.comp Computable.fst).pair (s.pair (t.pair old))))
  change Computable (fun p : X => row (b p.1) (n p.1) (k p.1) (orig p.1) p.2)
  apply (finishFrame.to_comp.comp packed).of_eq
  intro p
  rfl

/-- The compiled machine includes the new, initially separate output tape. All three
finite sizes and every row of the physical rule are computable in the family index. -/
theorem compile_family {A Q I : ℕ → Type} [∀ j, DecidableEq (I j)]
    (a : ∀ j, Numbering (A j)) (q : ∀ j, Numbering (Q j)) (i : ∀ j, Numbering (I j))
    (k : ∀ j, I j) (m : ∀ j, SM.Rule (A j) (Q j) (I j))
    (orig : ℕ → ℕ × ℕ → Option (ℕ × ℕ))
    (ha : Computable fun j => (a j).size) (hq : Computable fun j => (q j).size)
    (hi : Computable fun j => (i j).size) (hk : Computable fun j => ((i j).equiv (k j)).val)
    (ho : Computable₂ orig) (hs : ∀ j, StackRows.Sources (a j) (q j) (i j) (m j) (orig j)) :
    let state := fun j => (StackRows.pc (a j) (q j) (i j)).option
    let letter := fun j => (a j).option
    let heads := fun j => (i j).option
    let rows j := row (letter j).size (i j).size ((i j).equiv (k j)).val
      (StackRows.row (a j).size (q j).size (i j).size (orig j))
    Computable (fun j => (state j).size) ∧ Computable (fun j => (letter j).size) ∧
    Computable (fun j => (heads j).size) ∧ Computable₂ rows ∧ ∀ j s top,
      rows j (((state j).equiv s).val,(((heads j).arrow (letter j)).equiv top).val) =
        ((SM.complete (k j) (m j)) s top).map fun z => (((state j).equiv z.1).val,
          (((heads j).arrow ((letter j).prod Numbering.move)).equiv z.2).val) := by
  obtain ⟨state,letter,rows,valid⟩ := StackRows.compile_family a q i m orig ha hq hi ho hs
  exact ⟨Primrec.succ.to_comp.comp state, letter, Primrec.succ.to_comp.comp hi,
    computable_row letter hi hk rows, fun j => row_eq (a j) (StackRows.pc (a j) (q j) (i j))
      (i j) (k j) (SM.toTM (m j)) _ (valid j)⟩

end Generator.CompleteRows

end NearSquareRoot
end Computability
end OAI

import OAI.ThreeFlat.Diagonal.ShrinkDescriptorSpan

namespace OAI
/-! # Indexed readback from a contiguous series of stateful native scans -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan RAM.HeaderScan RAM.PhysicalPinsExpr
open scoped Fin.NatCast
variable {w : ℕ}

/-- State visible to the row at address `at`. Every smaller output address already
contains its final word and every remaining cell still has its input value. -/
def beforeAddress (lo pos : ℕ) (old out : Memory w) : Memory w :=
  fun i => if lo≤ i ∧ i<pos then out i else old i

theorem beforeAddress_frame (lo pos : ℕ) (old out : Memory w) :
    agreesOutside lo pos (beforeAddress lo pos old out) old := by
  intro i h
  simp [beforeAddress,show ¬(lo≤ i ∧ i<pos) by omega]

private theorem beforeAddress_empty (lo : ℕ) (old out : Memory w) : beforeAddress lo lo old out=old := by
  funext i; simp [beforeAddress,show ¬(lo≤ i ∧ i<lo) by omega]

theorem sweep_word (f : Word w → Memory w → Word w) (n : ℕ) (a : Word w) (m : Memory w)
    (fit : a.val+n<2^w) (i : ℕ) (low : a.val≤ i) (high : i<a.val+n) :
    (sweep f n a m) i = f (i:Word w) (beforeAddress a.val i m (sweep f n a m)) := by
  induction n generalizing a m with
  | zero => omega
  | succ n ih =>
    let next := writeMemory m a (f a m)
    let out := sweep f n (a+1) next
    have sa : (a+1).val=a.val+1 := Fin.val_add_one_of_lt' (by omega)
    have safe : (a+1).val+n<2^w := by omega
    have frame:=sweep_frame f n (a+1) next safe
    have head : out a.val=f a m := (frame _ (.inl (by omega))).trans (by simp [next,writeMemory])
    change out i=f (i:Word w) (beforeAddress a.val i m out)
    by_cases e : i=a.val
    · subst i; rw [head,beforeAddress_empty,Fin.cast_val_eq_self]
    · have between : (a+1).val≤ i := by omega
      have ctx : beforeAddress (a+1).val i next out=beforeAddress a.val i m out := by
        funext q
        by_cases this : q=a.val
        · subst q
          simp [beforeAddress,sa,show a.val< i by omega,next,writeMemory,head]
        · have cond : ((a+1).val≤q ∧ q< i) ↔ (a.val≤q ∧ q< i) := by omega
          simp only [beforeAddress,cond,next,writeMemory,ite_eq_right this]
      exact (ih (a+1) next safe between (by omega)).trans (congrArg (f (i:Word w)) ctx)

/-- The field starts/lengths partition `[lo,hi)` in literal program order. -/
def Consecutive (f : ℕ→ℕ) : Recipe → ℕ → ℕ → Prop
  | .one _ a n,lo,hi => a≤63 ∧ n≤63 ∧ f a=lo ∧ f a+f n=hi
  | .seq l r,lo,hi => ∃ mid,Consecutive f l lo mid ∧ Consecutive f r mid hi

theorem Consecutive.span {f : ℕ→ℕ} {p : Recipe} {lo hi : ℕ} (cons : Consecutive f p lo hi) :
    lo≤hi ∧ Within f lo hi p := by
  induction p generalizing lo hi with
  | one row a n =>
    obtain ⟨ha,hn,rfl,rfl⟩:=cons
    exact ⟨Nat.le_add_right ..,ha,hn,le_rfl,le_rfl⟩
  | seq a b ia ib =>
    obtain ⟨mid,left,right⟩:=cons
    have l:=ia left
    have r:=ib right
    exact ⟨l.1.trans r.1,Within.widen a l.2 le_rfl r.1,Within.widen b r.2 l.1 le_rfl⟩

/-- The literal expression assigned to one concrete word of a recipe. -/
inductive AtWord (f : ℕ→ℕ) : Recipe → ℕ → Template.F → Prop
  | one {r a n i} (hi : i<f n) : AtWord f (.one r a n) (f a+i) r
  | left {l r i row} (h : AtWord f l i row) : AtWord f (.seq l r) i row
  | right {l r i row} (h : AtWord f r i row) : AtWord f (.seq l r) i row

theorem AtWord.range {f : ℕ→ℕ} {p : Recipe} {i lo hi : ℕ} {r : Template.F}
    (atWord : AtWord f p i r) (window : Within f lo hi p) : lo≤ i ∧ i<hi := by
  induction atWord with
  | one h =>
    obtain ⟨_,_,a,b⟩:=window
    omega
  | left h ih => exact ih window.1
  | right h ih => exact ih window.2

def Published (p : Recipe) (cur : Word w) (f : ℕ→ℕ) (lo : ℕ) (old out : Memory w) : Prop :=
  ∀ {a row},AtWord f p a row →
    out a=Formula.value (fun _=>cur) (beforeAddress lo a old out) (fun _=>(a:Word w)) row

theorem publish (p : Recipe) (cur : Word w) (pub : Fin 1 → Word w) (m : Memory w) {head lo hi : ℕ}
    {f : ℕ→ℕ} (H : Scans.Header cur m head 63 f) (earlier : head+64≤lo) (later : hi≤cur.val)
    (cons : Consecutive f p lo hi) :
    Published p cur f lo m ((p.install cur).execute cur pub m).2 := by
  induction p generalizing m lo hi with
  | one row a n =>
    obtain ⟨ha,hn,eq1,eq2⟩:=cons
    have start : (headerRead m cur a).val=f a := H.get a ha
    have len : (headerRead m cur n).val=f n := H.get n hn
    intro i r atWord
    cases atWord with
    | @one _ _ _ j hj =>
      let word:=fun (q : Word w) (mem : Memory w)=>(Template.emit cur row).eval pub mem (fun _=>q)
      have safe : (headerRead m cur a).val+(headerRead m cur n).val<2^w := by rw [start,len,eq2];exact later.trans_lt cur.isLt
      have v := sweep_word word (headerRead m cur n).val (headerRead m cur a) m safe (f a+j) (by omega) (by omega)
      rw [start,eq1] at v
      simpa only [Recipe.install,Pass.execute,word,Template.program_value,eq1] using v
  | seq a b ia ib =>
    obtain ⟨mid,left,right⟩:=cons
    let z:=((a.install cur).execute cur pub m).2
    let out:=((b.install cur).execute cur pub z).2
    have l:=left.span; have r:=right.span
    have ra:=run a cur pub m H earlier (r.1.trans later) l.2
    have rb:=run b cur pub z ra.header (earlier.trans l.1) later r.2
    have pa : Published a cur f lo m z := ia m H earlier (r.1.trans later) left
    have pb : Published b cur f mid z out := ib z ra.header (earlier.trans l.1) later right
    intro i row atWord
    change out i=Formula.value _ (beforeAddress lo i m out) _ row
    cases atWord with
    | left word =>
      have range:=word.range l.2
      have ctx : beforeAddress lo i m z=beforeAddress lo i m out := by
        funext j
        by_cases here : lo≤j ∧ j< i
        · simp only [beforeAddress,ite_eq_left here]; exact (rb.frame j (.inl (by omega))).symm
        · simp [beforeAddress,here]
      exact (rb.frame i (.inl range.2)).trans (ctx ▸ pa word)
    | right word =>
      have range:=word.range r.2
      have ctx : beforeAddress mid i z out=beforeAddress lo i m out := by
        funext j
        by_cases small : j<mid
        · by_cases afterLo : lo≤j
          · have middle : z j=out j := (rb.frame j (.inl small)).symm
            simp [beforeAddress,afterLo,show j< i by omega,middle]
          · have same : z j=m j := ra.frame j (.inl (by omega))
            have outside : ¬ (mid ≤ j ∧ j < i) := by omega
            simpa [beforeAddress, outside, afterLo] using same
        · by_cases beforeI : j< i
          · simp [beforeAddress,show mid≤j by omega,show lo≤j by omega,beforeI]
          · have same : z j=m j := ra.frame j (.inr (by omega))
            simpa [beforeAddress,beforeI] using same
      exact ctx ▸ pb word


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

end OAI

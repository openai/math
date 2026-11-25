import OAI.Computability.NearSquareRoot.ScheduleGeneratorSequenceRows
import OAI.Computability.NearSquareRoot.ScheduleStagingCycle

/-! # Effective transitions for fixed controllers and repeated digit calls -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.EffectiveRows
open CommonAlphabet IntegerMultiplication TM

variable {A I C V : Type} {D : ℕ → Type}

/-- Evaluate a two-dimensional finite table with any primitive-codable result. -/
def finiteTable₂ [Inhabited V] (s : Numbering C) (a : Numbering A) (f : C → A → V) (u v : ℕ) : V :=
  ((List.ofFn fun k => List.ofFn fun h => f (s.equiv.symm k) (a.equiv.symm h)).getD u []).getD v default

theorem finiteTable₂_eq [Inhabited V] (s : Numbering C) (a : Numbering A) (f : C → A → V)
    (u : C) (v : A) : finiteTable₂ s a f (s.equiv u).val (a.equiv v).val = f u v := by
  simp [finiteTable₂,List.getD_eq_getElem?_getD]

theorem primrec_finiteTable₂ [Inhabited V] [Primcodable V]
    (s : Numbering C) (a : Numbering A) (f : C → A → V) : Primrec₂ (finiteTable₂ s a f) :=
  (Primrec.list_getD default).comp ((Primrec.list_getD []).comp (Primrec.const _) Primrec.fst) Primrec.snd

/-- A physically fixed controller contributes a constant table independent of the family index. -/
theorem constant (a : Numbering A) (i : Numbering I) (s : Numbering C) (m : Rule A C I) :
    EffectiveRows a i (fun _ => s) (fun _ => m) := by
  let row := fun q h => (m q h).map fun z => ((s.equiv z.1).val,((i.arrow (a.prod Numbering.move)).equiv z.2).val)
  refine ⟨fun _ p => finiteTable₂ s (i.arrow a) row p.1 p.2,
    (primrec_finiteTable₂ _ _ _).to_comp.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd),?_⟩
  exact fun _ _ _ => finiteTable₂_eq _ _ _ _ _

/-- The fixed caller can issue arbitrarily many calls into one indexed digit machine.
The return address and tape moves agree with the physical staging driver. -/
theorem cycle (a : Numbering A) (i : Numbering I) (c : Numbering C)
    (q : ∀ j, Numbering (D j)) (m : Rule A C I) (callee : ∀ j, Rule A (D j) I)
    (start : ∀ j, D j) (resume : C) (paused : C → Bool)
    (entry : Computable fun j => ((q j).equiv (start j)).val)
    (h : EffectiveRows a i q callee) :
    EffectiveRows a i (fun j => c.sum (q j))
      (fun j => (StagingCycle.Driver.mk m (callee j) paused (start j) resume).rule) := by
  obtain ⟨f,hf,fc⟩ := h
  let out := fun s r => (m s r).map fun z => ((c.equiv z.1).val,((i.arrow (a.prod Numbering.move)).equiv z.2).val)
  let call := Routing.lookup c fun s => (paused s).toNat
  let row (j : ℕ) (p : ℕ × ℕ) :=
    bif decide (p.1 < c.size) then
      bif decide (call p.1 = 1) then
        some ((finiteTable₂ c (i.arrow a) out p.1 p.2).getD
          (c.size+((q j).equiv (start j)).val,holdRank a i p.2))
      else finiteTable₂ c (i.arrow a) out p.1 p.2
    else
      some (((f j (p.1-c.size,p.2)).map (fun z => (c.size+z.1,z.2))).getD
        ((c.equiv resume).val,holdRank a i p.2))
  let X := ℕ × (ℕ × ℕ)
  have state : Computable fun x : X => x.2.1 := Computable.fst.comp Computable.snd
  have read : Computable fun x : X => x.2.2 := Computable.snd.comp Computable.snd
  have hold := (Routing.primrec_lookup (i.arrow a) (fun r => ((i.arrow (a.prod Numbering.move)).equiv
    (fun k => (r k,Move.stay))).val)).to_comp.comp read
  have localRow := (primrec_finiteTable₂ c (i.arrow a) out).to_comp.comp state read
  have test := (Primrec.eq.decide.to_comp.comp ((Routing.primrec_lookup c _).to_comp.comp state)
    (Computable.const 1) : Computable fun x : X => decide (call x.2.1 = 1))
  have fallback := (Primrec.nat_add.to_comp.comp (Computable.const c.size) (entry.comp Computable.fst)).pair hold
  have first := Computable.cond test (Computable.option_some.comp (Computable.option_getD localRow fallback)) localRow
  have inner := hf.comp (Computable.fst (α:=ℕ) (β:=ℕ × ℕ))
      ((Primrec.nat_sub.to_comp.comp state (Computable.const c.size)).pair read)
  have shift : Computable₂ fun (_ : X) (z : ℕ × ℕ) => (c.size+z.1,z.2) :=
    (Primrec.nat_add.to_comp.comp (Computable.const c.size) (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd)
  have second := Computable.option_some.comp (Computable.option_getD (Computable.option_map inner shift)
    ((Computable.const (c.equiv resume).val).pair hold))
  refine ⟨row,(Computable.cond (Primrec.nat_lt.decide.to_comp.comp state (Computable.const c.size))
    first second).to₂,?_⟩
  intro j s r
  cases s with
  | inl s =>
    have rank : ((c.sum (q j)).equiv (.inl s)).val = (c.equiv s).val := rfl
    simp only [row,rank,(c.equiv s).isLt,decide_true,Bool.cond_true,finiteTable₂_eq,call,
      Routing.lookup_rank,StagingCycle.Driver.rule,holdRank,out]
    cases m s r with
    | none => cases paused s <;> rfl
    | some z => cases paused s <;> rfl
  | inr s =>
    have rank : ((c.sum (q j)).equiv (.inr s)).val = c.size+((q j).equiv s).val := rfl
    simp only [row,rank,Nat.not_lt_of_ge (Nat.le_add_right _ _),decide_false,Bool.cond_false,
      Nat.add_sub_cancel_left,fc,holdRank,Routing.lookup_rank,StagingCycle.Driver.rule]
    cases callee j s r <;> rfl

end Generator.EffectiveRows

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.NearSquareRoot.ScheduleGeneratorPublicRoute
import OAI.Computability.NearSquareRoot.ScheduleInterpreterCommonBlank

/-! # Uniform transition rows for physical sequencing and alphabet extension -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator
open CommonAlphabet IntegerMultiplication TM

/-- A total computable numerical evaluator agrees with every physical transition at
a valid program counter and read tuple. Both arguments of the evaluator are unbounded. -/
def EffectiveRows {A I : Type} {Q : ℕ → Type} (a : Numbering A) (i : Numbering I)
    (q : ∀ j, Numbering (Q j)) (m : ∀ j, Rule A (Q j) I) : Prop :=
  ∃ f : Routing.Rows, Computable₂ f ∧ ∀ j s h,
    f j (((q j).equiv s).val, ((i.arrow a).equiv h).val) =
      (m j s h).map fun z => (((q j).equiv z.1).val, ((i.arrow (a.prod Numbering.move)).equiv z.2).val)

namespace EffectiveRows
variable {A I J : Type} {Q R : ℕ → Type}
variable {a : Numbering A} {i : Numbering I} {q : ∀ j, Numbering (Q j)}
  {r : ∀ j, Numbering (R j)} {m : ∀ j, Rule A (Q j) I} {n : ∀ j, Rule A (R j) I}

theorem route (h : EffectiveRows a i q m) (θ : Pipeline.Route I J) (k : Numbering J) :
    EffectiveRows a k q (fun j => θ.rule (m j)) := by
  obtain ⟨f,hf,hf'⟩ := h
  exact ⟨Routing.rows θ a i k f,Routing.computable_rows _ _ _ _ _ hf,
    Routing.rows_correct θ a i k f q m hf'⟩

def holdRank (a : Numbering A) (i : Numbering I) : ℕ → ℕ :=
  Routing.lookup (i.arrow a) fun read =>
    ((i.arrow (a.prod Numbering.move)).equiv fun k => (read k,Move.stay)).val

/-- Write back each current letter and enter the successor phase on a halting first row. -/
def sequence (a : Numbering A) (i : Numbering I) (count entry : ℕ → ℕ) (f g : Routing.Rows) :
    Routing.Rows := fun j p =>
  bif decide (p.1 < count j) then
    some ((f j p).getD (count j + entry j, holdRank a i p.2))
  else
    (g j (p.1 - count j, p.2)).map fun z => (count j + z.1,z.2)

set_option maxHeartbeats 1200000 in
theorem computable_sequence (count entry : ℕ → ℕ) (f g : Routing.Rows)
    (hc : Computable count) (he : Computable entry) (hf : Computable₂ f) (hg : Computable₂ g) :
    Computable₂ (sequence a i count entry f g) := by
  let X := ℕ × (ℕ × ℕ)
  have idx : Computable (fun x : X => x.1) := Computable.fst
  have state : Computable (fun x : X => x.2.1) := Computable.fst.comp Computable.snd
  have read : Computable (fun x : X => x.2.2) := Computable.snd.comp Computable.snd
  have num := hc.comp idx
  have held : Computable (holdRank a i) := (Routing.primrec_lookup _ _).to_comp
  have fallback : Computable fun x : X => (count x.1 + entry x.1, holdRank a i x.2.2) :=
    (Primrec.nat_add.to_comp.comp num (he.comp idx)).pair (held.comp read)
  have firstPhase : Computable fun x : X => some ((f x.1 x.2).getD (count x.1 + entry x.1, holdRank a i x.2.2)) :=
    Computable.option_some.comp (Computable.option_getD hf fallback)
  have call : Computable fun x : X => g x.1 (x.2.1-count x.1,x.2.2) :=
    hg.comp idx ((Primrec.nat_sub.to_comp.comp state num).pair read)
  have shift : Computable₂ fun (x : X) (z : ℕ × ℕ) => (count x.1+z.1,z.2) :=
    (Primrec.nat_add.to_comp.comp (num.comp Computable.fst) (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd)
  exact (Computable.cond (Primrec.nat_lt.decide.to_comp.comp state num) firstPhase
    (Computable.option_map call shift)).to₂

theorem seq (left : EffectiveRows a i q m) (right : EffectiveRows a i r n)
    (size : Computable fun j => (q j).size) (entry : ∀ j, R j)
    (he : Computable fun j => ((r j).equiv (entry j)).val) :
    EffectiveRows a i (fun j => (q j).sum (r j)) (fun j => TapeSequence.rule (m j) (n j) (entry j)) := by
  obtain ⟨f,hf,fc⟩ := left
  obtain ⟨g,hg,gc⟩ := right
  refine ⟨sequence a i _ _ f g, computable_sequence _ _ _ _ size he hf hg, ?_⟩
  intro j s h
  cases s with
  | inl x =>
    have sx : (((q j).sum (r j)).equiv (.inl x)).val = ((q j).equiv x).val := rfl
    simp only [sequence,sx,((q j).equiv x).isLt,decide_true,Bool.cond_true,fc,TapeSequence.rule]
    cases run : m j x h with
    | none => simp [holdRank,Routing.lookup_rank]; rfl
    | some z => rfl
  | inr x =>
    have sx : (((q j).sum (r j)).equiv (.inr x)).val = (q j).size + ((r j).equiv x).val := rfl
    simp only [sequence,sx,Nat.not_lt_of_ge (Nat.le_add_right _ _),decide_false,Bool.cond_false,
      Nat.add_sub_cancel_left,gc,TapeSequence.rule]
    cases n j x h <;> rfl

/-- A fixed change of tape alphabet pre- and postcomposes the packed transition with
two fixed lookup tables on the read and action tuple ranks. -/
theorem commonBlank [DecidableEq A] (a' : Numbering (Option A)) (blank : I → A)
    (eff : EffectiveRows a i q m) :
    EffectiveRows a' i q (fun j => Uniform.CommonBlank.rule blank (m j)) := by
  obtain ⟨f,hf,fc⟩ := eff
  let read : ℕ → ℕ := Routing.lookup (i.arrow a') (fun h =>
    ((i.arrow a).equiv fun k => (h k).getD (blank k)).val)
  let write : ℕ → ℕ := Routing.lookup (i.arrow (a.prod Numbering.move)) (fun o =>
    ((i.arrow (a'.prod Numbering.move)).equiv
      (fun k => (Uniform.CommonBlank.encode (blank k) (o k).1,(o k).2))).val)
  have hr : Computable read := (Routing.primrec_lookup _ _).to_comp
  have hw : Computable write := (Routing.primrec_lookup _ _).to_comp
  let ev (j : ℕ) (p : ℕ × ℕ) := (f j (p.1,read p.2)).map (fun z => (z.1,write z.2))
  refine ⟨ev,?_,?_⟩
  · exact Computable.option_map (hf.comp Computable.fst ((Computable.fst.comp Computable.snd).pair
      (hr.comp (Computable.snd.comp Computable.snd))))
      ((Computable.fst.comp Computable.snd).pair (hw.comp (Computable.snd.comp Computable.snd)))
  · intro j s h
    simp only [ev,read,Routing.lookup_rank,fc,Uniform.CommonBlank.rule]
    cases m j s (fun k => (h k).getD (blank k)) with
    | none => rfl
    | some z => simp [write,Routing.lookup_rank]

end EffectiveRows
end Generator

end NearSquareRoot
end Computability
end OAI

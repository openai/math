import OAI.Computability.IntegerMultiplication.SM.Stack
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Basic.Finite.Sum

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Simulation with a fresh, absolutely addressed output tape. This allows us to combine
algorithms entirely in the stack model. -/

namespace SM
variable {A Q I : Type}

namespace Action
private def tag : Action A → Option (Option A)
  | .skip => none
  | .pop => some none
  | .push a => some (some a)

instance [Finite A] : Finite (Action A) := Finite.of_injective tag (by
  intro a b
  cases a <;> cases b <;> simp [tag])
end Action

open TM (Tape)

private def preserve (a : A) : A × TM.Move := (a, .stay)
private def right (a : A) : A × TM.Move := (a, .right)

/-- `none` indexes the fresh output tape, `none` in the PC type means copying. -/
def withOutput [DecidableEq I] (k : I) (m : TM.Rule (Option A) Q I) :
    TM.Rule (Option A) (Option Q) (Option I)
  | some q, a =>
    match m q (fun i => a (some i)) with
    | none => some (none, fun i => preserve (a i))
    | some (q', o) => some (some q', fun i => match i with
      | none => preserve (a i)
      | some j => o j)
  | none, a => (a (some k)).map fun v =>
    (none, fun i => match i with
    | none => right (some v)
    | some j => if j=k then right none else preserve (a i))

def configOut (x : TM.Config (Option A) Q I) (Y : Tape (Option A)) :
    TM.Config (Option A) (Option Q) (Option I) :=
  ⟨some x.pc, fun i => match i with
    | none => Y
    | some j => x.tape j⟩

variable [DecidableEq I] {k : I} {m : TM.Rule (Option A) Q I}

private theorem lift_one (x y : TM.Config (Option A) Q I)
    (h : TM.advance m x = some y) (Y : Tape (Option A)) :
    TM.advance (withOutput k m) (configOut x Y) = some (configOut y Y) := by
  rcases x with ⟨pc,tape⟩
  let a := fun i => (tape i).view 0
  cases hm : m pc a with
  | none =>
    simp [a] at hm -- does simp change?
    simp [TM.advance, hm] at h
  | some op =>
    rcases op with ⟨q,o⟩
    simp only [TM.advance, show (fun i => (tape i).view 0)=a from rfl, hm, Option.map_some, Option.some.injEq] at h
    subst y
    dsimp [TM.advance, configOut, withOutput]
    rw [hm]
    simp only [Option.map_some, Option.some.injEq, TM.Config.mk.injEq, true_and]
    funext i
    cases i with
    | none => exact Action.apply_stay _
    | some j => rfl

theorem lift_many {x y : TM.Config (Option A) Q I} {n}
    (h : Trace (TM.advance m) x n y) (Y : Tape (Option A)) :
    Trace (TM.advance (withOutput k m)) (configOut x Y) n (configOut y Y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (lift_one _ _ h _) ih

/-- Streaming from a (some k) tape whose view is the stack display. The output tape
pos may start anywhere. The specification says precisely which symbols changed. -/
theorem drain {s : List A} {ts : Option I → Tape (Option A)}
    (he : (ts (some k)).view = display s) :
    ∃ ts',
      Trace (TM.advance (withOutput k m)) ⟨none, ts⟩ s.length ⟨none, ts'⟩ ∧
      TM.advance (withOutput k m) ⟨none, ts'⟩ = none ∧
      ∀ i, (ts' none).absolute i =
        if (ts none).pos ≤ i ∧ i < (ts none).pos + (s.length : ℤ)
        then display s (i-(ts none).pos) else (ts none).absolute i := by
  induction s generalizing ts with
  | nil =>
    refine ⟨ts, .nil _, ?_, ?_⟩
    · simp [TM.advance, withOutput, he, display_top]
    · intro i
      simp
  | cons x s ih =>
    have h0 : (ts (some k)).view 0 = some x := by rw [he, display_top]; rfl
    let ts₁ : Option I → Tape (Option A) := fun i => (ts i).apply
      (match i with
      | none => right (some x)
      | some j => if j=k then right none else preserve ((ts i).view 0))
    have hs : TM.advance (withOutput k m) ⟨none, ts⟩ = some ⟨none, ts₁⟩ := by
      simp only [TM.advance, withOutput, h0, Option.map_some]; rfl
    have hv : (ts₁ (some k)).view = display s := by
      funext i
      simp only [ts₁, ↓reduceIte, right, Tape.apply, TM.Move.shift, he, Action.pop_array]
    obtain ⟨ts', h₁, halt, hw⟩ := ih hv
    refine ⟨ts', ?_, halt, ?_⟩
    · simpa [Nat.add_comm] using Trace.cons hs h₁
    · intro i
      let p := (ts none).pos
      have hnext : (ts₁ none).pos = p+1 := rfl
      have hwrite : (ts₁ none).absolute i = if i=p then some x else (ts none).absolute i :=
        (ts none).absolute_apply _ _
      rw [hw i, hnext, hwrite]
      change (if p + 1 ≤ i ∧ i < p + 1 + (s.length : ℤ) then display s (i - (p+1))
        else if i = p then some x else (ts none).absolute i) =
        if p ≤ i ∧ i < p + (((x::s).length : ℕ) : ℤ) then display (x::s) (i-p) else _
      have hlen : (((x::s).length : ℕ) : ℤ)=s.length+1 := by simp
      by_cases h : p+1 ≤ i ∧ i < p+1+s.length
      · rw [ite_eq_left h, ite_eq_left (by omega)]
        have e : ∃ n : ℕ, i-(p+1)=(n:ℤ) :=
          ⟨(i-(p+1)).toNat, by omega⟩
        obtain ⟨n,hn⟩ := e
        rw [hn, show i-p=((n+1:ℕ):ℤ) by omega]
        rfl
      · rw [ite_eq_right h]
        by_cases hx : i=p
        · rw [ite_eq_left hx, ite_eq_left (by omega), hx, sub_self, display_top]
          rfl
        · rw [ite_eq_right hx, ite_eq_right (by omega)]


def origin (q : Q) (i : I) (s : List A) : Config A Q I :=
  ⟨q, fun j => if j=i then s else []⟩

def complete (k : I) (m : Rule A Q I) :
    TM.Rule (Option A) (Option (PC A Q I)) (Option I) :=
  withOutput k (toTM m)

theorem complete_run {n : ℕ} {i k : I} {s : List A} {q} {g : Rule A Q I} {x}
    (h : Trace (advance g) (origin q i s) n x) (hg : advance g x = none) :
    let load : Option I → Tape (Option A) := fun j => if j=some i
      then Tape.loaded none (s.map some) else Tape.loaded none []
    ∃ done,
      Trace (TM.advance (complete k g)) ⟨some (Sum.inl q), load⟩
        (2*n+1+(x.stack k).length) done ∧
      TM.advance (complete k g) done = none ∧
      TM.whole none ((x.stack k).map some) (done.tape none) := by
  let U : Tape (Option A) := Tape.loaded none []
  let B : I → Tape (Option A) := fun j => if j=i then Tape.loaded none (s.map some) else U
  have hb : faithful (origin q i s).stack B := by
    intro j
    dsimp [B, origin]
    split
    · exact display_loaded s
    · exact display_loaded []
  obtain ⟨T, he, ht⟩ := simulate h B hb
  have hh := simulate_halt hg he
  have hprefix := lift_many (k := k) ht U
  let W : Option I → Tape (Option A) := fun l => match l with
    | none => U
    | some j => T j
  have hp : Trace (TM.advance (complete k g))
      ⟨some (Sum.inl q), fun j => if j=some i then Tape.loaded none (s.map some) else U⟩
      (2*n) ⟨some (.inl x.pc), W⟩ := by
    have e : (configOut (TM.Config.mk (Sum.inl q : PC A Q I) B) U) =
        TM.Config.mk (some (Sum.inl q)) (fun j => if j=some i then Tape.loaded none (s.map some) else U) := by
      unfold configOut
      congr 1
      funext j
      cases j <;> simp [B]
    rw [← e]
    exact hprefix
  have hemit₁ : TM.advance (complete k g) ⟨some (.inl x.pc), W⟩ = some ⟨none, W⟩ := by
    have e₀ : toTM g (.inl x.pc) (fun i => (T i).view 0) = none := by
      change ((toTM g (.inl x.pc) (fun i => (T i).view 0)).map _) = none at hh
      cases e : toTM g (.inl x.pc) (fun i => (T i).view 0) <;> simp_all
    change (withOutput k (toTM g) _ (fun i => (W i).view 0)).map _ = _
    unfold withOutput
    simp only [show (fun i => (W (some i)).view 0) = (fun i => (T i).view 0) from rfl, e₀,
      Option.map_some, Option.some.injEq]
    simp [preserve, Action.apply_stay]
  obtain ⟨ts', hd, halt, hw⟩ := drain (ts := W) (m := toTM g) (k := k) (he k)
  refine ⟨⟨none, ts'⟩, Trace.trans (Trace.trans hp (Trace.single hemit₁)) hd, halt, ?_⟩
  funext j
  have heq := hw j
  have hz : (W none).pos = 0 := rfl
  rw [hz, zero_add, sub_zero] at heq
  change (ts' none).absolute j = (Tape.loaded none _).view (j-0)
  rw [sub_zero, heq, display_loaded]
  split
  · rfl
  · next hn =>
    change U.view (j-0) = display _ j
    rw [sub_zero, show U.view=display [] from display_loaded [], display_empty]
    cases j with
    | negSucc _ => rfl
    | ofNat b =>
      change none = (x.stack k)[b]?
      apply Eq.symm
      apply List.getElem?_eq_none
      change ¬ ((0:ℤ) ≤ (b:ℤ) ∧ (b:ℤ) < _) at hn
      omega
end SM

end IntegerMultiplication
end Computability
end OAI

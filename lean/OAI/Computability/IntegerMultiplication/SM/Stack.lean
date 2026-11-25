import OAI.Computability.IntegerMultiplication.TMModel

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace SM
variable {A Q I : Type}

structure Config (A Q I : Type) where
  pc : Q
  stack : I → List A

inductive Action (A : Type)
  | push (a : A)
  | pop
  | skip

namespace Action
variable (act : Action A)

def perform (s : List A) : List A :=
  match act with
  | push a => a::s
  | pop => s.tail
  | skip => s
end Action

abbrev Rule (A Q I : Type) :=
  Q → (I → Option A) → Option (Q × (I → Action A))

def tops (x : Config A Q I) : I → Option A := fun i => (x.stack i).head?

def perform (x : Config A Q I) (y : Q × (I → Action A)) : Config A Q I :=
  ⟨y.1, fun i => (y.2 i).perform (x.stack i)⟩

def advance (m : Rule A Q I) (x : Config A Q I) : Option (Config A Q I) :=
  (m x.pc (tops x)).map (perform x)

/-!
## Simulation on tapes

Represent a stack with symbols A by symbols Option A, with the top under the head
and the rest to the right, everywhere else blank. Arbitrary absolute position.
-/

open TM (Tape)

def display (s : List A) : ℤ → Option A
  | .ofNat n => s[n]?
  | .negSucc _ => none

def faithful (s : I → List A) (T : I → Tape (Option A)) : Prop :=
  ∀ i, (T i).view = display (s i)

@[simp]
theorem display_top (s : List A) : display s 0 = s.head? := by
  cases s <;> rfl

@[simp]
theorem display_empty : display ([] : List A) = fun _ => none := by
  funext i
  cases i <;> simp [display]

theorem display_loaded (s : List A) :
    (Tape.loaded (none : Option A) (s.map some)).view = display s := by
  funext i
  cases i with
  | ofNat n =>
    simp only [Tape.loaded, display, List.getElem?_map]
    cases s[n]? <;> rfl
  | negSucc n => rfl

namespace Action
variable (act : Action A)

def first (top : Option A) : Option A × TM.Move :=
  match act with
  | push _ => (top, .left)
  | pop =>
    match top with
    | none => (none, .stay)
    | some _ => (none, .right)
  | skip => (top, .stay)

def second (top : Option A) : Option A × TM.Move :=
  match act with
  | push a => (some a, .stay)
  | _ => (top, .stay)

-- push identity for relative array
private theorem push_array (a : A) (s : List A) (i : ℤ) :
    (if i = 0 then some a else display s (i-1)) = display (a::s) i := by
  cases i with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      have h : Int.ofNat (n+1) ≠ 0 := by
        exact fun g => Nat.succ_ne_zero n (Int.ofNat.inj g)
      have e : Int.ofNat (n+1) - 1 = Int.ofNat n := by change (↑(n+1) : ℤ) - 1 = n; omega
      rw [ite_eq_right h, e]; rfl
  | negSucc n =>
    have h : Int.negSucc n ≠ 0 := by omega
    have e : Int.negSucc n - 1 = Int.negSucc (n+1) := by omega
    simp [h, e, display]

theorem pop_array (a : A) (s : List A) (i : ℤ) :
    (if i + 1 = 0 then none else display (a::s) (i+1)) = display s i := by
  cases i with
  | ofNat n =>
    have h : Int.ofNat n + 1 = Int.ofNat (n+1) := rfl
    have e : Int.ofNat (n+1) ≠ 0 := by
        exact fun g => Nat.succ_ne_zero n (Int.ofNat.inj g)
    rw [h, ite_eq_right e]; rfl
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n =>
      have h : Int.negSucc (n+1) + 1 = Int.negSucc n := by omega
      have e : Int.negSucc n ≠ 0 := by omega
      simp [h, e, display]

theorem apply_stay {A' : Type} (T : Tape A') :
    T.apply (T.view 0, .stay) = T := by
  unfold Tape.apply
  simp only [TM.Move.shift, add_zero]
  have h : (fun i : ℤ => if i = 0 then T.view 0 else T.view i) = T.view := by
    funext i; split <;> simp_all
  rw [h]

theorem represent_perform (T : Tape (Option A)) (s : List A) (hs : T.view = display s) :
    let T' := T.apply (act.first (T.view 0))
    (T'.apply (act.second (T'.view 0))).view = display (act.perform s) := by
  cases act with
  | skip =>
    change ((T.apply (T.view 0, .stay)).apply (_, .stay)).view = display s
    simpa only [first, apply_stay] using hs
  | pop =>
    dsimp
    rw [show second (pop : Action A) = (fun top => (top, TM.Move.stay)) from rfl, apply_stay]
    cases s with
    | nil =>
      have e : T.view 0 = none := by rw [hs]; rfl
      rw [e, first, ← e, apply_stay]
      exact hs
    | cons a s =>
      have e : T.view 0 = some a := by rw [hs]; rfl
      funext i
      rw [e]
      simp only [perform, List.tail_cons, first, Tape.apply, TM.Move.shift, hs, pop_array]
  | push a =>
    funext i
    dsimp [perform, first, second, Tape.apply, TM.Move.shift]
    -- the first step wrote the same symbol and moved left
    simp only [add_zero, hs, show i + (-1 : ℤ) = i - 1 by omega]
    rw [ite_congr rfl (fun _ => rfl)
      (show ¬i = 0 → (if i - 1 = 0 then display s 0 else display s (i - 1)) =
        display s (i - 1) by
          intro _; split <;> simp_all)]
    exact push_array a s i
end Action

/-- At the intermediate PC retain the tuple with the destination PC and all actions. -/
abbrev PC (A Q I : Type) := Sum Q (Q × (I → Action A))

def toTM (m : Rule A Q I) : TM.Rule (Option A) (PC A Q I) I
  | .inl pc, top => (m pc top).map
      fun y => (.inr y, fun i => (y.2 i).first (top i))
  | .inr y, top => some (.inl y.1, fun i => (y.2 i).second (top i))

theorem simulate {m : Rule A Q I} {x y : Config A Q I} {n}
    (h : Trace (advance m) x n y) (T : I → Tape (Option A)) (he : faithful x.stack T) :
    ∃ T', faithful y.stack T' ∧
      Trace (TM.advance (toTM m)) ⟨.inl x.pc, T⟩ (2*n) ⟨.inl y.pc, T'⟩ := by
  induction h generalizing T with
  | nil z => exact ⟨T, he, by simpa using (Trace.nil (step := TM.advance (toTM m)) (TM.Config.mk (Sum.inl z.pc) T))⟩
  | @cons x u v n h _ ih =>
    cases hy : m x.pc (tops x) with
    | none => simp [advance, hy] at h
    | some y =>
      simp only [advance, hy, Option.map_some, Option.some.injEq] at h
      subst u
      have ht : (fun i => (T i).view 0) = tops x := by funext i; rw [he]; simp [tops]
      let T₁ : I → Tape (Option A) := fun i => (T i).apply ((y.2 i).first ((T i).view 0))
      let T₂ : I → Tape (Option A) := fun i => (T₁ i).apply ((y.2 i).second ((T₁ i).view 0))
      have h₁ : TM.advance (toTM m) ⟨.inl x.pc, T⟩ = some ⟨.inr y, T₁⟩ := by
        unfold TM.advance
        simp only [toTM, ht, hy, Option.map_some]
        simp [T₁]
      have h₂ : TM.advance (toTM m) ⟨.inr y, T₁⟩ = some ⟨.inl y.1, T₂⟩ := rfl
      obtain ⟨T', he', hr⟩ := ih T₂ fun i =>
        (y.2 i).represent_perform (T i) (x.stack i) (he i)
      refine ⟨T', he', ?_⟩
      rw [show 2*(1+n)=1+(1+2*n) by omega]
      exact Trace.cons h₁ (Trace.cons h₂ hr)

theorem simulate_halt {m : Rule A Q I} {x : Config A Q I}
    (h : advance m x = none) {T} (he : faithful x.stack T) :
    TM.advance (toTM m) ⟨.inl x.pc, T⟩ = none := by
  cases hy : m x.pc (tops x) with
  | some y => simp [advance, hy] at h
  | none =>
    have ht : (fun i => (T i).view 0) = tops x := by funext i; rw [he]; simp [tops]
    simp [TM.advance, toTM, ht, hy]

end SM

end IntegerMultiplication
end Computability
end OAI

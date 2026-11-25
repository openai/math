import OAI.Computability.NearSquareRoot.ScheduleInterpreterTrial

/-!
# Physical time slicing of a fixed multitape interpreter

The clock runs on its own tapes. At an outgoing pulse the executor advances
on its own tapes in the very same transition. Its heads and symbols otherwise
stay put. A halt consulted at a pulse finishes the trial immediately. Reaching
the clock's halt without a finished trial signals timeout.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Timed

open IntegerMultiplication TM

variable {A Q I B R J : Type}

private def mapTape {D E : Type} (f : D → E) (t : Tape D) : Tape E :=
  ⟨t.pos, f ∘ t.view⟩

private theorem map_apply {D E : Type} (f : D → E) (x : Tape D) (a : D) (d : Move) :
    (mapTape f x).apply (f a, d) = mapTape f (x.apply (a, d)) := by
  unfold mapTape Tape.apply
  congr 1
  funext k
  simp only [Function.comp_apply]
  split <;> rfl

private theorem stay_put {D : Type} (t : Tape D) : t.apply (t.view 0, Move.stay) = t := by
  cases t with
  | mk p f =>
    simp [Tape.apply, Move.shift]
    funext k
    split <;> simp_all

/-- Local state and symbol alphabets combine into one finite control and
one finite alphabet when the constituent machines have finite controls. -/
def pack (x : Config A Q I) (c : Config B R J) :
    Config (A ⊕ B) (Q × R) (I ⊕ J) :=
  ⟨(x.pc,c.pc), Sum.elim (fun i => mapTape Sum.inl (x.tape i))
    (fun j => mapTape Sum.inr (c.tape j))⟩

private def actions (w : I → A × Move) (u : J → B × Move) :
    (I ⊕ J) → (A ⊕ B) × Move :=
  Sum.elim (fun i => (.inl (w i).1, (w i).2)) (fun j => (.inr (u j).1, (u j).2))

/-- Both tables read only finite control and the currently scanned symbols.
The two defaults specify actions on noncanonical cross-alphabet reads. -/
def rule (a₀ : A) (b₀ : B) (m : Rule A Q I) (p : Rule B R J) (pulse : R → Bool) :
    Rule (A ⊕ B) (Q × R) (I ⊕ J) := fun (q,r) heads => do
  let a := fun i => (heads (.inl i)).elim id (fun _ => a₀)
  let b := fun j => (heads (.inr j)).elim (fun _ => b₀) id
  let (r', co) ← p r b
  if pulse r then
    let (q', wo) ← m q a
    some ((q',r'), actions wo co)
  else
    some ((q,r'), actions (fun i => (a i, .stay)) co)

/-- A single transition implements simultaneous updates on a pulse and a
clock step with a read-only stationary work head between pulses. -/
theorem advance_pack (a₀ : A) (b₀ : B) (m : Rule A Q I) (p : Rule B R J)
    (pulse : R → Bool) (x : Config A Q I) (c : Config B R J) :
    advance (rule a₀ b₀ m p pulse) (pack x c) =
      (advance p c).bind (fun d =>
        if pulse c.pc then (advance m x).map (fun y => pack y d)
        else some (pack x d)) := by
  cases hc : p c.pc (fun j => (c.tape j).view 0) with
  | none => simp [advance, rule, pack, mapTape, hc]
  | some co =>
    obtain ⟨r, u⟩ := co
    cases hp : pulse c.pc with
    | false =>
      simp [advance, rule, pack, mapTape, hc, hp]
      funext i
      cases i with
      | inl i => exact stay_put _
      | inr j => exact map_apply Sum.inr _ _ _
    | true =>
      cases ha : m x.pc (fun i => (x.tape i).view 0) with
      | none => simp [advance, rule, pack, mapTape, hc, hp, ha]
      | some wo =>
        obtain ⟨q, w⟩ := wo
        simp [advance, rule, pack, mapTape, hc, hp, ha]
        funext i
        cases i with
        | inl i => exact map_apply Sum.inl _ _ _
        | inr j => exact map_apply Sum.inr _ _ _

/-- Instrument the clock's transition with the count of executor consultations. -/
def countStep (p : Rule B R J) (pulse : R → Bool) (z : Config B R J × ℕ) :
    Option (Config B R J × ℕ) :=
  (advance p z.1).map (fun d => (d,z.2+(pulse z.1.pc).toNat))

private theorem count_mono {p : Rule B R J} {pulse : R → Bool} {u v : Config B R J × ℕ}
    {k : ℕ} (run : Trace (countStep p pulse) u k v) : u.2 ≤ v.2 := by
  induction run with
  | nil => rfl
  | @cons u w v n hs _ ih =>
    unfold countStep at hs
    cases hp : advance p u.1 with
    | none => simp [hp] at hs
    | some d =>
      simp [hp] at hs
      subst w
      exact (Nat.le_add_right ..).trans ih

/-- Decode the reason for a stopped combined trial. A clock halt means
timeout. At an earlier halt the state of the candidate determines acceptance. -/
def answer (p : Rule B R J) (accept : Q → Bool) (x : Config A Q I) (c : Config B R J) :
    Option (Config A Q I) :=
  if (advance p c).isSome && accept x.pc then some x else none

/-- A trace of the clock with `v.2-u.2` pulses gives the exact bounded-trial
answer. Every counted transition on the clock is a physical transition on the
combined tapes. An early executor halt may shorten the physical trace. -/
theorem execute (a₀ : A) (b₀ : B) (m : Rule A Q I) (p : Rule B R J)
    (pulse : R → Bool) (accept : Q → Bool) (x : Config A Q I)
    {u v : Config B R J × ℕ} {k : ℕ} (clock : Trace (countStep p pulse) u k v)
    (expired : advance p v.1 = none) :
    ∃ t ≤ k, ∃ y c,
      Trace (advance (rule a₀ b₀ m p pulse)) (pack x u.1) t (pack y c) ∧
      advance (rule a₀ b₀ m p pulse) (pack y c) = none ∧
      answer p accept y c = Schedule.tryFor (tapeTick m accept) (v.2-u.2) x := by
  induction clock generalizing x with
  | nil z =>
    exact ⟨0, le_rfl, x, z.1, .nil _, by simp [advance_pack, expired],
      by simp [answer, expired, Schedule.tryFor]⟩
  | @cons s w v k hstep tail ih =>
    cases hp : advance p s.1 with
    | none => simp [countStep, hp] at hstep
    | some d =>
      have he : (d, s.2+(pulse s.1.pc).toNat) = w := by simpa [countStep, hp] using hstep
      subst w
      have hcount := count_mono tail
      cases hPulse : pulse s.1.pc with
      | false =>
        obtain ⟨t, ht, y, c, run, halt, out⟩ := ih x expired
        refine ⟨1+t, by omega, y, c, .cons ?_ run, halt, ?_⟩
        · simp [advance_pack, hp, hPulse]
        · simpa [hPulse] using out
      | true =>
        simp only [hPulse, Bool.toNat_true] at hcount
        have heq : v.2-s.2 = (v.2-(s.2+1))+1 := by omega
        cases hw : advance m x with
        | none =>
          refine ⟨0, Nat.zero_le _, x, s.1, .nil _, ?_, ?_⟩
          · simp [advance_pack, hp, hPulse, hw]
          · cases ok : accept x.pc <;> simp [answer, hp, heq, Schedule.tryFor, tapeTick, hw, ok]
        | some x' =>
          obtain ⟨t, ht, y, c, run, halt, out⟩ := ih x' expired
          refine ⟨1+t, by omega, y, c, .cons ?_ run, halt, ?_⟩
          · simp [advance_pack, hp, hPulse, hw]
          · simpa [heq, Schedule.tryFor, tapeTick, hw, hPulse] using out

/-- Project any physical prefix onto clock steps and work steps. This lets the
space bounds for the two component tape families be charged separately. -/
theorem project_prefix (a₀ : A) (b₀ : B) (m : Rule A Q I) (p : Rule B R J) (pulse : R → Bool)
    {x : Config A Q I} {c : Config B R J} {k : ℕ} {w : Config (A ⊕ B) (Q × R) (I ⊕ J)}
    (h : Trace (advance (rule a₀ b₀ m p pulse)) (pack x c) k w) :
    ∃ y d, w = pack y d ∧ Trace (advance p) c k d ∧ ∃ j ≤ k, Trace (advance m) x j y := by
  generalize hw : pack x c = z at h
  induction h generalizing c x with
  | nil z => exact ⟨x, c, hw.symm, .nil _, 0, le_rfl, .nil _⟩
  | @cons z u w k hs _ ih =>
    subst z
    rw [advance_pack] at hs
    cases hp : advance p c with
    | none => simp [hp] at hs
    | some d =>
      cases hPulse : pulse c.pc with
      | false =>
        have he : pack x d = u := by simpa [hp, hPulse] using hs
        obtain ⟨y, d', hpack, hc, j, hj, hx⟩ := ih he
        exact ⟨y,d',hpack,.cons hp hc,j,by omega,hx⟩
      | true =>
        cases hm : advance m x with
        | none => simp [hp, hm, hPulse] at hs
        | some x' =>
          have he : pack x' d = u := by simpa [hp, hm, hPulse] using hs
          obtain ⟨y, d', hpack, hc, j, hj, hx⟩ := ih he
          exact ⟨y,d',hpack,.cons hp hc,1+j,by omega,.cons hm hx⟩

/-- Disjoint physical tape banks contribute their numbers of distinct visited
cells additively. This applies to unsuccessful trials and to any prefix. -/
theorem visits (a₀ : A) (b₀ : B) (m : Rule A Q I) (p : Rule B R J) (pulse : R → Bool)
    {x : Config A Q I} {c : Config B R J} {n sx sc : ℕ}
    (hx : VisitsAtMost m x n sx) (hc : VisitsAtMost p c n sc) :
    VisitsAtMost (rule a₀ b₀ m p pulse) (pack x c) n (sx+sc) := by
  classical
  obtain ⟨X, hX, pX⟩ := hx
  obtain ⟨C, hC, pC⟩ := hc
  let l : (I × ℤ) ↪ ((I ⊕ J) × ℤ) :=
    ⟨fun a => (.inl a.1,a.2), fun a b h => by cases a; cases b; simpa using h⟩
  let r : (J × ℤ) ↪ ((I ⊕ J) × ℤ) :=
    ⟨fun a => (.inr a.1,a.2), fun a b h => by cases a; cases b; simpa using h⟩
  refine ⟨X.map l ∪ C.map r, (Finset.card_union_le ..).trans ?_, ?_⟩
  · simpa using Nat.add_le_add hX hC
  · intro k hk w hw i
    obtain ⟨y,d,rfl,clk,j,hj,work⟩ := project_prefix a₀ b₀ m p pulse hw
    cases i with
    | inl i =>
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨_, pX j (hj.trans hk) _ work i, rfl⟩)
    | inr i =>
      exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨_, pC k hk _ clk i, rfl⟩)

end Uniform.Timed

end NearSquareRoot
end Computability
end OAI

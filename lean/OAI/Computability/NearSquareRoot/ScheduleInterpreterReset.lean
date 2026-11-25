import OAI.Computability.IntegerMultiplication.TMModel

/-! Exact erase-and-rewind trace on a marked visited interval. Static tracks
(such as previously installed fences) are carried unchanged. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Reset

open IntegerMultiplication IntegerMultiplication.TM

structure Cell (A F : Type) where
  val : A
  fixed : F
  origin : Bool
  leftEnd : Bool
  rightEnd : Bool

inductive Phase
  | seekLeft | erase | rewind | done

instance {A F : Type} [Finite A] [Finite F] : Finite (Cell A F) :=
  Finite.of_injective
    (fun v : Cell A F => (v.val, v.fixed, v.origin, v.leftEnd, v.rightEnd))
    (by rintro ⟨a, b, c, d, e⟩ ⟨a', b', c', d', e'⟩ h; simpa using h)

private def Phase.code : Phase → Bool × Bool
  | .seekLeft => (false, false)
  | .erase => (false, true)
  | .rewind => (true, false)
  | .done => (true, true)

instance : Finite Phase := Finite.of_injective Phase.code (by
  intro x y
  cases x <;> cases y <;> simp [Phase.code])

variable {A F : Type}

/-- Clear volatile data, restoring the singleton frontier at the origin. -/
def Cell.restore (base : F → A) (v : Cell A F) : Cell A F :=
  { v with val := base v.fixed, leftEnd := v.origin, rightEnd := v.origin }

/-- One fixed scratch head. Every returned operation writes and moves according
to the usual physical multitape transition semantics. -/
def restoringRule (base : F → A) : Rule (Cell A F) Phase Unit := fun q read =>
  let v := read ()
  match q with
  | .seekLeft =>
    if v.leftEnd then some (.erase, fun _ => (v, .stay))
    else some (.seekLeft, fun _ => (v, .left))
  | .erase =>
    if v.rightEnd then some (.rewind, fun _ => (v.restore base, .stay))
    else some (.erase, fun _ => (v.restore base, .right))
  | .rewind =>
    if v.origin then some (.done, fun _ => (v, .stay))
    else some (.rewind, fun _ => (v, .left))
  | .done => none

/-- Tape with absolute contents `f` and absolute head coordinate `p`. -/
def atHead {C : Type} (p : ℤ) (f : ℤ → C) : Tape C :=
  ⟨p, fun i => f (p + i)⟩

def config (q : Phase) (p : ℤ) (f : ℤ → Cell A F) : Config (Cell A F) Phase Unit :=
  ⟨q, fun _ => atHead p f⟩

/-- Standard endpoint and origin markers. -/
def marked (l r o : ℤ) (data : ℤ → A) (persist : ℤ → F) (i : ℤ) : Cell A F :=
  ⟨data i, persist i, decide (i = o), decide (i = l), decide (i = r)⟩

/-- `[l,u)` has been cleared; `[u,r]` is awaiting erasure. -/
def restoringSweep (base : F → A) (l u : ℤ) (f : ℤ → Cell A F) (i : ℤ) : Cell A F :=
  if l ≤ i ∧ i < u then (f i).restore base else f i

theorem atHead_apply {C : Type} (p : ℤ) (f : ℤ → C) (v : C) (d : Move) :
    (atHead p f).apply (v, d) =
      atHead (p + d.shift) (Function.update f p v) := by
  unfold atHead Tape.apply
  congr 1
  funext i
  simp only [Function.update_apply]
  by_cases h : i + d.shift = 0
  · simp [h, show p + d.shift + i = p by omega]
  · simp [h, show p + d.shift + i ≠ p by omega, show p + (i + d.shift) = p + d.shift + i by omega]

private theorem step (base : F → A) {q q' : Phase} {p : ℤ} {f : ℤ → Cell A F}
    {v : Cell A F} {d : Move}
    (h : restoringRule base q (fun _ => f p) = some (q', fun _ => (v, d))) :
    advance (restoringRule base) (config q p f) =
      some (config q' (p + d.shift) (Function.update f p v)) := by
  unfold advance
  change (restoringRule base q (fun _ => f (p + 0))).map _ = _
  rw [add_zero, h]
  change some (⟨q', fun _ => (atHead p f).apply (v, d)⟩ : Config (Cell A F) Phase Unit) = _
  rw [atHead_apply]
  rfl

private theorem unchanged (base : F → A) {q q' : Phase} {p : ℤ} {f : ℤ → Cell A F}
    {d : Move}
    (h : restoringRule base q (fun _ => f p) = some (q', fun _ => (f p, d))) :
    advance (restoringRule base) (config q p f) = some (config q' (p + d.shift) f) := by
  simpa using step base h

private theorem swept_update (base : F → A) {l p : ℤ} (hl : l ≤ p) (f : ℤ → Cell A F) :
    Function.update (restoringSweep base l p f) p ((f p).restore base) =
      restoringSweep base l (p+1) f := by
  funext i
  by_cases hi : i = p
  · subst i
    simp [restoringSweep, hl]
  · simp only [Function.update_of_ne hi, restoringSweep]
    have heq : (l ≤ i ∧ i < p) ↔ (l ≤ i ∧ i < p+1) := by omega
    simp [heq]

/-- Restrict the source of each step in a trace. This auxiliary relation is
only used to certify the positions of the physical heads. -/
private def checked (base : F → A) (l r : ℤ) (x : Config (Cell A F) Phase Unit) :=
  if l ≤ (x.tape ()).pos ∧ (x.tape ()).pos ≤ r then advance (restoringRule base) x else none

private theorem checked_step (base : F → A) {l r p : ℤ} {f : ℤ → Cell A F} {q : Phase}
    {y : Config (Cell A F) Phase Unit}
    (h : advance (restoringRule base) (config q p f) = some y) (hl : l ≤ p) (hr : p ≤ r) :
    checked base l r (config q p f) = some y := by
  simpa [checked, config, atHead, hl, hr] using h

private theorem seek (base : F → A) {l r : ℤ} (f : ℤ → Cell A F)
    (leftMark : ∀ i, (f i).leftEnd = decide (i = l)) (d : ℕ) (hr : l + d ≤ r) :
    Trace (checked base l r) (config .seekLeft (l + d) f) (d+1)
      (config .erase l f) := by
  induction d with
  | zero =>
    simpa [Move.shift] using (Trace.single (checked_step base (l := l) (r := r) (unchanged base
      (q := .seekLeft) (q' := .erase) (d := .stay) (p := l) (f := f) (by simp [restoringRule, leftMark])) le_rfl (by omega)))
  | succ d ih =>
    have hs := unchanged base (q := .seekLeft) (q' := .seekLeft) (d := .left)
      (p := l + ((d+1 : ℕ) : ℤ)) (f := f) (by
        simp [restoringRule, leftMark]; omega)
    have hm : l + ((d+1 : ℕ) : ℤ) + Move.left.shift = l + (d : ℤ) := by
      simp only [Move.shift]; omega
    rw [hm] at hs
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Trace.cons (checked_step base hs (by omega) hr) (ih (by omega))

private theorem erase (base : F → A) {l r : ℤ} (f : ℤ → Cell A F)
    (rightMark : ∀ i, (f i).rightEnd = decide (i = r)) (d : ℕ) :
    ∀ p : ℤ, l ≤ p → p + d = r →
    Trace (checked base l r) (config .erase p (restoringSweep base l p f)) (d+1)
      (config .rewind r (restoringSweep base l (r+1) f)) := by
  induction d with
  | zero =>
    intro p hp hr
    have : p = r := by omega
    subst p
    have hs := step base (q := .erase) (q' := .rewind) (d := .stay)
      (p := r) (f := restoringSweep base l r f) (v := (f r).restore base) (by
        simp [restoringRule, restoringSweep, rightMark])
    simpa [Move.shift, swept_update base hp] using Trace.single (checked_step base hs hp le_rfl)
  | succ d ih =>
    intro p hp hr
    have hs := step base (q := .erase) (q' := .erase) (d := .right)
      (p := p) (f := restoringSweep base l p f) (v := (f p).restore base) (by
        simp [restoringRule, restoringSweep, rightMark, show p ≠ r by omega])
    rw [swept_update base hp] at hs
    have ht := ih (p+1) (by omega) (by omega)
    simpa [Move.shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Trace.cons (checked_step base hs hp (by omega)) ht

private theorem rewind (base : F → A) {l r o : ℤ} (f : ℤ → Cell A F)
    (originMark : ∀ i, (f i).origin = decide (i = o)) (d : ℕ) (hl : l ≤ o) (hr : o + d ≤ r) :
    Trace (checked base l r) (config .rewind (o + d) f) (d+1)
      (config .done o f) := by
  induction d with
  | zero =>
    simpa [Move.shift] using (Trace.single (checked_step base (l := l) (r := r) (unchanged base
      (q := .rewind) (q' := .done) (d := .stay) (p := o) (f := f) (by simp [restoringRule, originMark])) hl (by omega)))
  | succ d ih =>
    have hs := unchanged base (q := .rewind) (q' := .rewind) (d := .left)
      (p := o + ((d+1 : ℕ) : ℤ)) (f := f) (by
        simp [restoringRule, originMark]; omega)
    have hm : o + ((d+1 : ℕ) : ℤ) + Move.left.shift = o + (d : ℤ) := by
      simp only [Move.shift]; omega
    rw [hm] at hs
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Trace.cons (checked_step base hs (by omega) hr) (ih (by omega))

/-- Erase exactly a visited interval, preserve every immutable track, restore
the singleton frontier at the origin, and halt with the head there. This works
also for a singleton interval and for an origin at either endpoint. -/
private theorem checked_cleanup (base : F → A) (l r o p : ℤ) (data : ℤ → A) (persist : ℤ → F)
    (hlp : l ≤ p) (hpr : p ≤ r) (hlo : l ≤ o) (hor : o ≤ r) :
    let src := marked l r o data persist
    let dst := marked o o o (fun i => if l ≤ i ∧ i ≤ r then base (persist i) else data i) persist
    let t := (p-l).toNat + (r-l).toNat + (r-o).toNat + 3
    Trace (checked base l r) (config .seekLeft p src) t (config .done o dst) ∧
      advance (restoringRule base) (config .done o dst) = none ∧ t ≤ 3 * ((r-l).toNat + 1) := by
  let f := marked l r o data persist
  let g := restoringSweep base l (r+1) f
  have h1 := seek base (r := r) f (fun _ => rfl) (p-l).toNat (by omega)
  have h2 := erase base f (fun _ => rfl) (r-l).toNat l le_rfl (by omega)
  have h3 := rewind base g (o := o) (by
    intro i
    simp only [g, restoringSweep]
    split <;> rfl) (r-o).toNat hlo (by omega : o + ((r-o).toNat : ℤ) ≤ r)
  have hs : restoringSweep base l l f = f := by
    funext i
    simp [restoringSweep, show ¬(l ≤ i ∧ i < l) by omega]
  rw [show l + ((p-l).toNat : ℤ) = p by omega] at h1
  rw [hs] at h2
  rw [show o + ((r-o).toNat : ℤ) = r by omega] at h3
  have hg : g = marked o o o (fun i => if l ≤ i ∧ i ≤ r then base (persist i) else data i) persist := by
    funext i
    dsimp [g, restoringSweep, f, marked, Cell.restore]
    by_cases h : l ≤ i ∧ i ≤ r
    · simp [h, show l ≤ i ∧ i < r+1 by omega]
    · simp [h, show ¬(l ≤ i ∧ i < r+1) by omega,
        show i ≠ o by omega, show i ≠ l by omega, show i ≠ r by omega]
  have ht := (h1.trans h2).trans h3
  rw [hg] at ht
  refine ⟨?_, rfl, ?_⟩
  · rw [show (p-l).toNat + (r-l).toNat + (r-o).toNat + 3 =
          ((p-l).toNat+1 + ((r-l).toNat+1)) + ((r-o).toNat+1) by omega]
    exact ht
  · omega

private theorem checked_sound {base : F → A} {l r : ℤ} {x z : Config (Cell A F) Phase Unit}
    {t : ℕ} (h : Trace (checked base l r) x t z) :
    Trace (advance (restoringRule base)) x t z := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    unfold checked at hs
    split at hs
    · exact .cons hs ih
    · cases hs

private theorem checked_prefix {base : F → A} {l r : ℤ} {x z : Config (Cell A F) Phase Unit}
    {t : ℕ} (h : Trace (checked base l r) x t z)
    (hz : l ≤ (z.tape ()).pos ∧ (z.tape ()).pos ≤ r) :
    ∀ {k y}, k ≤ t → Trace (advance (restoringRule base)) x k y →
      l ≤ (y.tape ()).pos ∧ (y.tape ()).pos ≤ r := by
  induction h with
  | nil =>
    intro k y hk hy
    cases hy with
    | nil => exact hz
    | cons => omega
  | cons hs _ ih =>
    unfold checked at hs
    split at hs
    · rename_i hx
      intro k y hk hy
      cases hy with
      | nil => exact hx
      | cons hstep ht =>
        rw [hs] at hstep
        cases hstep
        exact ih hz (by omega) ht
    · cases hs

/-- The physical rule restores the singleton frontier and returns to the origin
in at most three times the visited interval size. -/
theorem cleanup_restore (base : F → A) (l r o p : ℤ) (data : ℤ → A) (persist : ℤ → F)
    (hlp : l ≤ p) (hpr : p ≤ r) (hlo : l ≤ o) (hor : o ≤ r) :
    let src := marked l r o data persist
    let dst := marked o o o (fun i => if l ≤ i ∧ i ≤ r then base (persist i) else data i) persist
    let t := (p-l).toNat + (r-l).toNat + (r-o).toNat + 3
    Trace (advance (restoringRule base)) (config .seekLeft p src) t (config .done o dst) ∧
      advance (restoringRule base) (config .done o dst) = none ∧ t ≤ 3 * ((r-l).toNat + 1) := by
  obtain ⟨ht, hh, hb⟩ := checked_cleanup base l r o p data persist hlp hpr hlo hor
  exact ⟨checked_sound ht, hh, hb⟩

/-- Every prefix of the actual cleanup trace is confined to the marked interval. -/
theorem cleanup_restore_prefix (base : F → A) (l r o p : ℤ) (data : ℤ → A) (persist : ℤ → F)
    (hlp : l ≤ p) (hpr : p ≤ r) (hlo : l ≤ o) (hor : o ≤ r)
    {k : ℕ} {y : Config (Cell A F) Phase Unit}
    (hk : k ≤ (p-l).toNat + (r-l).toNat + (r-o).toNat + 3)
    (hy : Trace (advance (restoringRule base)) (config .seekLeft p (marked l r o data persist)) k y) :
    l ≤ (y.tape ()).pos ∧ (y.tape ()).pos ≤ r :=
  checked_prefix (checked_cleanup base l r o p data persist hlp hpr hlo hor).1 ⟨hlo, hor⟩ hk hy

/-- Constant-blank specializations for ordinary scratch tapes. -/
abbrev Cell.clear (blank : A) (v : Cell A F) := v.restore (fun _ => blank)

abbrev rule (blank : A) : Rule (Cell A F) Phase Unit := restoringRule (fun _ => blank)

abbrev swept (blank : A) (l u : ℤ) (f : ℤ → Cell A F) := restoringSweep (fun _ => blank) l u f

/-- The physical rule restores the singleton frontier and returns to the origin
in at most three times the visited interval size. -/
theorem cleanup (blank : A) (l r o p : ℤ) (data : ℤ → A) (persist : ℤ → F)
    (hlp : l ≤ p) (hpr : p ≤ r) (hlo : l ≤ o) (hor : o ≤ r) :
    let src := marked l r o data persist
    let dst := marked o o o (fun i => if l ≤ i ∧ i ≤ r then blank else data i) persist
    let t := (p-l).toNat + (r-l).toNat + (r-o).toNat + 3
    Trace (advance (rule blank)) (config .seekLeft p src) t (config .done o dst) ∧
      advance (rule blank) (config .done o dst) = none ∧ t ≤ 3 * ((r-l).toNat + 1) :=
  cleanup_restore (fun _ => blank) l r o p data persist hlp hpr hlo hor

/-- Every prefix of the actual cleanup trace is confined to the marked interval. -/
theorem cleanup_prefix (blank : A) (l r o p : ℤ) (data : ℤ → A) (persist : ℤ → F)
    (hlp : l ≤ p) (hpr : p ≤ r) (hlo : l ≤ o) (hor : o ≤ r)
    {k : ℕ} {y : Config (Cell A F) Phase Unit}
    (hk : k ≤ (p-l).toNat + (r-l).toNat + (r-o).toNat + 3)
    (hy : Trace (advance (rule blank)) (config .seekLeft p (marked l r o data persist)) k y) :
    l ≤ (y.tape ()).pos ∧ (y.tape ()).pos ≤ r :=
  cleanup_restore_prefix (fun _ => blank) l r o p data persist hlp hpr hlo hor hk hy

end Reset

end NearSquareRoot
end Computability
end OAI

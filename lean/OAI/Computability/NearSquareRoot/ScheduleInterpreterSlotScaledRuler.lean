import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotScaledSeed
import OAI.Computability.NearSquareRoot.ShortWordSpace
import Mathlib.Tactic.DeriveFintype

/-!
# Measuring a fixed multiple of the packed input length

In each of `D` passes the input and auxiliary heads move right together to
the first trailing blank. Only the input rewinds. After the last pass the
auxiliary head is at `D * L`; it sets its right boundary bit and rewinds.
All the other heads stay at the origin throughout. The number of passes is
stored in the finite control of the installer.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotScaledRuler
open IntegerMultiplication TM
variable {A I : Type}

inductive PC (D : ℕ)
  | scan (remaining : Fin (D+1))
  | back (remaining : Fin (D+1))
  | home
  deriving DecidableEq, Fintype

def start (D : ℕ) : PC D := .scan ⟨D, Nat.lt_succ_self _⟩
def done (D : ℕ) : PC D := .home

private def pick [DecidableEq I] {V : Type} (inp aux : I) (x y z : V) (j : I) : V :=
  if j = inp then x else if j = aux then y else z

private def rewindCount {D : ℕ} (r : Fin (D+1)) : Fin (D+1) := ⟨r.val-1, by omega⟩

def rule (D : ℕ) [DecidableEq I] [DecidableEq A] (inp aux : I) (blank : A) :
    Rule (Fence.Symbol A) (PC D) I
  | .scan r,h =>
    if r.val=0 then some (.home,fun j =>
      (if j=aux then SlotInstall.writeRight (h j) else h j,.stay))
    else if (h inp).1=blank then some (.back r, fun j => (h j,.stay))
    else some (.scan r,fun j => (h j,pick inp aux .right .right .stay j))
  | .back r,h =>
    if SlotInstall.atOrigin (h inp) then some (.scan (rewindCount r),fun j => (h j,.stay))
    else some (.back r,fun j => (h j,pick inp aux .left .stay .stay j))
  | .home,h =>
    if SlotInstall.atOrigin (h aux) then none
    else some (.home,fun j => (h j,pick inp aux .stay .left .stay j))

private def atHead {S : Type} (f : ℤ → S) (p : ℤ) : Tape S :=
  ⟨p,fun j => f (p+j)⟩

private theorem mov {S : Type} (f : ℤ → S) (p : ℤ) (d : Move) :
    (atHead f p).apply (f p,d) = atHead f (p+d.shift) := by
  simp only [Tape.apply,atHead,Tape.mk.injEq,true_and]
  funext j
  split <;> congr 1 <;> omega

private theorem write {S : Type} (f : ℤ → S) (p : ℤ) (b : S) :
    (atHead f p).apply (b,.stay) = atHead (Function.update f p b) p := by
  simp only [Tape.apply,atHead,Move.shift,Int.add_zero,Tape.mk.injEq,true_and]
  funext j
  by_cases h : j=0 <;> simp [h]

variable [DecidableEq I] [DecidableEq A]
private def layout {S Q : Type} (inp aux : I) (q : Q) (f : I → ℤ → S) (x y : ℕ) :
    Config S Q I :=
  ⟨q,fun j => atHead (f j) (pick inp aux (x : ℤ) y 0 j)⟩

omit [DecidableEq A] in
private theorem atZero {S Q : Type} (inp aux : I) (q : Q) (f : I → ℤ → S) :
    layout inp aux q f 0 0 = SlotInstall.base q f := by
  apply congrArg (Config.mk q)
  funext j
  simp [atHead,pick]

private abbrev Contents := I → ℤ → Fence.Symbol A

omit [DecidableEq A] in
private theorem slide {Q : Type} (m : Rule (Fence.Symbol A) Q I)
    (inp aux : I) (q q' : Q) (f : Contents) (x y x' y' : ℕ) (dir : I → Move)
    (ht : m q (fun j => f j (pick inp aux (x:ℤ) y 0 j)) =
      some (q',fun j => (f j (pick inp aux (x:ℤ) y 0 j),dir j)))
    (hp : ∀ j, pick inp aux (x:ℤ) y 0 j + (dir j).shift = pick inp aux (x':ℤ) y' 0 j) :
    advance m (layout inp aux q f x y) = some (layout inp aux q' f x' y') := by
  simp only [advance,layout,atHead,Int.add_zero,ht,Option.map_some,Option.some.injEq,
    Config.mk.injEq,true_and]
  funext j
  change (atHead (f j) _).apply (_,dir j)=atHead (f j) _
  rw [mov,hp]

private def bare (f : I → ℤ → A) (R : ℕ) : I → ℤ → Fence.Symbol A :=
  SlotInstall.paint f R true false (fun _ => false)

variable (D : ℕ) (inp aux : I) (blank : A)
local notation "M" => rule D inp aux blank
local notation "cfg" => layout inp aux

private theorem scanStep (f : I → ℤ → A) (R k b : ℕ) (r : Fin (D+1))
    (hc : r.val ≠ 0) (hs : f inp k ≠ blank) :
    advance M (cfg (.scan r) (bare f R) k b) =
      some (cfg (.scan r) (bare f R) (k+1) (b+1)) := by
  apply slide M inp aux _ _ _ _ _ _ _ (pick inp aux .right .right .stay)
  · simp [rule, hc, pick, bare, SlotInstall.paint, hs]
  · intro j
    by_cases h : j=inp <;> by_cases h' : j=aux <;> simp_all [pick,Move.shift]

private theorem outward (f : I → ℤ → A) (R L b : ℕ) (r : Fin (D+1))
    (hc : r.val ≠ 0) (hs : ∀ k : ℕ, k<L → f inp k ≠ blank) :
    Trace (advance M) (cfg (.scan r) (bare f R) 0 b) L
      (cfg (.scan r) (bare f R) L (b+L)) := by
  induction L with
  | zero => simpa using Trace.nil (step := advance M) (cfg (.scan r) (bare f R) 0 b)
  | succ L ih =>
    exact (ih (fun k hk => hs k (by omega))).trans (.single
      (scanStep D inp aux blank f R L (b+L) r hc (hs L (by omega))))

private theorem turn (f : I → ℤ → A) (R L b : ℕ) (r : Fin (D+1)) (hc : r.val≠0)
    (he : f inp L = blank) :
    advance M (cfg (.scan r) (bare f R) L b) = some (cfg (.back r) (bare f R) L b) := by
  apply slide M inp aux _ _ _ _ _ _ _ (fun _ => .stay)
  · simp [rule,hc,bare,SlotInstall.paint,pick,he]
  · simp [Move.shift]

private theorem backStep (f : I → ℤ → A) (R k b : ℕ) (r : Fin (D+1)) :
    advance M (cfg (.back r) (bare f R) (k+1) b) = some (cfg (.back r) (bare f R) k b) := by
  apply slide M inp aux _ _ _ _ _ _ _ (pick inp aux .left .stay .stay)
  · simp [rule,pick,SlotInstall.atOrigin,bare,SlotInstall.paint]
    omega
  · intro j
    by_cases h : j=inp <;> by_cases h' : j=aux <;> simp_all [pick,Move.shift]

private theorem backward (f : I → ℤ → A) (R L b : ℕ) (r : Fin (D+1)) :
    Trace (advance M) (cfg (.back r) (bare f R) L b) L (cfg (.back r) (bare f R) 0 b) := by
  induction L with
  | zero => exact .nil _
  | succ L ih =>
    simpa only [Nat.add_comm 1 L] using Trace.cons (backStep D inp aux blank f R L b r) ih

private theorem nextPass (f : I → ℤ → A) (R b : ℕ) (r : Fin (D+1)) :
    advance M (cfg (.back r) (bare f R) 0 b) =
      some (cfg (.scan (rewindCount r)) (bare f R) 0 b) := by
  apply slide M inp aux _ _ _ _ _ _ _ (fun _ => .stay)
  · simp [rule,pick,SlotInstall.atOrigin,bare,SlotInstall.paint]
  · simp [Move.shift]

private theorem cycles (f : I → ℤ → A) (R L : ℕ)
    (hs : ∀ k : ℕ, k<L → f inp k ≠ blank) (he : f inp L = blank)
    (remaining : ℕ) (hc : remaining ≤ D) (b : ℕ) :
    Trace (advance M) (cfg (.scan ⟨remaining,by omega⟩) (bare f R) 0 b) (remaining*(2*L+2))
      (cfg (.scan 0) (bare f R) 0 (b+remaining*L)) := by
  induction remaining generalizing b with
  | zero => simpa using Trace.nil (step := advance M) (cfg (.scan 0) (bare f R) 0 b)
  | succ r ih =>
    let v : Fin (D+1) := ⟨r+1,by omega⟩
    have hv : v.val ≠ 0 := Nat.succ_ne_zero _
    have h₁ := outward D inp aux blank f R L b v hv hs
    have h₂ := turn D inp aux blank f R L (b+L) v hv he
    have h₃ := backward D inp aux blank f R L (b+L) v
    have h₄ := nextPass D inp aux blank f R (b+L) v
    dsimp [v,rewindCount] at h₄
    have h := ((((h₁.trans (.single h₂)).trans h₃).trans (.single h₄))).trans
      (ih (by omega) (b+L))
    rw [Nat.succ_mul r (2*L+2), Nat.succ_mul r L]
    rw [show r*(2*L+2)+(2*L+2) = L+1+L+1+r*(2*L+2) by omega,
      show b+(r*L+L)=b+L+r*L by omega]
    exact h

private theorem paintEndpoint (f : I → ℤ → A) (R : ℕ) (hR : 0<R) (ha : inp ≠ aux) :
    advance M (cfg (.scan 0) (bare f R) 0 R) =
      some (cfg .home (SlotScaledBroadcast.seed f R aux) 0 R) := by
  simp only [advance,layout,rule,Fin.val_zero,ite_true,Option.map_some,Option.some.injEq,
    Config.mk.injEq,true_and]
  funext j
  simp only [atHead,Int.add_zero]
  change (atHead _ _).apply (_,Move.stay) = atHead _ _
  rw [write]
  apply congrArg (fun g => atHead g _)
  funext p
  by_cases hj : j=aux
  · subst j
    by_cases hp : p=(R:ℤ)
    · subst p
      simp [pick,ha.symm,bare,SlotScaledBroadcast.seed,SlotInstall.paint,SlotInstall.writeRight,hR.ne']
    · simp [pick,ha.symm,bare,SlotScaledBroadcast.seed,SlotInstall.paint,hp]
  · by_cases hp : p = pick inp aux (0:ℤ) R 0 j <;> simp [hj,hp,bare,SlotScaledBroadcast.seed,SlotInstall.paint]

private theorem lastStep (f : I → ℤ → A) (R k : ℕ) (ha : inp ≠ aux) :
    advance M (cfg .home (SlotScaledBroadcast.seed f R aux) 0 (k+1)) =
      some (cfg .home (SlotScaledBroadcast.seed f R aux) 0 k) := by
  apply slide M inp aux _ _ _ _ _ _ _ (pick inp aux .stay .left .stay)
  · simp [rule,pick,ha.symm,SlotInstall.atOrigin,SlotScaledBroadcast.seed,SlotInstall.paint]
    omega
  · intro j
    by_cases h : j=inp <;> by_cases h' : j=aux <;> simp_all [pick,Move.shift]

private theorem lastRun (f : I → ℤ → A) (R k : ℕ) (ha : inp ≠ aux) :
    Trace (advance M) (cfg .home (SlotScaledBroadcast.seed f R aux) 0 k) k
      (cfg .home (SlotScaledBroadcast.seed f R aux) 0 0) := by
  induction k with
  | zero => exact .nil _
  | succ k ih =>
    simpa only [Nat.add_comm 1 k] using Trace.cons (lastStep D inp aux blank f R k ha) ih

/-- The full measuring command, including every rewind and both turn ticks of
each scan. The output differs at exactly the positive auxiliary endpoint. -/
theorem run (s : List A) (distinct : inp ≠ aux) (hD : 0<D) (hL : 0<s.length)
    (clean : blank ∉ s) :
    let f := fun j => (SlotInstall.loaded inp blank s j).view
    let R := D*s.length
    let last := SlotInstall.base (done D) (SlotScaledBroadcast.seed f R aux)
    Trace (advance M) (SlotInstall.base (start D) (SlotInstall.paint f R true false (fun _=>false)))
      (D*(2*s.length+2)+1+D*s.length) last ∧ advance M last = none := by
  let f := fun j => (SlotInstall.loaded inp blank s j).view
  let R := D*s.length
  have c := cycles D inp aux blank f R s.length (fun _ hk => SlotInstall.read_nonblank inp blank s clean hk)
    (SlotInstall.read_end inp blank s) D le_rfl 0
  rw [Nat.zero_add] at c
  have t := (c.trans (.single (paintEndpoint D inp aux blank f R (Nat.mul_pos hD hL) distinct))).trans
    (lastRun D inp aux blank f R R distinct)
  exact ⟨by simpa only [atZero,start,done,bare,f,R] using t, by
    simp [done,advance,rule,SlotInstall.base,SlotScaledBroadcast.seed,SlotInstall.paint,SlotInstall.atOrigin]⟩

end Uniform.SlotScaledRuler

end NearSquareRoot
end Computability
end OAI

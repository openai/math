import OAI.Computability.IntegerMultiplication.Brief.News
import OAI.Computability.IntegerMultiplication.Scale.Stars

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Bureau
open Scale Param Strip Code Brief
open Filter
variable {I:Type} (n:I→ℕ)
-- carrier volume unit
def ton (i:I):ℕ := Param.load (n i)* Scale.P (n i)
def token (i:I):ℝ := ton n i
def grant (f:I→ℝ) (i:I):ℝ:=token n i*f i
theorem tonp (i):1≤ton n i:=Nat.mul_pos (Nat.pow_pos (by decide)) (budget_p _)
theorem chargep (i):1≤token n i:=by unfold token; exact_mod_cast tonp n i
theorem mint_ {f:I→ℝ} (h:∀ i,1≤f i) (i):1≤grant n f i:=one_le_mul_of_one_le_of_one_le (chargep ..) (h _)
theorem one_frac (i):token n i=grant n (fun _=>1) i:= (mul_one ..).symm
theorem allow_ {f:I→ℝ} (h:∀ i,1≤f i) (i) : token n i≤ grant n f i:=
  le_mul_of_one_le_right (by unfold token; positivity) (h _)
abbrev cell := (Brief.journals n).header
abbrev close := Volume (token n)
abbrev Wood (p q:I→Tree) :=
  Carries (token n) (Strip.together (cell n) p) q
abbrev Spun (f:I→ℝ) (p q:I→Tree):=
  Carries (grant n f) (Strip.together (cell n) p) q
variable {n} {p q r S:I→Tree}
theorem dispatch (g:(Brief.city n).Small S): Carries (token n) (cell n) S :=
  (g.cooked (Brief.wealthy n)).larger (fun i=> by
    have p:Param.load (n i)≤ton n i := Nat.le_mul_of_pos_right _ (budget_p _)
    unfold token
    exact_mod_cast p)

theorem cityMark : close n (cell n):=
  (dispatch (Regime.self (r:=Brief.city n))).small

theorem me (u:close n p): Wood n p p :=
  Carries.dropLeft (chargep n) cityMark u
theorem scoop (u:close n p) : Wood n p (cell n) :=
  Carries.dropRight (chargep n) cityMark u
theorem rescue (u:close n p) (g:(Brief.city n).Small S): Wood n p S := (scoop u).chain (dispatch g)
theorem combine (g:Wood n p q) (t:Wood n q r): Wood n p r :=
  ((scoop (Volume.right g.small)).twice g).chain t
theorem inherit (g : Wood n p q){f:I→ℝ}(v:∀i,1≤f i):Spun n f p q :=
  g.larger (allow_ n v)

theorem transport {f:I→ℝ} (g:Spun n f p q)(t:Spun n f q r):Spun n f p r :=
  ((Carries.dropRight g.budget (Volume.left g.small) (Volume.right g.small)).twice g).chain t

theorem escalate {f a:I→ℝ} (g:Spun n f p q) (u:∀i,f i≤a i) : Spun n a p q :=
  g.larger (fun i=> by unfold grant token; gcongr; exact u _)
theorem dispatch_drop {f a:I→ℝ} (g : Spun n f p q) (h:∀ i,1≤a i) (m:ℕ) (e:∀ i,f i≤ m*a i): Spun n a p q:=
  g.times (mint_ n h) m (by intro i; unfold grant token; rw [mul_left_comm]; gcongr; exact e _)

-- cylinder cost f, stationary data must fit unit.  For loops use Dial on city with compressed header polynomial.
variable (n)
theorem allowance (i:ℕ): 1 ≤ Param.fund i := fund1 _
theorem eligible {w:ℕ→ℕ}(m:ℕ)(q:Large fun n=>w n≤ m*(budget n+1)):
    ∃ D:ℕ,∀ t,
      Grid.mercy scouts batches chunk border w chunk faces t≤ D*fund t := by
  obtain ⟨k,v⟩ := Param.paid w m q
  let r:= Grid.mercy scouts batches chunk border w chunk faces
  let a i:ℝ:= (k+1:ℕ)*Param.fund i
  have P (i):1≤a i:=one_le_mul_of_one_le_of_one_le (by exact_mod_cast (Nat.zero_lt_succ k)) (allowance i)
  obtain ⟨j,G⟩:= Brief.realConstant r a (v.mono (by
    intro i h
    refine h.trans ?_
    unfold a
    have t:= allowance i
    push_cast
    linarith)) P
  refine ⟨j*(k+1),fun i=>le_trans (G i) (le_of_eq ?_)⟩
  unfold a; push_cast; ring

theorem raise_paid : ∃ D:ℕ,∀ i,
    Grid.mercy scouts batches chunk border Scale.W chunk faces (n i)≤ D*fund (n i) := by
  obtain ⟨D,E⟩:= eligible (w:=Scale.W) 8192
    (Filter.Eventually.of_forall (by intro i; unfold Scale.W Scale.P; omega))
  exact ⟨D,fun i=>E (n i)⟩

end Bureau

end IntegerMultiplication
end Computability
end OAI

import OAI.Computability.IntegerMultiplication.Phase.Plateau
import OAI.Computability.IntegerMultiplication.Phase.Dew

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Shuttle Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Code Packed Loom Dusk
open Finset
variable {J W U : Type} [Fintype J] [DecidableEq J] [Fintype W]
local notation "θ" => Motif.sigma
variable (d : Guild J W U θ) (R : Series W)
noncomputable section
abbrev Data0 (D : ℕ) (W : Type) := QuestP (W:=W) D
abbrev Za (J W : Type) [Fintype J] := Data0 (dim J) W
abbrev day1 (D : ℕ) (W : Type) := Sigma fun k=> Prairie D W (k+1)
def stay {D} : Prairie D W 0→Data0 D W := fun v=>⟨0,v⟩
def rise_t {D} : day1 D W→Data0 D W := fun ⟨n,v⟩=>⟨n+1,v⟩

omit [DecidableEq J] [Fintype W] in
private theorem profile_t {T : Type} {O X : Za J W→Tree} {uses : Za J W→List T}
    {z : Oracle T} {w₀ : Za J W→ℝ}
    (p : Tunnel z (w₀ ∘ stay) (uses ∘ stay) (O ∘ stay) (X ∘ stay))
    (q : Tunnel z (w₀ ∘ rise_t) (uses ∘ rise_t) (O ∘ rise_t) (X ∘ rise_t)) :
    Tunnel z w₀ uses (together (send ∘ green ∘ Sigma.fst) O) X := by
  refine Code.Tunnel.fork (green ∘ Sigma.fst) ?_ ?_
  · let I := {i : Za J W // green i.1=false}
    have e (i : I) : ∃ v : Prairie (dim J) W 0,i.val=stay v := by
      rcases i with ⟨⟨_|n,v⟩,h⟩; exact ⟨v,rfl⟩
      exact False.elim (Bool.noConfusion (show true=false from h))
    choose f g using e
    simpa only [Function.comp_def,← g] using p.slide f
  · let I := {i : Za J W // green i.1=true}
    have e (i:I) : ∃ v : day1 (dim J) W,i.val=rise_t v := by
      rcases i with ⟨⟨_|n,v⟩,h⟩
      · exact False.elim (Bool.noConfusion (show false=true from h))
      exact ⟨⟨_,v⟩,rfl⟩
    choose f g using e
    simpa only [Function.comp_def,← g] using q.slide f

private def include_ {D : ℕ} {T : Type} (t : day1 D W→List T) : Data0 D W→List T
| ⟨0,_⟩ => []
| ⟨n+1,v⟩ => t ⟨n,v⟩

def elbow (x : Za J W) := (((dim J):ℝ)^θ)^x.1
def sizeK {D : ℕ} (x : Data0 D W) : ℝ := (width x.2.plot.tops x.2.plot.foot:ℕ)+ (1:ℝ)
def pullout {D : ℕ} (r : ℕ) (x : Data0 D W) : ℝ :=
  x.2.plot.terrain.count*(timeMark x+((x.2.plot.metres:ℝ)+1)^r*(dim W:ℝ)^x.1)
def tariff (r : ℕ) (x : Za J W) : ℝ := pullout r x * (sizeK x* elbow x)

omit [Fintype W] in
theorem square0 {D : ℕ} (x : Data0 D W) : 1 ≤ sizeK x := by simp [sizeK]; positivity
include d
omit [DecidableEq J] in
theorem large0 (x : Za J W) : 1 ≤ elbow x :=
  one_le_pow₀ (Real.one_le_rpow (by exact_mod_cast d.large.trans' (by decide : 1≤3)) Motif.sigma_range.1.le)
abbrev regime (d : Guild J W U θ) := map_ (W:=W) (dim J) (d.large.trans' (by decide))
abbrev tagN {D : ℕ} (x : Data0 D W) := x.2.plot.terrain.count
abbrev size0 (M) := mass (regime d) tagN timeMark M
omit [DecidableEq J] in
theorem commercial (x : Za J W) (a) :
    size0 d a x ≤ pullout a x := by
  unfold size0 mass pullout
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add_right
    (le_mul_of_one_le_right (by change 0≤ ((x.2.plot.metres:ℝ)+1)^a; positivity)
      (one_le_pow₀ (show (1:ℝ) ≤ dim W by exact_mod_cast d.rank))) _
omit [DecidableEq J] in
theorem tariffM (x : Za J W) (a) : size0 d a x ≤ tariff a x :=
  (commercial d x a).trans (le_mul_of_one_le_right (by unfold pullout; positivity)
    (one_le_mul_of_one_le_of_one_le (square0 x) (large0 d x)))
abbrev up (i:day1 (dim J) W) :=
  ((dim J^i.1*width i.2.plot.tops i.2.plot.foot:ℕ)+ (1:ℝ))^θ

omit [DecidableEq J] in
theorem within (x : day1 (dim J) W) :
    up (J:=J) x ≤ sizeK (rise_t x)*elbow (J:=J) (rise_t x) := by
  let V : ℝ := dim J
  have v : 1 ≤ V := by unfold V; exact_mod_cast d.large.trans' (by decide : 1≤3)
  have a : 1 ≤ V^x.1 := one_le_pow₀ v
  let K := sizeK (rise_t x)
  let P := width x.2.plot.tops x.2.plot.foot
  have g : K=(P:ℝ)+1 := rfl
  have E : ((dim J^x.1*P:ℕ)+ (1:ℝ)) ≤ V^x.1*K := by
    rw [g]
    unfold V
    push_cast; unfold V at a
    linarith
  apply (Real.rpow_le_rpow (by positivity) E Motif.sigma_range.1.le).trans _
  rw [Real.mul_rpow (by positivity) (by rw [g]; positivity),mul_comm]
  have e : K^θ ≤ K := (Real.rpow_le_rpow_of_exponent_le (square0 (rise_t x)) Motif.sigma_range.2.le).trans_eq (Real.rpow_one _)
  apply mul_le_mul e _ (Real.rpow_nonneg (by positivity) _) (by rw [g]; positivity)
  rw [← Real.rpow_natCast_mul (show 0≤V by linarith), mul_comm, Real.rpow_mul_natCast (show 0≤V by linarith)] -- name?
  change ((V:ℝ)^θ)^x.1 ≤ ((V:ℝ)^θ)^(x.1+1)
  gcongr
  · exact Real.one_le_rpow v Motif.sigma_range.1.le
  omega

omit [DecidableEq J] in
theorem tariffH (x : day1 (dim J) W) (a) :
    size0 d a (rise_t x)*up (J:=J) x≤tariff (J:=J) a (rise_t x) := by
  unfold tariff
  apply mul_le_mul (commercial d _ _) (within d _) _ (by unfold pullout; positivity)
  unfold up; positivity

open Circuit
-- unify command family, set exponent from construction BEFORE oracle
private theorem forecast :
    let _G := regime d
    let O := oracle (dim J) R
    ∃ k uses, (∀ x y,y∈uses x → Range x y) ∧ (∀ x,x.1>0 → (uses x).length≤charges d) ∧
      (∀ x,x.1=0 → uses x=[]) ∧
      Tunnel ⟨tariff (J:=J) k,O.issue,O.reply⟩ (tariff (J:=J) k) uses O.issue O.reply := by
  dsimp only
  let O := oracle (dim J) R
  let A := Prairie (dim J) W 0
  let X := day1 (dim J) W
  let Z := regime d
  let s1 := rise_t (W:=W) (D:=dim J)
  let k := fun i:X=>i.1
  obtain ⟨a,n,t,M,N,L⟩ := devote d k (fun i:X=> i.2) (Regime.self (r:=Z.pull s1)) R
  obtain ⟨b,c⟩ := dawn R (id (α:=A)) (Regime.self (r:=Z.pull stay)) rfl
    (J:=J) (d.large.trans' (by decide))
  have F : ∀ i : Za J W, 1≤ tagN i := (climate (J:=J) id (Regime.self (r:=Z)) (by have := d.large; omega)).1
  have g := Rip.header (r:=Z) (l:=timeMark) F (children (D:=dim J) id (Regime.self (r:=Z))).1
  let V (i:Za J W) := goodsP (dim J) R i
  have u i : (cargo (dim J) R i).count*(grain_ (J:=J) (W:=W) id i+1)≤ timeMark i := by
    simp only [cargo,strands,timeMark,users,grain_,id_eq]
    apply Nat.mul_le_mul_left
    omega
  have ν : Alive Z tagN timeMark V :=
    shelter _ (fun i=> cargo (dim J) R i) (grain_ (J:=J) id) _ (climate id (Regime.self (r:=Z)) (by have := d.large; omega)) u
  have q := (g.left ν)
  -- q transforms id with v, want green × header ×V
  have σ : Rip Z tagN timeMark O.issue (send ∘ green ∘ Sigma.fst) :=
    (Rip.split (Rip.alivePair (Drive.started (r:=Z) F) ν)).1.chain g
  obtain ⟨w,T⟩ := σ.twice σ.again
  let k0 := n+b+w
  let y := tariff (J:=J) (W:=W) k0
  let j := Oracle.mk y O.issue O.reply
  let h := include_ t
  refine ⟨k0,h,?_,?_,?_,?_⟩
  · rintro ⟨_|k,x⟩ z
    · simp [h,include_]
    exact M ⟨_,x⟩ z
  · rintro ⟨_|k,x⟩ l
    · contradiction
    exact N ⟨_,x⟩
  · rintro ⟨k,x⟩ y; change k=0 at y; subst k; rfl
  have X0 : Tunnel j (y ∘ stay) (h ∘ stay) (O.issue ∘ stay) (O.reply ∘ stay) :=
    Code.Tunnel.walkway (c.runs.mono (fun i=>
      mass_le (r:=Z) (n:=tagN) (l:=timeMark) (by omega : b≤k0) (stay i) |>.trans (tariffM d _ _)))
  have X1 : Tunnel j (y ∘ rise_t) (h ∘ rise_t) (O.issue ∘ rise_t) (O.reply ∘ rise_t) := by
    -- use L y with budget different
    have e := L y
    apply Loom.Tunnel.monoT e
    intro i
    change size0 d n (s1 i)*_ ≤ y (s1 i)
    rw [show ahead k (fun i:X=> i.2) i=up (J:=J) i by unfold ahead white Spindle.modes up; push_cast; rfl]
    exact (mul_le_mul_of_nonneg_right (mass_le (by omega : n≤k0) _) (by unfold up; positivity)).trans (tariffH d _ k0)
  have u1 : Tunnel j y (fun _=>[]) O.issue (together (send ∘ green ∘ Sigma.fst) O.issue) :=
    Code.Tunnel.walkway (T.runs.mono (fun i=> mass_le (by omega : w≤k0) (r:=Z) i |>.trans (tariffM d _ _)))
  exact u1.join (profile_t X0 X1)
omit [DecidableEq J] d in
private theorem step_r (k : ℕ) {x y : Za J W} (h : Range x y) :
    tariff (J:=J) k y*((dim W:ℝ)*(dim J:ℝ)^θ)= tariff (J:=J) k x := by
  unfold tariff pullout elbow sizeK timeMark users -- tagN not on goal?
  simp only [h.rows,h.common,h.K,← h.close,h.radio,h.sense, pow_succ (dim W),pow_succ (dim W:ℝ),pow_succ ((dim J:ℝ)^θ)]
  push_cast; ring

omit [DecidableEq J] in
private theorem enough (k : ℕ) (uses : Za J W → List (Za J W))
    (z : ∀ x:Za J W, x.1>0 → (uses x).length≤charges d)
    (t : ∀ x:Za J W, x.1=0 → uses x=[])
    (m : ∀ x y,y∈uses x → Range x y) :
    let T := tariff (J:=J) (W:=W) k
    let O := Oracle.mk T (oracle (dim J) R).issue (oracle (dim J) R).reply
    (∀ x,1≤T x) ∧ ∃ a:ℝ,0<a ∧ ∀ x,O.reserve (uses x)+a*T x≤T x := by
  let T := tariff (J:=J) (W:=W) k
  let O := Oracle.mk T (oracle (dim J) R).issue (oracle (dim J) R).reply
  let F : ℝ := dim W
  let K : ℝ := (dim J:ℝ)^θ
  let D := F*K
  let E := max 0 ((charges d:ℝ)/D)
  have f : 0<F := by unfold F; exact_mod_cast d.rank
  have j : 0<K := by apply Real.rpow_pos_of_pos; exact_mod_cast d.large.trans' (by decide : 1≤3)
  have s : 0<D := mul_pos f j
  have e : E<1 := max_lt (by norm_num) ((div_lt_one s).mpr
    (by rw [show D=K*F from mul_comm ..]; exact (div_lt_iff₀ f).1 d.less))
  have u : ∀ x:Za J W,1≤ tagN x := (climate (J:=J) id (Regime.self (r:=regime d)) (by have := d.large; omega)).1
  have d₁ (x) : 1≤T x := (unit_mass (r:=regime d) (l:=timeMark) u _ _).trans (tariffM d x k)
  refine ⟨d₁,1-E,sub_pos.mpr e,fun x=>?_⟩
  change O.reserve (uses x)+(1-E)*T x≤T x
  have d₂ := (le_trans (show (0:ℝ) ≤ 1 by norm_num) (d₁ x))
  suffices a : O.reserve (uses x)≤ E*T x by linarith
  have S (l : List (Za J W)) (h : ∀ y∈l,Range x y) :
      O.reserve l * D = l.length * T x := by
    induction l with
    | nil => simp [Oracle.reserve]
    | cons a l ih =>
      have q := step_r k (h a List.mem_cons_self)
      change T a*D=T x at q
      rw [show O.reserve (a::l) = T a+O.reserve l by simp [O,Oracle.reserve], List.length_cons,add_mul,q,ih (fun _ k => h _ (by simp [k]))]
      push_cast; ring
  cases Nat.eq_zero_or_pos x.1 with
  | inl h =>
    rw [t x h,show O.reserve []=0 from rfl]; exact mul_nonneg (le_max_left ..) d₂
  | inr h =>
    apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) d₂)
    rw [div_mul_eq_mul_div,le_div_iff₀ s, S _ (m x)]
    apply mul_le_mul_of_nonneg_right _ d₂
    exact_mod_cast z x h

/-- exact multitape solver on gaussian Mersenne grid and powers of fixed network
dimension, costing mass * O(axis width)*(dimension^σ)^height.
No FFT layout assumptions used. -/
theorem obtainC :
    ∃ k, Sized (tariff (J:=J) k) (oracle (dim J) R).issue (oracle (dim J) R).reply := by
  obtain ⟨k,uses,v,w,s,t⟩ := forecast d R
  obtain ⟨e,a,z,p⟩ := enough d R k uses w s v
  exact ⟨k,Code.Tunnel.solve _ t e (fun _=>le_rfl) a z p Sigma.fst
    (fun x y m=> (v x y m).close ▸ Nat.lt_succ_self _)⟩

end
end Phase

end IntegerMultiplication
end Computability
end OAI

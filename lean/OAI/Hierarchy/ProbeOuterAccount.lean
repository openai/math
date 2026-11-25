import OAI.Hierarchy.ProbeOuterCharges
import OAI.Hierarchy.ProbeOuterStock

namespace OAI
/-! # The signed account on actual whole-bit inventory -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

variable {I X : Type*} [Fintype I]

/-- The cash projection includes all installed routing costs and credits the
catalyst bits already used. The stock projection counts real outstanding bits. -/
structure OuterBank (I X : Type*) where
  stock : X → I → ℕ
  cash : X → ℝ
  payload : I → ℕ
  box : I → ℝ
  coefficient : I → ℝ
  a : ℝ
  M : ℝ

namespace OuterBank
variable (B : OuterBank I X)

def units (w : ℕ) (x : X) (i : I) : ℝ := (B.stock x i:ℝ)/w

def balance (w : ℕ) (s : ℝ) (x : X) :=
  B.cash x+potential B.a B.M s B.coefficient B.box (B.units w x)

def requests (w m j : ℕ) (x : X) (i : I) :=
  B.stock x i + if j<m then slice m w j * B.payload i else 0

omit [Fintype I] in
theorem requests_inject {w m j : ℕ} (hj : j<m) (x : X) (i : I) :
    (B.requests w m j x i:ℝ)/w = B.units w x i+payloadSlice m w j*(B.payload i:ℝ) := by
  simp [requests,units,payloadSlice,hj,add_div,mul_div_assoc]
  ring

omit [Fintype I] in
theorem requests_cool {w m j : ℕ} (hj : m≤j) (x : X) (i : I) :
    (B.requests w m j x i:ℝ)/w = B.units w x i := by simp [requests,units,not_lt.mpr hj]

/-- Physical capped routing on a mesh increment: the excess integers are
sent on their core routes, and all other outstanding integer bits remain. -/
structure Caps (m w cap : ℕ) (move : ℕ → X → X) : Prop where
  stored : ∀ j<m+m, ∀ x i, B.stock (move j x) i = min (B.requests w m j x i) (cap*w)
  charged : ∀ j<m+m, ∀ x, B.cash (move j x) ≤ B.cash x+
    pairing (fun i=> ((B.requests w m j x i-B.stock (move j x) i:ℕ):ℝ)/w) B.box

theorem cap_payment {m w cap j : ℕ} {s : ℝ} (move : ℕ→X→X) (events : B.Caps m w cap move)
    (hj : j<m+m) (x : X) (hw : 0<w) (hs : 0<s) (ha : 0<B.a) (hb : ∀ i,0≤B.coefficient i)
    (hM : 0≤B.M) (sat : ∀ i,s*rowSlope B.a (B.coefficient i) B.M (B.box i)≤cap) :
    B.balance w s (move j x) ≤ B.cash x+
      potential B.a B.M s B.coefficient B.box (fun i=>(B.requests w m j x i:ℝ)/w) := by
  let bits := B.requests w m j x
  have stored : B.stock (move j x) = clipBits cap w bits :=
    funext (events.stored j hj x)
  have charged : B.cash (move j x) ≤ B.cash x+pairing (bitStock w (spillBits cap w bits)) B.box := by
    change B.cash (move j x) ≤ B.cash x+pairing
      (fun i=>((bits i-clipBits cap w bits i:ℕ):ℝ)/w) B.box
    simpa only [stored] using events.charged j hj x
  change B.cash (move j x)+potential B.a B.M s B.coefficient B.box (bitStock w (B.stock (move j x))) ≤
    B.cash x+potential B.a B.M s B.coefficient B.box (bitStock w bits)
  rw [stored,outer_stock_cap cap B.coefficient B.box bits hw ha hb hM hs sat]
  exact add_le_add charged le_rfl

/-- The ordinary low-excess or crude step bound after all actual cap payments. -/
theorem inject_move {n m w j cap : ℕ} {C L : ℝ} (hm : 0<m) (hw : m≤w) (hj : j<m)
    (move : ℕ→X→X) (events : B.Caps m w cap move) (x : X) (ha : 0<B.a)
    (hb : ∀ i,0≤B.coefficient i) (hM : 0≤B.M) (hA : ∀ i,0≤B.box i)
    (sat : ∀ i,(1:ℝ)*rowSlope B.a (B.coefficient i) B.M (B.box i)≤cap)
    (hC : 0≤C) (large : C≤B.a*m) (sumSq : (∑ i,(B.payload i:ℝ)^2)≤C*n)
    (offer : pairing (fun i=>(B.payload i:ℝ)) (maximizer B.a B.M 1 B.coefficient B.box (B.units w x))≤L*n) :
    B.balance w 1 (move j x) ≤ B.balance w 1 x+payloadSlice m w j*(L+1/2)*n := by
  have first := B.cap_payment move events (j:=j) (by omega) x (hm.trans_le hw) (by norm_num : (0:ℝ)<1) ha hb hM sat
  simp only [B.requests_inject hj] at first
  have second := inject_scaled hm hw j B.coefficient B.box (B.units w x) (fun i=>(B.payload i:ℝ)) ha hb hM
    (fun i=>by unfold units; positivity) hA (fun _=>by positivity) hC large sumSq offer
  unfold balance at first ⊢
  linarith

theorem cool_move {n m w j cap : ℕ} {s₀ G L : ℝ} (hm : 0<m) (hw : 0<w) (hj : j<m)
    (move : ℕ→X→X) (events : B.Caps m w cap move) (x : X) (ha : 0<B.a)
    (hb : ∀ i,0≤B.coefficient i) (hM : 0≤B.M) (hA : ∀ i,0≤B.box i)
    (hs : 0<s₀) (hs₁ : s₀≤1)
    (sat : ∀ i,clockTime s₀ m (j+1)*rowSlope B.a (B.coefficient i) B.M (B.box i)≤cap)
    (hG : 0≤G) (large : G≤s₀*B.a*m)
    (sumSq : (∑ i,(rowSlope B.a (B.coefficient i) B.M
      (maximizer B.a B.M (clockTime s₀ m j) B.coefficient B.box (B.units w x) i))^2)≤G*n)
    (offer : score B.a B.M B.coefficient
      (maximizer B.a B.M (clockTime s₀ m j) B.coefficient B.box (B.units w x))≤L*n) :
    B.balance w (clockTime s₀ m (j+1)) (move (m+j) x) ≤
      B.balance w (clockTime s₀ m j) x+(1-s₀)/(m:ℝ)*(L+1/2)*n := by
  have endLe := (clock_bounds hs hs₁ hm (j+1) (by omega)).1
  have first := B.cap_payment move events (j:=m+j) (by omega) x hw (hs.trans_le endLe) ha hb hM sat
  simp only [B.requests_cool (show m≤m+j by omega)] at first
  have second := cool_scaled hm j hj B.coefficient B.box (B.units w x) ha hb hM
    (fun i=>by unfold units; positivity) hA hs hs₁ hG large sumSq offer
  unfold balance at first ⊢
  linarith

end OuterBank
end
end Hierarchy.AdaptiveProbe

end OAI

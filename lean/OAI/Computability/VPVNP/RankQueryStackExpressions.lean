import OAI.Computability.VPVNP.RankQueryStackRegister

/-!
# Compiling the arithmetic expressions of a Schur query

Each syntax node receives one fixed scratch register. Disjoint intervals
serve the two subexpressions. The proofs track the result register and show
that registers outside the assigned interval retain their values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Dispatch

open BurstRAM PrivateRAM

namespace Expr

variable {r w : ℕ}

/-- Number of nodes in an expression tree, used to allocate disjoint scratch slots for its
subexpressions. -/
def nodes : Expr → ℕ
  | .reg _ | .lit _ => 1
  | .op _ l r => 1 + l.nodes + r.nodes

theorem nodes_pos (e : Expr) : 0 < e.nodes := by cases e <;> simp [nodes]

/-- All intermediate natural-number results fit the register width. -/
def Fits (w : ℕ) (env : Fin 8 → ℕ) (e : Expr) : Prop :=
  e.eval env < 2^w ∧ match e with
    | .reg _ | .lit _ => True
    | .op _ l r => l.Fits w env ∧ r.Fits w env

/-- Compile an expression into register code that writes its value to the scratch slot at
`start`. -/
def compile (arg : Fin 8 → Fin r) (slot : ℕ → Fin r) (start : ℕ) : Expr → RegCode r
  | .reg i => .copy (slot start) (arg i)
  | .lit n => .lit (slot start) n
  | .op a l r => .seq (l.compile arg slot (start+1)) <|
    .seq (r.compile arg slot (start+1+l.nodes)) <|
      .op (slot start) a (slot (start+1)) (slot (start+1+l.nodes))

/-- The compilation never writes outside the finite register interval
assigned to this expression. -/
theorem preserves (e : Expr) (arg : Fin 8 → Fin r) (slot : ℕ → Fin r) (start : ℕ)
    (rs : Regs r w) (j : Fin r)
    (h : ∀ i, start ≤ i → i < start+e.nodes → slot i ≠ j) :
    (e.compile arg slot start).exec rs j = rs j := by
  induction e generalizing start rs with
  | reg i =>
    simp [compile, RegCode.exec, Function.update_of_ne (h start le_rfl (by simp [nodes])).symm]
  | lit n =>
    simp [compile, RegCode.exec, Function.update_of_ne (h start le_rfl (by simp [nodes])).symm]
  | op a l r ihl ihr =>
    have hroot := h start le_rfl (by simp [nodes])
    simp only [compile, RegCode.exec, Function.update_of_ne hroot.symm]
    rw [ihr, ihl] <;> intro i hi hfin <;> apply h i <;> (try simp only [nodes]) <;> omega

/-- Interpreting a compiled expression reads the eight input words and
writes exactly its natural value to the first scratch register. -/
theorem compile_correct (e : Expr) (env : Fin 8 → ℕ) (arg : Fin 8 → Fin r)
    (slot : ℕ → Fin r) (cap start : ℕ) (rs : Regs r w) (hfit : e.Fits w env)
    (hr : ∀ i, (rs (arg i)).val = env i) (hcap : start + e.nodes ≤ cap)
    (hinj : ∀ i < cap, ∀ j < cap, slot i = slot j → i = j)
    (hsep : ∀ i < cap, ∀ j, slot i ≠ arg j) :
    ((e.compile arg slot start).exec rs (slot start)).val = e.eval env := by
  induction e generalizing start rs with
  | reg i => simpa [compile, RegCode.exec, eval] using hr i
  | lit n =>
    simp only [compile, RegCode.exec, Function.update_self, eval]
    change (Fin.ofNat (2^w) n).val = n
    exact Nat.mod_eq_of_lt hfit.1
  | op a l r ihl ihr =>
    let left := start+1
    let right := start+1+l.nodes
    let rsL := (l.compile arg slot left).exec rs
    let rsR := (r.compile arg slot right).exec rsL
    simp only [compile, RegCode.exec, Function.update_self]
    change ((a.word (rsR (slot left)) (rsR (slot right))).val) = _
    have hc : start + (1+l.nodes+r.nodes) ≤ cap := hcap
    have hcL : left+l.nodes ≤ cap := by dsimp [left]; omega
    have hcR : right+r.nodes ≤ cap := by dsimp [right]; omega
    have hsafe : l.Fits w env ∧ r.Fits w env := hfit.2
    have hL := ihl left rs hsafe.1 hr hcL
    have hinput (i : Fin 8) : (rsL (arg i)).val = env i := by
      change ((l.compile arg slot left).exec rs (arg i)).val = _
      rw [preserves l arg slot left rs (arg i) (fun j _ hj => hsep j (by omega) i)]
      exact hr i
    have hR := ihr right rsL hsafe.2 hinput hcR
    have hkeep : rsR (slot left) = rsL (slot left) := by
      apply preserves
      intro j hj hk he
      have heq := hinj j (by omega) left (by have := l.nodes_pos; omega) he
      dsimp [left, right] at hj heq
      have := l.nodes_pos
      omega
    have vL : (rsR (slot left)).val = l.eval env := hkeep ▸ hL
    have vR : (rsR (slot right)).val = r.eval env := hR
    rw [a.word_val _ _ (by simpa only [vL, vR, eval] using hfit.1), vL, vR]
    rfl

/-- A syntax-dependent coefficient in the linear word-width bound. -/
def weight : Expr → ℕ
  | .reg _ => 1
  | .lit n => n+1
  | .op _ l r => l.weight+r.weight+1

theorem fits_mono {env : Fin 8 → ℕ} (e : Expr) {u v : ℕ} (h : e.Fits u env) (hu : u ≤ v) :
    e.Fits v env := by
  induction e with
  | reg | lit => exact ⟨h.1.trans_le (Nat.pow_le_pow_right (by decide) hu), trivial⟩
  | op a l r ihl ihr => exact ⟨h.1.trans_le (Nat.pow_le_pow_right (by decide) hu), ihl h.2.1, ihr h.2.2⟩

/-- A width linear in the input bit bound suffices for any fixed expression. -/
theorem fits_weight (e : Expr) (p : ℕ) (env : Fin 8 → ℕ) (he : ∀ i, env i < 2^p) :
    e.Fits ((p+1)*e.weight) env := by
  induction e with
  | reg i =>
    exact ⟨(he i).trans_le (Nat.pow_le_pow_right (by decide) (by simp [weight])), trivial⟩
  | lit n =>
    have hn : n < 2^n := Nat.lt_two_pow_self
    exact ⟨hn.trans_le (Nat.pow_le_pow_right (by decide) (by simp [weight, Nat.add_mul]; omega)), trivial⟩
  | op a l r ihl ihr =>
    let L := (p+1)*l.weight
    let R := (p+1)*r.weight
    let W := (p+1)*(op a l r).weight
    have hw : W = L + R + (p+1) := by simp [W,L,R,weight,Nat.mul_add]
    have hl : l.eval env < 2^L := by cases l <;> exact ihl.1
    have hr : r.eval env < 2^R := by cases r <;> exact ihr.1
    have hL : 1 ≤ 2^L := Nat.one_le_pow _ _ (by decide)
    have hR : 1 ≤ 2^R := Nat.one_le_pow _ _ (by decide)
    have hbig : 2^L*2^R*2 ≤ 2^W := by
      rw [hw, pow_add, pow_add]
      apply Nat.mul_le_mul_left
      exact (Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ p+1 by omega))
    have hlr := Nat.mul_le_mul_left (2^L) hR
    have hrl := Nat.mul_le_mul_right (2^R) hL
    refine ⟨?_, fits_mono l ihl (by change L ≤ W; omega), fits_mono r ihr (by change R ≤ W; omega)⟩
    change a.eval (l.eval env) (r.eval env) < 2^W
    have hlW : 2^L ≤ 2^W := Nat.pow_le_pow_right (by decide) (by omega)
    cases a with
    | add => change l.eval env + r.eval env < 2^W; simp only [Nat.mul_one, Nat.one_mul] at hlr hrl; omega
    | sub => exact (Nat.sub_le ..).trans_lt (hl.trans_le hlW)
    | mul =>
      have hm := Nat.mul_le_mul hl.le hr.le
      have hp := Nat.mul_pos (Nat.zero_lt_of_lt hl) (Nat.zero_lt_of_lt hr)
      change l.eval env * r.eval env < 2^W
      omega
    | div => exact (Nat.div_le_self ..).trans_lt (hl.trans_le hlW)
    | mod => exact (Nat.mod_le ..).trans_lt (hl.trans_le hlW)

end Expr

end RankQuery.Stack.Dispatch

end VPVNP
end Computability
end OAI

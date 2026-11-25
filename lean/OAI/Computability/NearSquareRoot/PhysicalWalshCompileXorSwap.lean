import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorRoute
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSwapRouter

/-! # Compiling a whole-slot swap from its low and high fields -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileXorSwap

open IntegerMultiplication Code PhysicalWalshNode PhysicalWalshCompileXorRoute
open KernelPass.ComputableSyntax (Raw)
open CommonRegisters GeneratorSyntax

abbrev Params := Raw × ℕ × ℕ

def reverseKey (k : Params) : Params := (k.1,k.2.2,k.2.1)

private theorem computable_reverseKey : Computable reverseKey :=
  Computable.fst.pair ((Computable.snd.comp Computable.snd).pair (Computable.fst.comp Computable.snd))

/-- For decreasing axes the low field takes three directed XORs, followed by
one packed rectangle interchange for the high field. -/
def ordered (K : Kit) (low high : Params → Cmd) (k : Params) : Cmd :=
  K.chain (K.chain (K.chain (low k) (low (reverseKey k))) (low k)) (high k)

/-- Canonicalize the axis order in the compiler, including a one-scan diagonal. -/
def command (K : Kit) (low high : Params → Cmd) (k : Params) : Cmd :=
  if k.2.2 < k.2.1 then ordered K low high k
  else if k.2.1 < k.2.2 then ordered K low high (reverseKey k)
  else K.erase

theorem effective_command (K : Kit) {low high : Params → Cmd} (hl : Effective ltr low)
    (hh : Effective ltr high) : Effective ltr (command K low high) := by
  have base : Effective ltr (ordered K low high) :=
    K.effective_chain (K.effective_chain (K.effective_chain hl (hl.comp computable_reverseKey)) hl) hh
  have hi : Primrec (fun k : Params => k.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun k : Params => k.2.2) := Primrec.snd.comp Primrec.snd
  apply (Computable.cond (Primrec.nat_lt.comp hj hi).decide.to_comp base
    (Computable.cond (Primrec.nat_lt.comp hi hj).decide.to_comp (base.comp computable_reverseKey)
      (effective_const ltr K.erase))).of_eq
  intro k
  by_cases h : k.2.2 < k.2.1 <;> by_cases h' : k.2.1 < k.2.2 <;>
    simp [command,h,h']

theorem within_command {K : Kit} {R M : ℕ} (hk : Legal K R) (le : R ≤ M) {low high : Params → Cmd}
    (hl : ∀ k, Within M (low k)) (hh : ∀ k, Within M (high k)) (k : Params) :
    Within M (command K low high k) := by
  have bounded (j : Params) : Within M (ordered K low high j) :=
    hk.within_chain le (hk.within_chain le (hk.within_chain le (hl _) (hl _)) (hl _)) (hh _)
  unfold command
  split_ifs <;> first | apply bounded | exact hk.within_erase le

/-- This is the row action of an elementary XOR on the specified low slots. -/
def slice {a : ℕ} (cut : Shape → ℕ) (src dst : Fin (a+1)) (s : Shape) (x : Data s) : Data s :=
  x ∘ ElementarySweep.address src dst s (cut s)

private theorem three {a : ℕ} (cut : Shape → ℕ) (cap : ∀ s, cut s ≤ grow (a+1) (s.level-1))
    (i j : Fin (a+1)) (ji : j < i) (s : Shape) (x : Data s) :
    slice cut i j s (slice cut j i s (slice cut i j s x)) = Route.lowerSwap cut i j s x := by
  funext n
  let L := grow (a+1) (s.level-1)
  let lo := XorBits.offset L i
  let hi := XorBits.offset L j
  change x (SwapWord.stride s (XorBits.window lo hi (cut s)) (SwapWord.stride s (XorBits.window hi lo (cut s))
    (SwapWord.stride s (XorBits.window lo hi (cut s)) n))) = _
  rw [SwapWord.stride_comp,SwapWord.stride_comp]
  apply congrArg x
  exact congrArg (fun f => SwapWord.stride s f n) (funext fun q =>
    SwapWord.three_xor lo hi _ q ((Nat.add_le_add_left (cap s) lo).trans (Route.apart_of_gt ji L)))

/-- The same emitted command acts correctly on every admitted node, and all
four passes use a common resident arena. -/
theorem runs_command {K : Kit} {R a W : ℕ} (hk : Legal K R) {low high : Params → Cmd} (raw : Raw)
    (cut scan arena : Shape → ℕ) (cap : ∀ s, cut s ≤ grow (a+1) (s.level-1))
    (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ arena s)
    (hl : ∀ i j : Fin (a+1), i ≠ j →
      Flat (a:=a) (W:=W) scan arena (slice cut i j) (low (raw,i.val,j.val)))
    (hh : ∀ i j : Fin (a+1), j < i →
      Flat (a:=a) (W:=W) scan arena (Route.upperSwap cut i j) (high (raw,i.val,j.val)))
    (i j : Fin (a+1)) :
    Flat (a:=a) (W:=W) scan arena (Route.axisSwap i j) (command K low high (raw,i.val,j.val)) := by
  have decreasing (u v : Fin (a+1)) (lt : v < u) :
      Flat (a:=a) (W:=W) scan arena (Route.axisSwap u v) (ordered K low high (raw,u.val,v.val)) := by
    have h₁ := hl u v (ne_of_gt lt)
    have h₂ := hl v u (ne_of_lt lt)
    have chain := hk.runs_chain cost fit (hk.runs_chain cost fit (hk.runs_chain cost fit h₁ h₂) h₁) (hh u v lt)
    simpa only [ordered,reverseKey,three cut cap u v lt,Route.lower_upper cut cap u v lt] using chain
  rcases lt_trichotomy j i with ji|eq|ij
  · rw [command,ite_eq_left (show j.val < i.val from ji)]
    exact decreasing i j ji
  · subst j
    simp only [command,lt_irrefl,ite_false]
    simpa only [Flat,Route.axisSwap_self] using hk.runs_id cost fit
  · rw [command,ite_eq_right (show ¬j.val < i.val from not_lt_of_gt ij),ite_eq_left (show i.val < j.val from ij)]
    have h : Route.axisSwap j i = Route.axisSwap i j := by unfold Route.axisSwap; rw [Equiv.swap_comm j i]
    rw [← h]
    exact decreasing j i ij

/-- A uniform source and absolute register bound for the complete slot swap. -/
theorem compile (low high : Params → Cmd) (hl : Effective ltr low) (hh : Effective ltr high)
    (B : ℕ) (rl : ∀ k, Within B (low k)) (rh : ∀ k, Within B (high k)) :
    ∃ (swap : Params → Cmd) (M : ℕ), Effective ltr swap ∧ (∀ k, Within M (swap k)) ∧
      ∀ (a W : ℕ) (raw : Raw) (cut scan arena : Shape → ℕ), (∀ s, cut s ≤ grow (a+1) (s.level-1)) →
        (∀ s, arena s ≤ scan s) →
        (∀ s, PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ arena s) →
        (∀ i j : Fin (a+1), i ≠ j → Flat (a:=a) (W:=W) scan arena (slice cut i j) (low (raw,i.val,j.val))) →
        (∀ i j : Fin (a+1), j < i → Flat (a:=a) (W:=W) scan arena (Route.upperSwap cut i j) (high (raw,i.val,j.val))) →
        ∀ i j : Fin (a+1), Flat (a:=a) (W:=W) scan arena (Route.axisSwap i j) (swap (raw,i.val,j.val)) := by
  obtain ⟨K,R,hk⟩ := exists_kit
  refine ⟨command K low high,max R B,effective_command K hl hh,
    within_command hk (le_max_left ..) (fun k => RegisterSelect.within_mono (le_max_right ..) _ (rl k))
      (fun k => RegisterSelect.within_mono (le_max_right ..) _ (rh k)),?_⟩
  intro a W raw cut scan arena cap cost fit prefixRuns rect
  exact runs_command hk raw cut scan arena cap cost fit prefixRuns rect

end PhysicalWalshCompileXorSwap

end NearSquareRoot
end Computability
end OAI

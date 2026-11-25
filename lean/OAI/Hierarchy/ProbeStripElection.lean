import OAI.Hierarchy.ProbeStripFormat

namespace OAI
/-! # Election and alphabet at a real strip before its private histogram is read -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe PurchaseStage
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing Classical BigOperators

variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N q goods digits w : ℕ}

private theorem key_equal (radix : ℕ) (xs : List Expr) (m n : Memory w) (r : Word w)
    (h : ∀x∈xs,x.eval m r=x.eval n r) :
    (menuKey radix xs).eval m r=(menuKey radix xs).eval n r := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [menuKey,Expr.eval,eval_scale,h x (List.mem_cons_self ..),ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))]

private theorem choose_equal (k off : ℕ) (f : Fin k→ℕ) (key : Expr) (m n : Memory w) (r : Word w)
    (same : key.eval m r=key.eval n r) :
    (chooseField k off (fun i=>.lit (f i)) key).eval m r =
    (chooseField k off (fun i=>.lit (f i)) key).eval n r := by
  induction k generalizing off with
  | zero=>rfl
  | succ k ih=>
    simp only [chooseField,Expr.eval,same,ih (off+1) (fun i=>f i.succ)]; rfl

private theorem mul_equal (k copies : ℕ) (x : Expr) (m n : Memory w) (r : Word w)
    (same : x.eval m r=x.eval n r) :
    (boundedMul k (.lit copies) x).eval m r=(boundedMul k (.lit copies) x).eval n r := by
  induction k with
  | zero=>rfl
  | succ k ih=>simp only [boundedMul,Expr.eval,eval_scale,same,ih]

/-- All equalities concern actual public and prior-state reads. The two
current (and all future) private histogram tapes can be arbitrary. -/
theorem election (menu : Probe.FixedMenu F edge req box ε tree N) (test : StripTest digits)
    (terms recommendations enabled selectors stocks : Bank) (copies maxWidth : ℕ)
    (ports : Fin goods→E) (slot : Fin goods→Option Expr) (m n : Memory w) (r : Word w)
    (mask : enabled.read m r=enabled.read n r)
    (quote : ∀i,(test.quoted i).eval m r=(test.quoted i).eval n r)
    (page : let key:=menuKey test.radix (List.ofFn test.quoted)
      recommendations.read m (key.eval m r)=recommendations.read n (key.eval m r))
    (arity : let key:=menuLookup recommendations test.radix (List.ofFn test.quoted)
      terms.read m (key.eval m r)=terms.read n (key.eval m r))
    (prior : ∀i a,slot i=some a→stocks.read m (a.eval m r)=stocks.read n (a.eval n r)) :
    let b:=batch (q:=q) menu test terms recommendations enabled selectors stocks .row copies maxWidth ports slot
    b.packet.eval m r=b.packet.eval n r ∧
      b.termCount.read m (b.packet.eval m r)=b.termCount.read n (b.packet.eval n r) ∧
      (b.selected m r ↔ b.selected n r) := by
  let b:=batch (q:=q) menu test terms recommendations enabled selectors stocks .row copies maxWidth ports slot
  let key:=menuKey test.radix (List.ofFn test.quoted)
  have sameKey : key.eval m r=key.eval n r := by
    apply key_equal
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    exact quote i
  have packet : b.packet.eval m r=b.packet.eval n r := by
    change recommendations.read m (key.eval m r)=recommendations.read n (key.eval n r)
    exact page.trans (congrArg (recommendations.read n) sameKey)
  have cardinal : b.termCount.read m (b.packet.eval m r)=b.termCount.read n (b.packet.eval n r) :=
    arity.trans (congrArg (terms.read n) packet)
  have demands (i : Fin goods) : (b.need i).eval m r=(b.need i).eval n r := by
    apply mul_equal
    exact choose_equal _ 1 _ _ m n r packet
  have funds (i : Fin goods) : (b.stock i).eval m r=(b.stock i).eval n r := by
    change (inventory stocks (b.need i) (slot i)).eval m r=
      (inventory stocks (b.need i) (slot i)).eval n r
    cases hin : slot i with
    | none=>exact demands i
    | some a=>exact prior i a hin
  refine ⟨packet,cardinal,?_⟩
  change (enabled.read m r≠0 ∧ b.packet.eval m r≠0 ∧ ∀i,((b.need i).eval m r).val≤((b.stock i).eval m r).val) ↔
    (enabled.read n r≠0 ∧ b.packet.eval n r≠0 ∧ ∀i,((b.need i).eval n r).val≤((b.stock i).eval n r).val)
  simp only [mask,packet,demands,funds]

end Hierarchy.ProtocolRAM.StripDirectory

end
end OAI

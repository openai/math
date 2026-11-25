import OAI.Computability.NearSquareRoot.PhysicalWalshOpen
import OAI.Computability.NearSquareRoot.PhysicalWalshBank
import OAI.Computability.NearSquareRoot.KernelPass

/-! # A space-aware compiler for the normalized stream grammar

The row type may carry width invariants. On the tape a bank is a shared header
followed by a list of complete serialized rows in order. Parallel composition
splits at a fixed row boundary, parks the sibling while executing each branch,
and joins both results. All of these operations are implemented P192 commands.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication Code Space KernelPass

/-- The mathematical row may depend on widths stored in the common header. -/
structure Layout (U H R : Type) where
  Row : U → Type
  header : U → H
  store : ∀ u, Row u → R

variable {U H R : Type} {A i j o : ℕ}

abbrev Rows (l : Layout U H R) (u : U) (n : ℕ) := Fin n → l.Row u

def packet (l : Layout U H R) {n : ℕ} (u : U) (x : Rows l u n) : H × List R :=
  (l.header u, List.ofFn fun i => l.store u (x i))

/-- The four primitive instructions operate on width-checked mathematical rows. -/
structure Ops (A : ℕ) (l : Layout U H R) where
  mix : ∀ {i o}, (Fin o → Fin i → Coefficient) → ∀ u, Rows l u i → Rows l u o
  xor : Fin A × Fin A → ∀ u, l.Row u → l.Row u
  scale : ∀ q, (Column A → Fin q → ZMod 2) → ((Fin q → ZMod 2) → Coefficient) → ∀ u, l.Row u → l.Row u
  child : Fin A → ∀ u, l.Row u → l.Row u

/-- The rounded implementation of a plan, with the same evaluation order as the physical code. -/
def Ops.applyPlan {l : Layout U H R} (f : Ops A l) : ∀ {i o}, Plan A i o → ∀ u, Rows l u i → Rows l u o
  | _, _, .mix c, u, x => f.mix c u x
  | _, _, .xor g, u, x => fun _ => f.xor g u (x 0)
  | _, _, .scale q t c, u, x => fun _ => f.scale q t c u (x 0)
  | _, _, .child a, u, x => fun _ => f.child a u (x 0)
  | _, _, .seq p q, u, x => f.applyPlan p u (f.applyPlan q u x)
  | _, _, @Plan.parallel _ i j _ _ p q, u, x =>
    Fin.append (f.applyPlan p u fun a => x (a.castAdd j)) (f.applyPlan q u fun b => x (b.natAdd i))

variable [Codec H] [Codec R] {l : Layout U H R} {m : Meter U}

/-- One uniform stream command on all bank widths/data in the specified layout. -/
def Executes (n : ℕ) (g : ∀ u, Rows l u i → Rows l u o) : Prop :=
  OpenRun m n (Sigma.fst (α := U) (β := fun u => Rows l u i))
    (fun x => send (packet l x.1 x.2)) (fun x => send (packet l x.1 (g x.1 x.2)))

private theorem Executes.atInputs {X : Type*} {g : ∀ u, Rows l u i → Rows l u o} {n : ℕ}
    (h : Executes (m := m) n g) (u : X → U) (x : ∀ t, Rows l (u t) i) :
    OpenRun m n u (fun t => send (packet l (u t) (x t))) (fun t => send (packet l (u t) (g (u t) (x t)))) :=
  h.on fun t => ⟨u t, x t⟩

/-- Every complete row and the common header fit in the node's reserved storage. -/
structure FitsLayout (m : Meter U) (l : Layout U H R) : Prop where
  header : ∀ u, size (l.header u) ≤ m.arena u
  row : ∀ u r, size (l.store u r) ≤ m.arena u

theorem FitsLayout.packet (h : FitsLayout m l) {n : ℕ} (u : U) (x : Rows l u n) :
    size (packet l u x) ≤ (n+3)*(m.arena u+1) := by
  have hr := PhysicalWalshBank.size_rows_le (fun i => l.store u (x i)) (m.arena u) fun i => h.row u _
  have hh := h.header u
  simp only [PhysicalWalsh.packet, size_prod, Nat.add_mul]
  omega

theorem FitsLayout.both (h : FitsLayout m l) {n' : ℕ} (u : U) (x : Rows l u i) (y : Rows l u n') :
    size (PhysicalWalsh.packet l u x, PhysicalWalsh.packet l u y) ≤ (i+3+(n'+3)+1)*(m.arena u+1) := by
  have hx := h.packet u x
  have hy := h.packet u y
  rw [size_prod,Nat.add_mul,Nat.add_mul]; dsimp only; omega

omit [Codec H] [Codec R] in
private theorem store_append {i j : ℕ} {u : U} (x : Rows l u i) (y : Rows l u j) :
    (fun a => l.store u (Fin.append x y a)) = Fin.append (fun a => l.store u (x a)) (fun a => l.store u (y a)) := by
  funext a; exact Fin.addCases (fun _ => by simp) (fun _ => by simp) a

omit [Codec H] [Codec R] in
theorem split_packet {i j : ℕ} {u : U} (x : Rows l u (i+j)) :
    PhysicalWalshBank.split i (packet l u x) =
      (packet l u (fun a => x (a.castAdd j)), packet l u (fun b => x (b.natAdd i))) := by
  unfold packet
  let z (t : Fin (i+j)) := l.store u (x t)
  have e := PhysicalWalshBank.split_rows (l.header u) (fun a => z (a.castAdd j)) (fun b => z (b.natAdd i))
  rw [Fin.append_castAdd_natAdd (f := z)] at e
  exact e

omit [Codec H] [Codec R] in
theorem combine_packet {n' : ℕ} {u : U} (x : Rows l u i) (y : Rows l u n') :
    PhysicalWalshBank.combine (packet l u x, packet l u y) = packet l u (Fin.append x y) := by
  simp only [PhysicalWalshBank.combine, packet, store_append, List.ofFn_fin_append]

/-- Serial execution retains the exact sum of child counts. -/
theorem Executes.seq {c d : ℕ} {f : ∀ u, Rows l u i → Rows l u j} {g : ∀ u, Rows l u j → Rows l u o}
    (hf : Executes (m := m) c f) (hg : Executes (m := m) d g) :
    Executes (m := m) (c+d) (fun u x => g u (f u x)) :=
  OpenRun.seq hf (hg.atInputs (Sigma.fst (β := fun u => Rows l u i)) fun t => f t.1 t.2)

/-- Framing a parallel call on the particular states that reach this instruction. -/
theorem parallelAt {X : Type} {i j o b c d : ℕ} (hl : FitsLayout m l)
    (u : X → U) (x : ∀ t, Rows l (u t) (i+j)) (e : ∀ t, Rows l (u t) o) (v : ∀ t, Rows l (u t) b)
    (hf : OpenRun m c u (fun t => send (packet l (u t) (fun a => x t (a.castAdd j))))
      (fun t => send (packet l (u t) (e t))))
    (hg : OpenRun m d u (fun t => send (packet l (u t) (fun a => x t (a.natAdd i))))
      (fun t => send (packet l (u t) (v t)))) :
    OpenRun m (c+d) u (fun t => send (packet l (u t) (x t)))
      (fun t => send (packet l (u t) (Fin.append (e t) (v t)))) := by
  let b' (t : X) : Rows l (u t) j := fun a => x t (a.natAdd i)
  have split := OpenRun.easy (m := m) (u := u) _ (PhysicalWalshBank.easy_split i)
    (fun t : X => packet l (u t) (x t)) _ (fun x => hl.packet (u x) _)
  simp only [split_packet, send_prod] at split
  have left := hf.left (fun x => send (packet l (u x) (b' x))) _ (fun x => hl.packet _ _)
  have swap := OpenRun.easy (m := m) (u := u) _ Easy.exchange
    (fun x => (packet l (u x) (e x), packet l (u x) (b' x))) _ (fun x => hl.both _ _ _)
  have right := hg.left (fun x => send (packet l (u x) (e x))) _ (fun x => hl.packet _ _)
  have finish := OpenRun.easy (m := m) (u := u) _ (Easy.exchange.compose PhysicalWalshBank.easy_combine)
    (fun x => (packet l (u x) (v x), packet l (u x) (e x))) _ (fun x => hl.both _ _ _)
  simp only [Prod.swap_prod_mk, combine_packet, send_prod] at swap finish
  simpa only [send_prod, Nat.zero_add, Nat.add_zero] using (((split.seq left).seq swap).seq (right.seq finish))

/-- Both branches execute sequentially on shared registers and keep the same header. -/
theorem Executes.parallel {i j o b c d : ℕ} {f : ∀ u, Rows l u i → Rows l u o}
    {g : ∀ u, Rows l u j → Rows l u b} (hl : FitsLayout m l)
    (hf : Executes (m := m) c f) (hg : Executes (m := m) d g) :
    Executes (m := m) (c+d) (fun u x => Fin.append (f u fun a => x (a.castAdd j)) (g u fun a => x (a.natAdd i))) := by
  let u := Sigma.fst (β := fun u => Rows l u (i+j))
  exact parallelAt hl u Sigma.snd _ _
    (hf.atInputs u fun x a => x.2 (a.castAdd j)) (hg.atInputs u fun x a => x.2 (a.natAdd i))

/-- Independent primitive proofs. A child instruction has one recursive charge. -/
structure Leaves (m : Meter U) (f : Ops A l) : Prop where
  mix : ∀ {i o} (c : Fin o → Fin i → Coefficient), Executes (m := m) 0 (f.applyPlan (.mix c))
  xor : ∀ g, Executes (m := m) 0 (f.applyPlan (.xor g))
  scale : ∀ q t c, Executes (m := m) 0 (f.applyPlan (.scale q t c))
  child : ∀ a, Executes (m := m) 1 (f.applyPlan (.child a))

/-- Compile any finite normalized template. Its syntax determines exactly the
coefficient of the child call time in the recurrence, independent of depth. -/
theorem compilePlan (f : Ops A l) (shape : FitsLayout m l) (leaf : Leaves m f) (p : Plan A i o) :
    Executes (m := m) p.calls (f.applyPlan p) := by
  induction p with
  | mix c => exact leaf.mix c
  | xor g => exact leaf.xor g
  | scale q t c => exact leaf.scale q t c
  | child a => exact leaf.child a
  | seq p q hp hq => simpa only [Plan.calls, Ops.applyPlan, Nat.add_comm p.calls q.calls] using hq.seq hp
  | parallel p q hp hq => exact hp.parallel shape hq

end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI

import OAI.ThreeFlat.Routing.SpillLinks
import Mathlib.Tactic.Ring

namespace OAI
/-! # Wiring the endpoint banks of every candidate batch

A bank is indexed by a public batch and one of its two sides. The public
read address can be shared across several candidate batches. At each bank
the candidate links transmit selected endpoint words into assigned positions.
All other output words and activity flags are forced to zero.
-/

namespace ThreeFlat.Routing.BatchEndpointLinks

open scoped Classical BigOperators
noncomputable section

variable {B L R P F : Type*} [Fintype B] [Fintype L] [Fintype R] [Fintype P] [DecidableEq R]

abbrev Bank (B : Type*) := B × Bool

/-- Selectors and outputs are private to each candidate batch's side, while
the source payloads are indexed by their common public address. -/
abbrev Pin (B : Type*) (N : L → Finset R) (P : Type*) (u : ℕ) :=
  (Bank B × Spill.Candidate N) ⊕ ((P × Fin u) ⊕ (Bank B × R × Option (Fin u)))

private def wire (N : L → Finset R) (read : Bank B → L → P) (u : ℕ) (g : Bank B) :
    Spill.LinkPin N u → Pin B N P u ⊕ Empty
  | .inl e => .inl (.inl (g,e))
  | .inr (.inl (x,i)) => .inl (.inr (.inl (read g x,i)))
  | .inr (.inr (r,j)) => .inl (.inr (.inr (g,r,j)))

/-- Both endpoint banks of every possible batch are fixed physical copies. -/
def network [Zero F] [One F] (N : L → Finset R) (read : Bank B → L → P) (u : ℕ) :
    BitNetwork F (Fintype.card (Pin B N P u)) :=
  TypedWiring.glue (fun _ : Bank B => Spill.linkNetwork N u) (wire N read u)

def pins {N : L → Finset R} {u : ℕ} (pick : Bank B → Spill.Candidate N → Bool)
    (input : P → Fin u → Bool) (out : Bank B → R → Option (Fin u) → Bool) : Pin B N P u → Bool :=
  Sum.elim (Function.uncurry pick) (Sum.elim (Function.uncurry input)
    (Function.uncurry fun g => Function.uncurry (out g)))

/-- With the selectors fixed, all exposed endpoint-bank outputs are determined. -/
theorem network_eval [CommSemiring F] (N : L → Finset R) (read : Bank B → L → P) (u : ℕ)
    (pick : Bank B → Spill.Candidate N → Bool) (input : P → Fin u → Bool)
    (out : Bank B → R → Option (Fin u) → Bool) :
    TypedWiring.value (network (F := F) N read u) (pins pick input out) =
      if out = fun g => Spill.packed (pick g) (input ∘ read g) then 1 else 0 := by
  classical
  rw [network, TypedWiring.glue_value, Fintype.sum_unique]
  have factor (g : Bank B) (h : Empty → Bool) :
      (fun p => Sum.elim (pins pick input out) h (wire N read u g p)) =
        Spill.linkPins (pick g) (input ∘ read g) (out g) := by
    funext p
    rcases p with e | ⟨x,i⟩ | ⟨r,j⟩ <;> rfl
  calc
    _ = ∏ g, (if out g = Spill.packed (pick g) (input ∘ read g) then (1 : F) else 0) := by
      apply Finset.prod_congr rfl
      intro g _
      exact (congrArg (TypedWiring.value (Spill.linkNetwork (F := F) N u)) (factor g _)).trans
        (Spill.linkNetwork_eval N u (pick g) (input ∘ read g) (out g))
    _ = _ := by
      rw [Fintype.prod_boole]
      congr 1
      exact propext funext_iff.symm

/-- A named unit reports the public link between its source endpoint and
its assigned position. Empty unit types give inactive batch sides. -/
def selector {A : Type*} {N : L → Finset R} (endpoint : A → L) (position : A ↪ R) :
    Spill.Candidate N → Bool :=
  fun e => decide (∃ a, endpoint a = e.1 ∧ position a = e.2.val)

/-- Put a word with a true activity flag at every assigned position. -/
def output {A : Type*} {u : ℕ} (position : A ↪ R) (word : A → Fin u → Bool) :
    R → Option (Fin u) → Bool :=
  Function.extend position (fun a k => k.elim true (word a)) (fun _ _ => false)

omit [Fintype R] [DecidableEq R] in
@[simp] theorem output_at {A : Type*} {u : ℕ} (f : A ↪ R) (word : A → Fin u → Bool)
    (a : A) (j : Option (Fin u)) : output f word (f a) j = j.elim true (word a) := by
  rw [output, f.injective.extend_apply]

omit [Fintype R] [DecidableEq R] in
theorem output_idle {A : Type*} {u : ℕ} (f : A ↪ R) (word : A → Fin u → Bool)
    (r : R) (hr : r ∉ Set.range f) (j : Option (Fin u)) : output f word r j = false := by
  rw [output, Function.extend_apply' _ _ _ hr]

omit [Fintype R] in
theorem packed_eq_output {A : Type*} {N : L → Finset R} {u : ℕ}
    (endpoint : A → L) (position : A ↪ R) (adj : ∀ a, position a ∈ N (endpoint a))
    (word : L → Fin u → Bool) :
    Spill.packed (selector (N := N) endpoint position) word =
      output position (word ∘ endpoint) := by
  classical
  funext r k
  by_cases h : r ∈ Set.range position
  · obtain ⟨a,rfl⟩ := h
    rw [output, position.injective.extend_apply]
    apply Bool.eq_iff_iff.mpr
    rw [Spill.packed, decide_eq_true_eq]
    constructor
    · rintro ⟨x, selected, bit⟩
      obtain ⟨a', address, slot⟩ := of_decide_eq_true selected
      obtain rfl : a' = a := position.injective slot
      simpa only [Function.comp_apply, address] using bit
    · intro bit
      exact ⟨⟨endpoint a,adj a⟩, decide_eq_true ⟨a,rfl,rfl⟩,bit⟩
  · rw [output, Function.extend_apply' _ _ _ h]
    apply decide_eq_false
    rintro ⟨x, selected, _⟩
    obtain ⟨a, _, assigned⟩ := of_decide_eq_true selected
    exact h ⟨a,assigned⟩

/-- Installed selectors in the actual bit network transmit each unit's word
and pin every unused position to zero, on both sides of every batch. -/
theorem network_eval_assigned [CommSemiring F] (N : L → Finset R) (read : Bank B → L → P)
    (u : ℕ) {A : Bank B → Type*} (endpoint : ∀ g, A g → L) (position : ∀ g, A g ↪ R)
    (adj : ∀ g a, position g a ∈ N (endpoint g a)) (input : P → Fin u → Bool)
    (out : Bank B → R → Option (Fin u) → Bool) :
    TypedWiring.value (network (F := F) N read u)
        (pins (fun g => selector (endpoint g) (position g)) input out) =
      if out = fun g => output (position g) (input ∘ read g ∘ endpoint g) then 1 else 0 := by
  rw [network_eval]
  have he g := packed_eq_output (endpoint g) (position g) (adj g) (input ∘ read g)
  simp only [he, Function.comp_assoc]

/-- Install data for the two sides of each active batch in the public bank
index. The complement receives a fixed default. -/
def activeData {A V : Type*} (batch : A ↪ B) (data : A → Bool → V) (empty : V) :
    Bank B → V := fun g => Function.extend batch (fun a => data a g.2) (fun _ => empty) g.1

omit [Fintype B] in
@[simp] theorem activeData_at {A V : Type*} (f : A ↪ B) (data : A → Bool → V)
    (empty : V) (a : A) (s : Bool) : activeData f data empty (f a,s) = data a s :=
  f.injective.extend_apply _ _ _

omit [Fintype B] in
theorem activeData_idle {A V : Type*} (f : A ↪ B) (data : A → Bool → V)
    (empty : V) (b : B) (hb : b ∉ Set.range f) (s : Bool) : activeData f data empty (b,s) = empty :=
  Function.extend_apply' _ _ _ hb

omit [Fintype B] [Fintype P] [Fintype R] in
/-- The physical link outputs split into the transported active words and
the forced-zero words of every inactive candidate batch. -/
theorem packed_activeData (N : L → Finset R) (read : Bank B → L → P)
    (u : ℕ) {A : Type*} (batch : A ↪ B) {U : A → Type*}
    (endpoint : ∀ a, Bool → U a → L) (position : ∀ a, Bool → U a ↪ R)
    (adj : ∀ a s i, position a s i ∈ N (endpoint a s i)) (input : P → Fin u → Bool) :
    let picks := activeData batch (fun a s => selector (N := N) (endpoint a s) (position a s))
      (fun _ => false)
    let words := activeData batch (fun a s =>
      output (position a s) (input ∘ read (batch a,s) ∘ endpoint a s)) (fun _ _ => false)
    (fun g => Spill.packed (picks g) (input ∘ read g)) = words := by
  classical
  dsimp only
  funext ⟨b,s⟩
  by_cases h : b ∈ Set.range batch
  · obtain ⟨a,rfl⟩ := h
    simp only [activeData,batch.injective.extend_apply]
    exact packed_eq_output _ _ (adj a s) _
  · simp only [activeData, Function.extend_apply' _ _ _ h]
    funext r j
    simp [Spill.packed]

/-- Active batches can be indexed by their own type before embedding into
the public pool. Both banks of every other possible batch are forced blank. -/
theorem network_eval_active [CommSemiring F] (N : L → Finset R) (read : Bank B → L → P)
    (u : ℕ) {A : Type*} (batch : A ↪ B) {U : A → Type*}
    (endpoint : ∀ a, Bool → U a → L) (position : ∀ a, Bool → U a ↪ R)
    (adj : ∀ a s i, position a s i ∈ N (endpoint a s i)) (input : P → Fin u → Bool)
    (out : Bank B → R → Option (Fin u) → Bool) :
    let picks := activeData batch (fun a s => selector (N := N) (endpoint a s) (position a s))
      (fun _ => false)
    let words := activeData batch (fun a s =>
      output (position a s) (input ∘ read (batch a,s) ∘ endpoint a s)) (fun _ _ => false)
    TypedWiring.value (network (F := F) N read u) (pins picks input out) =
      if out = words then 1 else 0 := by
  dsimp only
  rw [network_eval, packed_activeData N read u batch endpoint position adj input]

/-- Contracting the shared output words and activity flags has multiplicity one. -/
theorem contract [CommSemiring F] (N : L → Finset R) (read : Bank B → L → P) (u : ℕ)
    (pick : Bank B → Spill.Candidate N → Bool) (input : P → Fin u → Bool)
    (continuation : (Bank B → R → Option (Fin u) → Bool) → F) :
    (∑ out, TypedWiring.value (network N read u) (pins pick input out) * continuation out) =
      continuation (fun g => Spill.packed (pick g) (input ∘ read g)) := by
  simp only [network_eval]
  simp [ite_mul]

/-- Each half of a batch pays once for the bounded-degree link network at
each position and each payload or flag bit. -/
theorem network_cells [Zero F] [One F] (N : L → Finset R) (read : Bank B → L → P)
    (u d : ℕ) (degree : ∀ r, Fintype.card (Spill.Contenders N r) ≤ d) :
    (network (F := F) N read u).cells ≤
      2 * Fintype.card B * Fintype.card R * (u+1) * (2^(2*d+1)*(2*d+3)) := by
  have h := Nat.mul_le_mul_left (Fintype.card (Bank B))
    (Spill.linkNetwork_cells (F := F) N u d degree)
  simpa only [network, TypedWiring.glue_cells, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
    Bank, Fintype.card_prod, Fintype.card_bool, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- For a pool fixed at 129 percent of the parent payload budget, the
forwarders have linear total size, including the activity bit on every word. -/
theorem network_cells_budget [Zero F] [One F] {C H u W : ℕ} (width : 0 < u)
    (N : Fin (C*H) → Finset (Fin H)) (d : ℕ)
    (degree : ∀ r, (Finset.univ.filter fun x => r ∈ N x).card ≤ d)
    (read : Bank (Fin (C*(129*W/(100*(H*u))))) → Fin (C*H) → P) :
    100 * (network (F := F) N read u).cells ≤ 4*C*(2^(2*d+1)*(2*d+3))*129*W := by
  let K := 129*W/(100*(H*u))
  let cost := 2^(2*d+1)*(2*d+3)
  have deg (r : Fin H) : Fintype.card (Spill.Contenders N r) ≤ d := by
    simpa only [Spill.Contenders, Fintype.card_subtype] using degree r
  have size : (network (F := F) N read u).cells ≤ 2*(C*K)*H*(u+1)*cost := by
    simpa only [Fintype.card_fin] using network_cells (F := F) N read u d deg
  have budget : K*(100*(H*u)) ≤ 129*W := Nat.div_mul_le_self _ _
  calc
    _ ≤ 100*(2*(C*K)*H*(u+1)*cost) := Nat.mul_le_mul_left 100 size
    _ ≤ 100*(2*(C*K)*H*(2*u)*cost) := by gcongr; omega
    _ = (4*C*cost)*(K*(100*(H*u))) := by ring
    _ ≤ _ := by simpa only [cost, Nat.mul_assoc] using Nat.mul_le_mul_left (4*C*cost) budget

/-- The local truth-table compiler uses fewer internal bits than cells. -/
theorem network_internal_le_cells [Zero F] [One F] (N : L → Finset R) (read : Bank B → L → P)
    (u : ℕ) : (network (F := F) N read u).internal ≤ (network (F := F) N read u).cells := by
  have h : (Spill.linkNetwork (F := F) N u).internal ≤ (Spill.linkNetwork (F := F) N u).cells := by
    simp only [Spill.linkNetwork, LocalChecks.network, TypedWiring.glue_internal, TypedWiring.glue_cells,
      Fintype.card_ofIsEmpty, zero_add]
    apply Finset.sum_le_sum
    intro i _
    simp only [TypedWiring.localTable, TableCompiler.localTableNetwork_internal,
      TableCompiler.localTableNetwork_cells]
    gcongr; omega
  simpa only [network, TypedWiring.glue_internal, TypedWiring.glue_cells, Fintype.card_ofIsEmpty,
    zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] using
    Nat.mul_le_mul_left (Fintype.card (Bank B)) h

end
end ThreeFlat.Routing.BatchEndpointLinks

end OAI

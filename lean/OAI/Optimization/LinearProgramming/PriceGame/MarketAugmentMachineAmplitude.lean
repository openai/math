import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineStep

/-! Operand and path-length bounds for the serialized transshipment program,
including arbitrary input words of the typed wire format. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment
namespace Machine

open GridMachine
open GridMachine.Table

/-- Reading outside a table selects the specified default. -/
theorem read_property {α : Type} (P : α → Prop) (xs : List α) (d : α) (i : ℕ)
    (hd : P d) (hs : ∀ v ∈ xs, P v) : P ((xs.drop i).headD d) := by
  have sub := List.drop_sublist i xs
  cases h : xs.drop i with
  | nil => exact hd
  | cons a as => exact hs a (sub.subset (a := a) (by simp [h]))

private theorem winner_property (P : Item → Prop) (xs : List Item) (initial : Item)
    (hi : P initial) (hx : ∀ v ∈ xs, P v) :
    P (xs.foldl (fun a b => winner (a,b)) initial) := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons a tail ih =>
    apply ih
    · change P (if improves (initial.1,a.1) then a else initial)
      split
      · exact hx a (by simp)
      · exact hi
    · intro t ht
      exact hx t (by simp [ht])

private abbrev Valid (k U : ℕ) (v : Item) := v.1.1.natAbs ≤ U ∧ v.2.length ≤ k

private theorem layer_valid (G : GridMachine.Table.Graph) (old : List Item) (k R C : ℕ)
    (hG : ∀ r ∈ G, r.1.natAbs ≤ R ∧ ∀ a ∈ r.2, a.1.2.natAbs ≤ C)
    (ho : ∀ v ∈ old, Valid k (R+k*C) v) :
    ∀ v ∈ layer (G,old), Valid (k+1) (R+(k+1)*C) v := by
  intro v hv
  obtain ⟨row,hm,rfl⟩ := List.mem_map.mp hv
  obtain ⟨hr,he⟩ := hG row hm
  apply winner_property
  · change row.1.natAbs ≤ R+(k+1)*C ∧ 0 ≤ k+1
    exact ⟨hr.trans (Nat.le_add_right ..), Nat.zero_le _⟩
  · intro v hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hold := read_property (Valid k (R+k*C)) old zeroItem a.1.1
      (by exact ⟨Nat.zero_le _,Nat.zero_le _⟩) ho
    let prev := neighbor old a
    change (prev.1.1 + a.1.2).natAbs ≤ R+(k+1)*C ∧ prev.2.length+1 ≤ k+1
    change prev.1.1.natAbs ≤ R+k*C ∧ prev.2.length ≤ k at hold
    have hsum := (Int.natAbs_add_le prev.1.1 a.1.2).trans (Nat.add_le_add hold.1 (he a ha))
    exact ⟨by simpa [Nat.add_mul,Nat.add_assoc] using hsum, Nat.succ_le_succ hold.2⟩

/-- Scores increase in magnitude by at most one arc weight per sweep.
Every returned route contains at most one arc per sweep. -/
theorem bellman_bounds (G : GridMachine.Table.Graph) (K R C : ℕ)
    (hG : ∀ r ∈ G, r.1.natAbs ≤ R ∧ ∀ a ∈ r.2, a.1.2.natAbs ≤ C) :
    ∀ v ∈ GridMachine.Table.solve (K,G), v.1.1.natAbs ≤ R+K*C ∧ v.2.length ≤ K := by
  have step : ∀ k, ((GridMachine.Table.update^[k]) (G,G.map start)).1 = G ∧
      ∀ v ∈ ((GridMachine.Table.update^[k]) (G,G.map start)).2, Valid k (R+k*C) v := by
    intro k
    induction k with
    | zero =>
      refine ⟨rfl,?_⟩
      intro v hv
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hv
      exact ⟨by simpa [start] using (hG r hr).1,show 0 ≤ 0 from le_rfl⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨ih.1,?_⟩
      change ∀ v ∈ layer (((GridMachine.Table.update^[k]) (G,G.map start)).1,
        ((GridMachine.Table.update^[k]) (G,G.map start)).2), _
      rw [ih.1]
      exact layer_valid G _ k R C hG ih.2
  exact (step K).2

private abbrev BankBound (xs : Bank) (U : ℕ) := ∀ v ∈ xs, Int.natAbs v ≤ U

private theorem bank_read (xs : Bank) (i U : ℕ) (h : BankBound xs U) :
    ((xs.drop i).headD 0).natAbs ≤ U :=
  read_property (fun x : ℤ => x.natAbs ≤ U) xs 0 i (Nat.zero_le _) h

private theorem replace_bound (xs : Bank) (j : ℕ) (z : ℤ) (U : ℕ)
    (hx : BankBound xs U) (hz : z.natAbs ≤ U) : BankBound (replaceCell ((j,z),xs)) U := by
  intro x h
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
  unfold replacedCell
  split
  · exact hz
  · exact bank_read xs i U hx

private theorem terminals_bound (s : Seed) (U D : ℕ)
    (he : BankBound s.2.2.2.1 U) (ho : BankBound s.2.2.2.2 U) (hd : s.2.2.1.natAbs ≤ D) :
    BankBound (terminalBanks s).1 (U+D) ∧ BankBound (terminalBanks s).2 (U+D) := by
  have he' : BankBound s.2.2.2.1 (U+D) := fun v h => (he v h).trans (Nat.le_add_right ..)
  have ho' : BankBound s.2.2.2.2 (U+D) := fun v h => (ho v h).trans (Nat.le_add_right ..)
  have hz : (newTerminal s).natAbs ≤ U+D := by
    unfold newTerminal
    apply (Int.natAbs_add_le ..).trans
    apply Nat.add_le_add _ hd
    split
    · exact bank_read _ _ _ he
    · simpa only [List.drop_zero] using bank_read _ 0 U ho
  unfold terminalBanks
  split
  · exact ⟨he',replace_bound _ _ _ _ ho' hz⟩
  · exact ⟨replace_bound _ _ _ _ he' hz,ho'⟩

private theorem emitted_bound (x : FlowMachine.Rows.Request) (f : Bool) (C : ℕ)
    (hc : BankBound x.2.1.2.2 C) :
    ∀ a ∈ FlowMachine.Rows.emit f x, a.1.2.natAbs ≤ C := by
  intro a ha
  let k := x.1.1*x.2.2.2.2.length+x.1.2
  let inc := !(xor f (FlowMachine.Rows.read false x.2.1.1 x.1.1))
  let valid := (FlowMachine.Rows.read false x.2.1.2.1 k) &&
    (inc || !decide (FlowMachine.Rows.read 0 x.2.2.1 k = 0))
  let cost := FlowMachine.Rows.read 0 x.2.1.2.2 k
  let out : Arc := ((if f then x.2.1.1.length+x.1.2 else x.1.1, if inc then cost else -cost),
    if inc then 2*k else 2*k+1)
  change a ∈ (if valid then [out] else []) at ha
  by_cases h : valid = true
  · simp only [h,ite_true,List.mem_singleton] at ha
    rw [ha]
    change (if inc then cost else -cost).natAbs ≤ C
    have hu : cost.natAbs ≤ C := bank_read _ _ _ hc
    cases inc <;> simpa using hu
  · simp [h] at ha

private theorem row_bound (x : FlowMachine.Rows.Raw) (j : ℕ) (f : Bool) (R C : ℕ)
    (he : BankBound x.2.2.1 R) (ho : BankBound x.2.2.2 R) (hc : BankBound x.1.2.2 C) :
    (FlowMachine.Rows.row f (j,x)).1.natAbs ≤ R ∧
      ∀ a ∈ (FlowMachine.Rows.row f (j,x)).2, a.1.2.natAbs ≤ C := by
  constructor
  · cases f
    · exact bank_read _ _ _ ho
    · exact bank_read _ _ _ he
  · intro a ha
    obtain ⟨es,hmem,ha⟩ := List.mem_flatten.mp ha
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hmem
    cases f
    · exact emitted_bound _ false C hc a ha
    · exact emitted_bound _ true C hc a ha

private theorem all_rows_bound (x : FlowMachine.Rows.Raw) (R C : ℕ)
    (he : BankBound x.2.2.1 R) (ho : BankBound x.2.2.2 R) (hc : BankBound x.1.2.2 C) :
    ∀ r ∈ FlowMachine.Rows.make x, r.1.natAbs ≤ R ∧ ∀ a ∈ r.2, a.1.2.natAbs ≤ C := by
  intro r hr
  rcases List.mem_append.mp hr with hl | hl
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hl
    exact row_bound x j true R C he ho hc
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hl
    exact row_bound x j false R C he ho hc

/-- Each dynamic payload is bounded entrywise; the shape is independent of the values. -/
structure DynamicBound (s : Dynamic) (U : ℕ) : Prop where
  flow : ∀ v ∈ s.1, v ≤ U
  expert : ∀ v ∈ s.2.1, v.natAbs ≤ U
  option : ∀ v ∈ s.2.2, v.natAbs ≤ U

/-- The route length bounds the increase of a mass; the new scores come from the
actual Bellman result, with the one target bonus included. -/
theorem marketUnit_bound (i : ℕ) (s : Environment) (U C : ℕ) (hs : DynamicBound s.2 U)
    (hD : s.1.1.natAbs ≤ C) (hc : BankBound s.1.2.2.2 C) :
    DynamicBound (marketUnit (i,s)) (max (U+horizon s) (U+C+horizon s*C)) := by
  let K := horizon s
  let x := makeRowsInput (i,s)
  let G := FlowMachine.Rows.make x
  let xs := GridMachine.Table.solve (K,G)
  obtain ⟨he,ho⟩ := terminals_bound (makeSeed (i,s)) U C hs.expert hs.option hD
  have hy := bellman_bounds G K (U+C) C (all_rows_bound x (U+C) C he ho hc)
  have rv (j : ℕ) : ((xs.drop j).headD zeroItem).1.1.natAbs ≤ U+C+K*C ∧
      ((xs.drop j).headD zeroItem).2.length ≤ K :=
    read_property (Valid K (U+C+K*C)) xs zeroItem j ⟨Nat.zero_le _, Nat.zero_le _⟩ hy
  have bank (k j : ℕ) : BankBound (block (k,(j,xs))) (U+C+K*C) := by
    intro v hv
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hv
    exact (rv _).1
  refine ⟨?_,fun v hv => (bank _ _ v hv).trans (Nat.le_max_right ..),
    fun v hv => (bank _ _ v hv).trans (Nat.le_max_right ..)⟩
  intro v hv
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hv
  let p := ((xs.drop (sourceIndex (makeSeed (i,s)))).headD zeroItem).2
  have hp : p.length ≤ K := (rv _).2
  have hm := read_property (fun n : ℕ => n ≤ U) s.2.1 0 j (Nat.zero_le _) hs.flow
  have hq : p.count (2*j) ≤ p.length := List.count_le_length
  change ((s.2.1.drop j).headD 0 + p.count (2*j) - p.count (2*j+1)) ≤ _
  apply (Nat.sub_le ..).trans
  exact (Nat.add_le_add hm (hq.trans hp)).trans (Nat.le_max_left ..)

end Machine
end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

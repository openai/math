import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankConcrete

/-! # The recursive-call ledger of the compiled auxiliary sweeps -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.SweepBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROM InterchangeROMAddress InterchangeAddress InterchangeBatch LoomRegisters
open Physical (Positions Allowance Bank)

variable {J A : Type} {D : A → Type}

private theorem sum_plus (s : List A) (f g k : A → ℕ) (h : ∀ a, f a = g a + k a) :
    (s.map f).sum = (s.map g).sum + (s.map k).sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.map_cons,List.sum_cons,h,ih]; omega

private theorem peak_plus (s : List A) (f g : A → ℕ) (k : ℕ) (h : ∀ a ∈ s, f a ≤ g a+k) :
    (s.map f).foldr max 0 ≤ (s.map g).foldr max 0 + k := by
  induction s with
  | nil => simp
  | cons a s ih =>
    have u := h a (List.mem_cons_self ..)
    have v := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.map_cons,List.foldr_cons]
    omega

theorem field_time (s : Series A) (h : Tree) (enc : (a : A) → D a → Tree) (op : J → (a : A) → D a → D a)
    (cost localCost : J → (a : A) → D a → Allowance) (t : J → (a : A) → D a → ℕ)
    (hc : ∀ j a v, (cost j a v).time = (localCost j a v).time + t j a v)
    (js : List J) (x : (a : A) → D a) :
    (fieldCost s h enc op cost js x).time = (fieldCost s h enc op localCost js x).time +
      ((calls s op js x).map (fun q => t q.1 q.2.1 q.2.2)).sum := by
  induction js generalizing x with
  | nil => simp [fieldCost,calls]
  | cons j js ih =>
    let y a := op j a (x a)
    have v := ih y
    dsimp only [y] at v
    have u := sum_plus s.explore (fun a => (cost j a (x a)).time)
      (fun a => (localCost j a (x a)).time) (fun a => t j a (x a)) (fun a => hc j a _)
    simp only [fieldCost,packetCost,calls,Series.tab,List.map_append,List.map_map,Function.comp_def,
      List.sum_append]
    omega

theorem field_space (s : Series A) (h : Tree) (enc : (a : A) → D a → Tree) (op : J → (a : A) → D a → D a)
    (cost localCost : J → (a : A) → D a → Allowance) (js : List J) (x : (a : A) → D a)
    (S D' : ℕ) (hc : ∀ q ∈ calls s op js x,
      (cost q.1 q.2.1 q.2.2).cap ≤ (localCost q.1 q.2.1 q.2.2).cap+S ∧
      (cost q.1 q.2.1 q.2.2).depth ≤ (localCost q.1 q.2.1 q.2.2).depth+D') :
    (fieldCost s h enc op cost js x).cap ≤ (fieldCost s h enc op localCost js x).cap + S ∧
    (fieldCost s h enc op cost js x).depth ≤ (fieldCost s h enc op localCost js x).depth + D' := by
  induction js generalizing x with
  | nil => simp [fieldCost]
  | cons j js ih =>
    let y a := op j a (x a)
    have v := ih y (fun q hq => hc q (List.mem_append_right _ hq))
    dsimp only [y] at v
    have hrow a := hc (j,⟨a,x a⟩) (List.mem_append_left _ (List.mem_map.mpr ⟨a,s.complete a,rfl⟩))
    have u := peak_plus s.explore (fun a => (cost j a (x a)).cap)
      (fun a => (localCost j a (x a)).cap) S (fun a _ => (hrow a).1)
    have w := peak_plus s.explore (fun a => (cost j a (x a)).depth)
      (fun a => (localCost j a (x a)).depth) D' (fun a _ => (hrow a).2)
    simp only [fieldCost,packetCost,Series.tab,List.map_map,Function.comp_def]
    constructor <;> omega

variable {P G S : Dims.Tape} {p a m l s b f w : ℕ} {E : Type}
local notation "X" => Positions P G S a m b f
local notation "R" => ZMod (p+1)
local notation "F" => Fin (a+m+a)

noncomputable def emitted (w : ℕ) (pay : Series E) (half : ℕ) (inv : Bool) (x y : Bank R (Fin l) (X × E) (Fin s)) :
    List (Request b) :=
  (calls (banks l s) (fun j _ => update inv (half:R) j) (order a m inv) (streams x y)).map
    fun q => request w pay q.1 q.2.2

theorem emitted_length (w : ℕ) (pay : Series E) (half : ℕ) (inv : Bool)
    (x y : Bank R (Fin l) (X × E) (Fin s)) : (emitted w pay half inv x y).length = 2*l*s*m :=
  by simp only [emitted,List.length_map,native_call_count]

theorem emitted_typed (w : ℕ) (pay : Series E) (half : ℕ) (inv : Bool) (x y : Bank R (Fin l) (X × E) (Fin s))
    (q : Request b) (hq : q ∈ emitted w pay half inv x y) :
    (allowed (fun _ : Unit => f) (fun _ => (layout P G S a m b f).count) (fun _ => w) () q ∧
     ∀ k, InterchangePayloadBank.Good (fun _ : Unit => pay) (fun z : R => InterchangeROMTable.numeral z.val) ()
       (q.contents k)) ∧ inherited b P G S q := by
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hq
  exact ⟨⟨Sweep.child_allowed ..,fun k => ⟨_,rfl⟩⟩,Sweep.child_inherited (Equiv.refl F) (fun _ : Unit => P) (fun _ => G) (fun _ => S)
    (fun _ => f) (fun _ => w) z.1 _ ()⟩

def noneCost : Allowance := ⟨0,0,0⟩

private def Split (a z d : Allowance) : Prop :=
  a.time = z.time+d.time ∧ a.cap ≤ z.cap+d.cap ∧ a.depth ≤ z.depth+d.depth

private theorem split_join {a z d : Allowance} (b : Allowance) (h : Split a z d) :
    Split (Sweep.joinCost a b) (Sweep.joinCost z b) d := by
  rcases h with ⟨ht,hs,hd⟩
  simp only [Split,Sweep.joinCost]
  omega

private theorem split_three (x y z u : Tree) (i j : Allowance) {a a₀ d : Allowance} (h : Split a a₀ d) :
    Split (Sweep.cost3 x y z u i j a) (Sweep.cost3 x y z u i j a₀) d := by
  rcases h with ⟨ht,hs,hd⟩
  simp only [Split,Sweep.cost3,seriesClock,costSum,Sweep.three,Sweep.two,Option.elim',
    Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

private theorem split_pivot (b n j : ℕ) (h : Header) (hdr u v : Tree) (ac : Allowance) :
    Split (Sweep.pivotCost b n j h hdr u v ac) (Sweep.pivotCost b n j h hdr u v noneCost) ac := by
  simp only [Split,Sweep.pivotCost,dataSpace,returnSpace,noneCost]
  omega

private theorem row_split (w half : ℕ) (inv : Bool) (pay : Series E) (child : Request b → Allowance)
    (j : F) (g : X → E → R) :
    let z := rowCost w half inv pay (fun _ => noneCost) j g
    let c := rowCost w half inv pay child j g
    let d := child (request w pay j g)
    c.time = z.time + d.time ∧ c.cap ≤ z.cap + d.cap ∧ c.depth ≤ z.depth+d.depth := by
  apply split_join
  apply split_three
  apply split_pivot

noncomputable def charge (w half : ℕ) (inv : Bool) (pay : Series E) (child : Request b → Allowance)
    (x y : Bank R (Fin l) (X × E) (Fin s)) : Allowance :=
  fieldCost (banks l s) (send (header f P G S)) (fun _ => Sweep.row (layout P G S a m b f) pay)
    (fun j _ => update inv (half:R) j) (fun j _ => rowCost w half inv pay child j) (order a m inv) (streams x y)

/-- The recursive clocks add once for each concrete request. Register storage
and return depth add only the peak over the same ledger. -/
theorem charge_split (w half : ℕ) (inv : Bool) (pay : Series E) (child : Request b → Allowance)
    (x y : Bank R (Fin l) (X × E) (Fin s)) :
    let c := charge w half inv pay child x y
    let z := charge w half inv pay (fun _ => noneCost) x y
    let ledger := emitted w pay half inv x y
    c.time = z.time + (ledger.map fun q => (child q).time).sum ∧
    c.cap ≤ z.cap + (ledger.map fun q => (child q).cap).foldr max 0 ∧
    c.depth ≤ z.depth + (ledger.map fun q => (child q).depth).foldr max 0 := by
  dsimp only
  let v := calls (banks l s) (fun j _ => update inv (half:R) j) (order a m inv) (streams x y)
  let get := fun q : F × (i : Bool × Fin (l*s)) × (X → E → R) => child (request w pay q.1 q.2.2)
  simp only [emitted,List.map_map,Function.comp_def]
  refine ⟨field_time _ _ _ _ _ _ (fun j _ g => (child (request w pay j g)).time)
    (by intro j i g; exact (row_split w half inv pay child j g).1) _ _, ?_⟩
  apply field_space
  intro q hq
  have c := (row_split w half inv pay child q.1 q.2.2).2
  have mx {T : Type} (xs : List T) (f : T → ℕ) (t : T) (ht : t ∈ xs) : f t ≤ (xs.map f).foldr max 0 := by
    induction xs with
    | nil => cases ht
    | cons z zs ih => rcases List.mem_cons.mp ht with rfl | h <;> first
                      | exact le_max_left ..
                      | exact (ih h).trans (le_max_right ..)
  have sc := mx v (fun z => (get z).cap) q hq
  have sd := mx v (fun z => (get z).depth) q hq
  exact ⟨c.1.trans (Nat.add_le_add_left sc _),c.2.trans (Nat.add_le_add_left sd _)⟩

end InterchangeROMRepair.SweepBank

end NearSquareRoot
end Computability
end OAI

import OAI.Hierarchy.UniversalGrid
import OAI.Hierarchy.GridThroughPinCore
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Programming the through wires of one selector

Each rail has two port bits per cell on its line. Focus and neighbor links
are ordinary equality tests. At a cell exactly one of the catalyst table,
an extra through equality, or a pair of data pins consumes a passage.
The separate center bits at a touch mount the two data pins at the tick.
-/

namespace Hierarchy.GridThrough

open UniversalGrid
open scoped BigOperators Classical
noncomputable section

/-- A checked controller setting. Each touched pair occupies two distinct
data pins, and every data pin has either one such endpoint or a literal. -/
structure Program (E : Type) {k : ℕ} (n p : ℕ) (width : Fin k → ℕ) where
  direction : E → Fin k
  row : E → Cell k n
  touch : E → Option (Fin (n+1))
  data : Cell k n → Fin p → (Touch touch × Bool) ⊕ Bool
  data_cell : ∀ c i u, data c i = .inl u →
    GridLens.cellOnRail (direction u.1.val.1) (row u.1.val.1) u.1.val.2 = c
  data_once : ∀ u, ∃! ci : Cell k n × Fin p, data ci.1 ci.2 = .inl u
  pass : Cell k n → Catalyst.Wire width → E
  pass_injective : ∀ c, Function.Injective (pass c)
  pass_dir : ∀ c w, direction (pass c w) = w.1
  pass_line : ∀ c w, GridLens.cellOnRail (direction (pass c w)) (row (pass c w))
    (c (direction (pass c w))) = c
  pass_untouched : ∀ c w, touch (pass c w) ≠ some (c (direction (pass c w)))

namespace PinAssignment
variable {E : Type} {k n q d : ℕ} (A : PinAssignment E k n q d)

/-- Number the two sides of each owned pair consecutively, after the public
advice for this particular tick. The controller chooses the order of the pairs. -/
private def pairedSlots {I : Type} {m d : ℕ} (order : I ≃ Fin m)
    (offset : ℕ) (room : offset + 2*m ≤ d) : (I × Bool) ↪ Fin d where
  toFun u := ⟨offset + 2*(order u.1).val + u.2.toNat, by
    have hi := (order u.1).isLt
    have hb := Bool.toNat_le u.2
    omega⟩
  inj' := by
    rintro ⟨i,s⟩ ⟨j,s'⟩ h
    have eq : offset + 2*(order i).val + s.toNat = offset + 2*(order j).val + s'.toNat :=
      congrArg Fin.val h
    have hs := Bool.toNat_le s
    have ht := Bool.toNat_le s'
    have ij : (order i).val = (order j).val := by omega
    apply Prod.ext (order.injective (Fin.ext ij))
    cases s <;> cases s' <;> simp_all

private theorem fiberSlots_injective {T : Type} (owner : E → T)
    (slots : ∀ t, ({e // owner e = t} × Bool) ↪ Fin d) :
    Function.Injective (fun u : E × Bool => (owner u.1,slots (owner u.1) (⟨u.1,rfl⟩,u.2))) := by
  let route (z : Σ t, ({e // owner e = t} × Bool)) := (z.1, slots z.1 z.2)
  have inj : Function.Injective route := by
    rintro ⟨a,u⟩ ⟨a',u'⟩ h
    obtain rfl : a = a' := congrArg (fun z : T × Fin d => z.1) h
    have same : u = u' := (slots a).injective (congrArg (fun z : T × Fin d => z.2) h)
    cases same
    rfl
  intro u v h
  have eq : (⟨owner u.1,⟨u.1,rfl⟩,u.2⟩ : Σ t, ({e // owner e = t} × Bool)) =
      ⟨owner v.1,⟨v.1,rfl⟩,v.2⟩ := inj h
  exact congrArg (fun z : Σ t, ({e // owner e = t} × Bool) => (z.2.1.val,z.2.2)) eq

/-- Pack all assigned pairs after the literal prefix of each receiving tick.
The permutation of the pair fiber is an input, so interval-descriptor order
and any reordering of the evaluator's public inputs can be specified. -/
def ofReserved (direction : E → Fin k) (tick : E → Cell k n × Fin q)
    (offset count : Cell k n × Fin q → ℕ)
    (order : ∀ t, {e // tick e = t} ≃ Fin (count t))
    (room : ∀ t, offset t + 2*count t ≤ d)
    (literal : Cell k n × Fin (q*d) → Bool) : PinAssignment E k n q d where
  direction := direction
  tick := tick
  slot u := pairedSlots (order (tick u.1)) (offset (tick u.1)) (room (tick u.1)) (⟨u.1,rfl⟩,u.2)
  fresh := fiberSlots_injective tick (fun t => pairedSlots (order t) (offset t) (room t))
  literal := literal

theorem ofReserved_slot_val (direction : E → Fin k) (tick : E → Cell k n × Fin q)
    (offset count : Cell k n × Fin q → ℕ)
    (order : ∀ t, {e // tick e = t} ≃ Fin (count t))
    (room : ∀ t, offset t + 2*count t ≤ d)
    (literal : Cell k n × Fin (q*d) → Bool) (e : E) (s : Bool) :
    ((ofReserved direction tick offset count order room literal).slot (e,s)).val =
      offset (tick e) + 2*(order (tick e) ⟨e,rfl⟩).val + s.toNat := rfl

theorem ofReserved_adjacent (direction : E → Fin k) (tick : E → Cell k n × Fin q)
    (offset count : Cell k n × Fin q → ℕ)
    (order : ∀ t, {e // tick e = t} ≃ Fin (count t))
    (room : ∀ t, offset t + 2*count t ≤ d)
    (literal : Cell k n × Fin (q*d) → Bool) (e : E) :
    ((ofReserved direction tick offset count order room literal).slot (e,true)).val =
      ((ofReserved direction tick offset count order room literal).slot (e,false)).val + 1 := by
  simp only [ofReserved_slot_val, Bool.toNat_false, Bool.toNat_true,Nat.add_zero]

/-- Every bit in the reserved advice prefix is genuinely emitted as a
literal by the controller, even at a tick that also owns some rail pairs. -/
theorem ofReserved_prefix (direction : E → Fin k) (tick : E → Cell k n × Fin q)
    (offset count : Cell k n × Fin q → ℕ)
    (order : ∀ t, {e // tick e = t} ≃ Fin (count t))
    (room : ∀ t, offset t + 2*count t ≤ d)
    (literal : Cell k n × Fin (q*d) → Bool) (t : Cell k n × Fin q) (i : Fin d)
    (hi : i.val < offset t) :
    (ofReserved direction tick offset count order room literal).data t.1 (finProdFinEquiv (t.2,i)) =
      .inr (literal (t.1,finProdFinEquiv (t.2,i))) := by
  let B := ofReserved direction tick offset count order room literal
  apply pinSource_unused B.dest literal
  intro u placed
  let e := u.1.val.1
  have c : (tick e).1 = t.1 := congrArg (fun z : Cell k n × Fin (q*d) => z.1) placed
  have pins : ((tick e).2,B.slot (e,u.2)) = (t.2,i) := finProdFinEquiv.injective (congrArg (fun z : Cell k n × Fin (q*d) => z.2) placed)
  have ht : tick e = t := Prod.ext c (congrArg (fun z : Fin q × Fin d => z.1) pins)
  have val : (B.slot (e,u.2)).val = i.val := congrArg Fin.val (congrArg (fun z : Fin q × Fin d => z.2) pins)
  have formula := ofReserved_slot_val direction tick offset count order room literal e u.2
  change (B.slot (e,u.2)).val = _ at formula
  have pref := congrArg offset ht
  omega

end PinAssignment

namespace Program
variable {E : Type} {k n p : ℕ} {width : Fin k → ℕ} (P : Program E n p width)

def railCell (e : E) (t : Fin (n+1)) := GridLens.cellOnRail (P.direction e) (P.row e) t

def Selected (e : E) (t : Fin (n+1)) := ∃ w, P.pass (P.railCell e t) w = e

abbrev Track := E × Fin (n+1) × Bool
abbrev Hidden := Track (E:=E) (n:=n) ⊕ (Touch P.touch × Bool)
abbrev Extra := {z : E × Fin (n+1) // P.touch z.1 ≠ some z.2 ∧ ¬P.Selected z.1 z.2}
abbrev Edge := (E × Bool) ⊕ (E × Fin n) ⊕ P.Extra ⊕ (Touch P.touch × Bool)

variable [Fintype E]

def hiddenOrdinal := Fintype.equivFin P.Hidden
def edgeOrdinal := Fintype.equivFin P.Edge
/-- Positional grid index, with coordinate zero varying fastest. -/
def cellOrdinal : Cell k n ≃ Fin ((n+1)^k) := finFunctionFinEquiv

theorem cellOrdinal_val (c : Cell k n) : (cellOrdinal c).val = ∑ j, (c j).val * (n+1)^j.val :=
  finFunctionFinEquiv_apply c

abbrev Addr := Address E (Fintype.card P.Hidden)

def base (e : E) (t : Fin (n+1)) (s : Bool) : P.Addr :=
  .inl (P.hiddenOrdinal (.inl (e,t,s)))

def center (u : Touch P.touch × Bool) : P.Addr := .inl (P.hiddenOrdinal (.inr u))

def edgePair : P.Edge → P.Addr × P.Addr
  | .inl (e,false) => (.inr (.inl (e,false)), P.base e 0 false)
  | .inl (e,true) => (P.base e (Fin.last n) true, .inr (.inl (e,true)))
  | .inr (.inl (e,t)) => (P.base e t.castSucc true, P.base e t.succ false)
  | .inr (.inr (.inl z)) => (P.base z.val.1 z.val.2 false, P.base z.val.1 z.val.2 true)
  | .inr (.inr (.inr u)) => (P.base u.1.val.1 u.1.val.2 u.2, P.center u)

/-- Both ends of a catalyst pair are actual ports at this cell on its rail. -/
def pin (c : Cell k n) : Catalyst.Port p width → P.Addr
  | .inl i => (P.data c i).elim P.center (fun b => .inr (.inr b))
  | .inr (w,s) => P.base (P.pass c w) (c (P.direction (P.pass c w))) s

def wiring : Wiring E (Catalyst.Port p width) ((n+1)^k) where
  internal := Fintype.card P.Hidden
  pin i := P.pin (cellOrdinal.symm i)
  equal := List.ofFn (fun i => P.edgePair (P.edgeOrdinal.symm i))

/-- The value supplied to a tick pin after propagating the exterior bits. -/
def dataBits (x : GridDiagonal.Pins E) (c : Cell k n) (i : Fin p) : Bool :=
  (P.data c i).elim (fun u => x (u.1.val.1, u.2)) id

/-- Read a physically labelled assignment through the ordinal chart used by
`Wiring`. Only this change-of-index map mentions its arbitrary enumeration. -/
def rawRead (x : GridDiagonal.Pins E) (h : P.Hidden → Bool) (a : P.Addr) : Bool :=
  bit x (fun i => h (P.hiddenOrdinal.symm i)) a

@[simp] theorem rawRead_base (x : GridDiagonal.Pins E) (h : P.Hidden → Bool)
    (e : E) (t : Fin (n+1)) (s : Bool) :
    P.rawRead x h (P.base e t s) = h (.inl (e,t,s)) := by simp [rawRead,bit,base]

@[simp] theorem rawRead_center (x : GridDiagonal.Pins E) (h : P.Hidden → Bool)
    (u : Touch P.touch × Bool) : P.rawRead x h (P.center u) = h (.inr u) := by
  simp [rawRead,bit,center]

/-- Actual local-table input from typed terminal sites, independent of any
enumeration of the hidden choices or the tests. -/
def typedPin (h : P.Hidden → Bool) (c : Cell k n) : Catalyst.Port p width → Bool
  | .inl i => (P.data c i).elim (fun u => h (.inr u)) id
  | .inr (w,s) => h (.inl (P.pass c w,c (P.direction (P.pass c w)),s))

/-- The two endpoints of every ordinary test in the typed physical layout. -/
def typedEdge (x : GridDiagonal.Pins E) (h : P.Hidden → Bool) : P.Edge → Prop
  | .inl (e,false) => x (e,false) = h (.inl (e,0,false))
  | .inl (e,true) => h (.inl (e,Fin.last n,true)) = x (e,true)
  | .inr (.inl (e,t)) => h (.inl (e,t.castSucc,true)) = h (.inl (e,t.succ,false))
  | .inr (.inr (.inl z)) => h (.inl (z.val.1,z.val.2,false)) = h (.inl (z.val.1,z.val.2,true))
  | .inr (.inr (.inr u)) => h (.inl (u.1.val.1,u.1.val.2,u.2)) = h (.inr u)

theorem rawRead_pin (x : GridDiagonal.Pins E) (h : P.Hidden → Bool)
    (c : Cell k n) (j : Catalyst.Port p width) :
    P.rawRead x h (P.pin c j) = P.typedPin h c j := by
  rcases j with i | ⟨w,s⟩
  · cases eq : P.data c i with
    | inl u => simp [pin,typedPin,eq]
    | inr b => simp [pin,typedPin,eq,rawRead,bit]
  · exact P.rawRead_base ..

theorem rawRead_edge (x : GridDiagonal.Pins E) (h : P.Hidden → Bool) (z : P.Edge) :
    (P.rawRead x h (P.edgePair z).1 = P.rawRead x h (P.edgePair z).2) ↔ P.typedEdge x h z := by
  rcases z with ⟨e,s⟩ | ⟨e,t⟩ | z | u
  · cases s <;> simp [edgePair,typedEdge,rawRead,base,bit]
  · simp [edgePair,typedEdge]
  · simp [edgePair,typedEdge]
  · simp [edgePair,typedEdge]

/-- The native physical coefficient can enumerate its own terminal sites and
test list. This holds for a substituted approximation as well as an exact table. -/
def typedEval {F : Type*} [Field F] (f : (Catalyst.Port p width → Bool) → F)
    (x : GridDiagonal.Pins E) : F :=
  ∑ h : P.Hidden → Bool, if ∀ z, P.typedEdge x h z then ∏ c, f (P.typedPin h c) else 0

theorem sum_typed {F : Type*} [Field F] (f : Fin ((n+1)^k) → (Catalyst.Port p width → Bool) → F)
    (x : GridDiagonal.Pins E) :
    (∑ h : Bits P.wiring.internal,
      if ∀ uv ∈ P.wiring.equal, bit x h uv.1 = bit x h uv.2 then
        ∏ i, f i (fun j => bit x h (P.wiring.pin i j)) else 0) =
    ∑ h : P.Hidden → Bool,
      if ∀ z, P.typedEdge x h z then ∏ c, f (cellOrdinal c) (P.typedPin h c) else 0 := by
  symm
  refine Fintype.sum_equiv (P.hiddenOrdinal.arrowCongr (Equiv.refl Bool)) _ _ ?_
  intro h
  change (if ∀ z, P.typedEdge x h z then ∏ c, f (cellOrdinal c) (P.typedPin h c) else 0) =
    if ∀ uv ∈ P.wiring.equal, P.rawRead x h uv.1 = P.rawRead x h uv.2 then
      ∏ i, f i (fun j => P.rawRead x h (P.wiring.pin i j)) else 0
  have checked : (∀ uv ∈ P.wiring.equal, P.rawRead x h uv.1 = P.rawRead x h uv.2) ↔
      ∀ z, P.typedEdge x h z := by
    constructor
    · intro ok z
      apply (P.rawRead_edge x h z).1
      apply ok (P.edgePair z)
      change P.edgePair z ∈ List.ofFn (fun i => P.edgePair (P.edgeOrdinal.symm i))
      exact List.mem_ofFn.mpr ⟨P.edgeOrdinal z,congrArg P.edgePair (P.edgeOrdinal.symm_apply_apply z)⟩
    · intro ok uv hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      exact (P.rawRead_edge ..).2 (ok _)
  by_cases valid : ∀ z, P.typedEdge x h z
  · rw [ite_eq_left valid,ite_eq_left (checked.2 valid)]
    simp only [wiring,rawRead_pin]
    simpa only [Equiv.apply_symm_apply] using
      (cellOrdinal.symm.prod_comp (fun c => f (cellOrdinal c) (P.typedPin h c))).symm
  · rw [ite_eq_right valid,ite_eq_right (mt checked.1 valid)]

theorem eval_typed {F : Type*} [Field F] (f : (Catalyst.Port p width → Bool) → F)
    (x : GridDiagonal.Pins E) : P.wiring.eval f x = P.typedEval f x := by
  unfold Wiring.eval typedEval
  refine Eq.trans ?_ (P.sum_typed (fun _ => f) x)
  apply Finset.sum_congr rfl
  intro h _
  by_cases ok : ∀ uv ∈ P.wiring.equal, bit x h uv.1 = bit x h uv.2
  · simp only [ite_eq_left ok]
  · simp only [ite_eq_right ok]

/-- The index immediately before the break. An untouched rail breaks past
its final cell, so compatibility of its exterior endpoints is required. -/
private def cut (t : Option (Fin (n+1))) : ℕ := t.elim (n+1) Fin.val

private def forcedBit (t : Option (Fin (n+1))) (x : Bool → Bool)
    (i : Fin (n+1)) (s : Bool) : Bool :=
  if i.val + s.toNat ≤ cut t then x false else x true

private theorem forcedBit_touch (i : Fin (n+1)) (x : Bool → Bool) (s : Bool) :
    forcedBit (some i) x i s = x s := by
  cases s <;> simp [forcedBit,cut]

private structure Local (t : Option (Fin (n+1))) (x : Bool → Bool)
    (a : Fin (n+1) → Bool → Bool) : Prop where
  left : x false = a 0 false
  right : a (Fin.last n) true = x true
  next : ∀ i : Fin n, a i.castSucc true = a i.succ false
  through : ∀ i, t ≠ some i → a i false = a i true

private theorem local_iff (t : Option (Fin (n+1))) (x : Bool → Bool)
    (a : Fin (n+1) → Bool → Bool) :
    Local t x a ↔ (t = none → x false = x true) ∧ a = forcedBit t x := by
  constructor
  · intro h
    have before (i : Fin (n+1)) : i.val ≤ cut t → a i false = x false := by
      induction i using Fin.induction with
      | zero => exact fun _ => h.left.symm
      | succ i ih =>
        intro hi
        have strict : i.val < cut t := hi
        have thru := h.through i.castSucc (by intro he; simp [he,cut] at strict)
        exact (h.next i).symm.trans (thru.symm.trans (ih strict.le))
    have after (i : Fin (n+1)) : cut t ≤ i.val → a i true = x true := by
      induction i using Fin.reverseInduction with
      | last => exact fun _ => h.right
      | cast i ih =>
        intro hi
        have hlt : cut t < i.succ.val := Nat.lt_succ_of_le hi
        have thru := h.through i.succ (by intro he; simp [he,cut] at hlt)
        exact (h.next i).trans (thru.trans (ih hlt.le))
    constructor
    · rintro rfl
      have lhs := before (Fin.last n) (by simp [cut])
      exact lhs.symm.trans ((h.through _ (by simp)).trans h.right)
    · funext i s
      cases s
      · simp only [forcedBit,Bool.toNat_false,Nat.add_zero]
        split
        · exact before i ‹_›
        · have gt : cut t < i.val := by omega
          exact (h.through i (by intro he; simp [he,cut] at gt)).trans (after i gt.le)
      · simp only [forcedBit,Bool.toNat_true]
        split
        · have lt : i.val < cut t := by omega
          exact (h.through i (by intro he; simp [he,cut] at lt)).symm.trans (before i lt.le)
        · exact after i (by omega)
  · rintro ⟨compatible,rfl⟩
    constructor
    · simp [forcedBit]
    · cases t with
      | none => simpa [forcedBit,cut] using compatible rfl
      | some j =>
        have hj := j.isLt
        have hn : ¬n+1 ≤ j.val := by omega
        simp [forcedBit,cut,Fin.last,hn]
    · intro i
      simp [forcedBit]
    · intro i untouched
      cases t with
      | none =>
        have hi := i.isLt
        simp [forcedBit,cut,show i.val + 1 ≤ n+1 by omega, hi.le]
      | some j =>
        have ne : i.val ≠ j.val := by intro eq; exact untouched (congrArg some (Fin.ext eq.symm))
        simp [forcedBit,cut,show i.val + 1 ≤ j.val ↔ i.val ≤ j.val by omega]

/-- Exterior assignments accepted by a selector. Only entirely untouched
rails restrict their exterior endpoints. -/
def Compatible (x : GridDiagonal.Pins E) := ∀ e, P.touch e = none → x (e,false) = x (e,true)

private def trackValue (h : Bits (Fintype.card P.Hidden)) (e : E) (t : Fin (n+1))
    (s : Bool) : Bool := h (P.hiddenOrdinal (.inl (e,t,s)))

private def aliasValue (h : Bits (Fintype.card P.Hidden)) (u : Touch P.touch × Bool) :=
  h (P.hiddenOrdinal (.inr u))

private def setting (x : GridDiagonal.Pins E) : Bits (Fintype.card P.Hidden) :=
  fun i => (P.hiddenOrdinal.symm i).elim
    (fun z => forcedBit (P.touch z.1) (fun s => x (z.1,s)) z.2.1 z.2.2)
    (fun u => x (u.1.val.1,u.2))

@[simp] private theorem setting_track (x : GridDiagonal.Pins E) (e : E) (i : Fin (n+1)) (s : Bool) :
    P.trackValue (P.setting x) e i s = forcedBit (P.touch e) (fun b => x (e,b)) i s := by
  simp [trackValue,setting]

@[simp] private theorem setting_alias (x : GridDiagonal.Pins E) (u : Touch P.touch × Bool) :
    P.aliasValue (P.setting x) u = x (u.1.val.1,u.2) := by simp [aliasValue,setting]

private def Links (x : GridDiagonal.Pins E) (h : Bits (Fintype.card P.Hidden)) :=
  ∀ z : P.Edge, bit x h (P.edgePair z).1 = bit x h (P.edgePair z).2

private def Passes (h : Bits (Fintype.card P.Hidden)) (c : Cell k n) :=
  ∀ w, P.trackValue h (P.pass c w) (c (P.direction (P.pass c w))) false =
       P.trackValue h (P.pass c w) (c (P.direction (P.pass c w))) true

private theorem supports_iff (x : GridDiagonal.Pins E) (h : Bits (Fintype.card P.Hidden)) :
    P.Links x h ∧ (∀ c, P.Passes h c) ↔ P.Compatible x ∧ h = P.setting x := by
  constructor
  · rintro ⟨links, passes⟩
    have localRail (e : E) : Local (P.touch e) (fun b => x (e,b)) (P.trackValue h e) := by
      refine ⟨links (.inl (e,false)), links (.inl (e,true)), fun i => links (.inr (.inl (e,i))), ?_⟩
      intro i unt
      by_cases sel : P.Selected e i
      · obtain ⟨w, hw⟩ := sel
        have occupied := passes (P.railCell e i) w
        rw [hw] at occupied
        simpa only [railCell,GridLens.cellOnRail_axis] using occupied
      · exact links (.inr (.inr (.inl ⟨(e,i),unt,sel⟩)))
    have unique (e : E) := (local_iff _ _ _).1 (localRail e)
    refine ⟨fun e => (unique e).1, ?_⟩
    funext i
    obtain ⟨z,rfl⟩ := P.hiddenOrdinal.surjective i
    cases z with
    | inl z =>
      rcases z with ⟨e,t,s⟩
      change P.trackValue h e t s = P.trackValue (P.setting x) e t s
      rw [setting_track]
      exact congrFun (congrFun (unique e).2 t) s
    | inr u =>
      change P.aliasValue h u = P.aliasValue (P.setting x) u
      rw [setting_alias]
      have eq : P.trackValue h u.1.val.1 u.1.val.2 u.2 = P.aliasValue h u :=
        links (.inr (.inr (.inr u)))
      rw [← eq, (unique u.1.val.1).2, u.1.property]
      exact forcedBit_touch ..
  · rintro ⟨compat,rfl⟩
    have localRail (e : E) : Local (P.touch e) (fun s => x (e,s)) (P.trackValue (P.setting x) e) :=
      (local_iff ..).2 ⟨compat e, funext (fun t => funext (fun s => P.setting_track x e t s))⟩
    constructor
    · rintro (⟨e,s⟩ | ⟨e,i⟩ | z | u)
      · cases s
        · exact (localRail e).left
        · exact (localRail e).right
      · exact (localRail e).next i
      · exact (localRail z.val.1).through z.val.2 z.property.1
      · change P.trackValue (P.setting x) u.1.val.1 u.1.val.2 u.2 = P.aliasValue (P.setting x) u
        rw [setting_track,setting_alias,u.1.property]
        exact forcedBit_touch ..
    · exact fun c w => (localRail (P.pass c w)).through _ (P.pass_untouched c w)

private theorem links_list (x : GridDiagonal.Pins E) (h : Bits (Fintype.card P.Hidden)) :
    (∀ uv ∈ P.wiring.equal, bit x h uv.1 = bit x h uv.2) ↔ P.Links x h := by
  constructor
  · intro ok z
    apply ok (P.edgePair z)
    change P.edgePair z ∈ List.ofFn _
    exact List.mem_ofFn.mpr ⟨P.edgeOrdinal z, by simp⟩
  · intro ok uv mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact ok _

/-- Bit-level uniqueness before taking any field-valued sum. This tests
the actual equality list and the actual catalyst pins of every cell. -/
theorem unique_ideal_setting (x : GridDiagonal.Pins E) (compatible : P.Compatible x) :
    ∃! h : Bits P.wiring.internal,
      (∀ uv ∈ P.wiring.equal, bit x h uv.1 = bit x h uv.2) ∧
        ∀ c w, bit x h (P.pin c (.inr (w,false))) = bit x h (P.pin c (.inr (w,true))) := by
  obtain ⟨links,passes⟩ := (P.supports_iff x (P.setting x)).2 ⟨compatible,rfl⟩
  refine ⟨P.setting x, ⟨(P.links_list ..).2 links,passes⟩,?_⟩
  rintro h ⟨ok,occupied⟩
  exact ((P.supports_iff x h).1 ⟨(P.links_list ..).1 ok,occupied⟩).2

private theorem pin_setting (x : GridDiagonal.Pins E) (c : Cell k n) (i : Fin p) :
    bit x (P.setting x) (P.pin c (.inl i)) = P.dataBits x c i := by
  cases eq : P.data c i with
  | inl u => simpa [pin,dataBits,eq,center,bit,aliasValue] using P.setting_alias x u
  | inr b => simp [pin,dataBits,eq,bit]

variable {F : Type*} [Field F]

private theorem cellProduct (f : (Fin p → Bool) → F) (x : GridDiagonal.Pins E)
    (h : Bits (Fintype.card P.Hidden)) :
    (∏ i, Catalyst.ideal width f (fun j => bit x h (P.wiring.pin i j))) =
    if ∀ c, P.Passes h c then
      (∏ c : Cell k n, f (fun i => bit x h (P.pin c (.inl i)))) else 0 := by
  rw [← cellOrdinal.prod_comp (fun i => Catalyst.ideal width f (fun j => bit x h (P.wiring.pin i j)))]
  have at_cell (c : Cell k n) :
      Catalyst.ideal width f (fun j => bit x h (P.wiring.pin (cellOrdinal c) j)) =
      if P.Passes h c then f (fun i => bit x h (P.pin c (.inl i))) else 0 := by
    simp only [wiring,Equiv.symm_apply_apply,Catalyst.ideal]
    let ok := ∀ w : Catalyst.Wire width,
      bit x h (P.pin c (.inr (w,false))) = bit x h (P.pin c (.inr (w,true)))
    by_cases passes : P.Passes h c
    · have actual : ok := passes
      rw [ite_eq_left actual,ite_eq_left passes]
    · have actual : ¬ok := passes
      rw [ite_eq_right actual,ite_eq_right passes]
  simp_rw [at_cell]
  split
  · rename_i allPass
    simp [allPass]
  · rename_i bad
    obtain ⟨c,hc⟩ := not_forall.mp bad
    exact Finset.prod_eq_zero (Finset.mem_univ c) (ite_eq_right hc)

/-- Exact coefficient of this concrete shared-address contraction. There
is one admissible hidden setting if the untouched endpoints agree.
The remaining data are precisely the programmed endpoint bits and literals. -/
theorem eval_ideal (f : (Fin p → Bool) → F) (x : GridDiagonal.Pins E) :
    P.wiring.eval (Catalyst.ideal width f) x =
      if P.Compatible x then ∏ c, f (P.dataBits x c) else 0 := by
  unfold Wiring.eval
  calc
    _ = ∑ h : Bits (Fintype.card P.Hidden),
        if h = P.setting x then (if P.Compatible x then ∏ c, f (P.dataBits x c) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      change Bits (Fintype.card P.Hidden) at h
      split
      · rename_i ok
        have links := (P.links_list x h).1 ok
        refine (P.cellProduct f x h).trans ?_
        split
        · rename_i pass
          obtain ⟨compat,same⟩ := (P.supports_iff x h).1 ⟨links,pass⟩
          subst h
          simp only [ite_eq_left compat,P.pin_setting,ite_true,eq_self]
        · rename_i pass
          split
          · rename_i same
            have bad : ¬P.Compatible x := fun compat => pass ((P.supports_iff x h).2 ⟨compat,same⟩).2
            simp only [ite_eq_right bad]
          · rfl
      · rename_i failed
        split
        · rename_i same
          have bad : ¬P.Compatible x := fun compat => failed ((P.links_list x h).2
            ((P.supports_iff x h).2 ⟨compat,same⟩).1)
          simp only [ite_eq_right bad]
        · rfl
    _ = _ := by simp

/-- Simulation selectors with one touch on each rail read each external
pair at that touch. The q independent tick factors use their own pins. -/
theorem eval_ticks {d q : ℕ} (Q : Program E n (q*d) width)
    (tick : ThreeFlat.BitNetwork F d)
    (allTouched : ∀ e, Q.touch e ≠ none) (x : GridDiagonal.Pins E) :
    Q.wiring.eval (Catalyst.ideal width (Catalyst.tickProduct tick q)) x =
      ∏ c, ∏ j : Fin q, tick.eval (fun a => Q.dataBits x c (finProdFinEquiv (j,a))) := by
  have comp : Q.Compatible x := fun e he => (allTouched e he).elim
  rw [Q.eval_ideal,ite_eq_left comp]
  rfl

/-- The identity selector leaves every rail untouched. Each programmed
constant row has unit value, hence the whole coefficient is the exterior identity. -/
theorem eval_identity (f : (Fin p → Bool) → F) (idle : ∀ e, P.touch e = none)
    (units : ∀ c, f (P.dataBits (fun _ => false) c) = 1) (x : GridDiagonal.Pins E) :
    P.wiring.eval (Catalyst.ideal width f) x = GridDiagonal.identity F x := by
  have fixed (c : Cell k n) : P.dataBits x c = P.dataBits (fun _ => false) c := by
    funext i
    cases eq : P.data c i with
    | inl u => exact (show False by simpa [idle] using u.1.property).elim
    | inr b => simp [dataBits,eq]
  simp [P.eval_ideal,Compatible,idle,fixed,units,GridDiagonal.identity]


end Program
end
end Hierarchy.GridThrough

end OAI

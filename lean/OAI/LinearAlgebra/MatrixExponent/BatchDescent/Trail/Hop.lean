import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact

/-!
# Following original exterior stacks

A span carries a local channel and the original stack key. The
long global name of the channel is shared by every block at its host.
This record contains no values of the exterior input bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail

open Assembly Coloring Packing Classical
variable {F : Type} {x y : Wire} {h u d e : ℕ}

abbrev Short (h d : ℕ) := Fin d ⊕ Fin h

def tag (c : Fin d) (s : Cell h) : Short h d → Bool :=
  Sum.elim (fun j => decide (j = c)) (Fintype.equivOfCardEq
    (show Fintype.card (Cell h) = Fintype.card (Fin h → Bool) by simp [Cell]) s)

theorem tag_injective {c c' : Fin d} {s s' : Cell h} (ht : tag c s = tag c' s') :
    c = c' ∧ s = s' := by
  have h₁ := congrFun ht (.inl c)
  have h₂ := congrArg (fun f => f ∘ Sum.inr) ht
  refine ⟨by simpa [tag] using h₁.symm, ?_⟩
  exact (Fintype.equivOfCardEq
    (show Fintype.card (Cell h) = Fintype.card (Fin h → Bool) by simp [Cell])).injective h₂

structure Record (S : Scheme F) (h d e : ℕ) where
  short : S.Span → Short h d → Bool
  long : B S.m → Fin d → Fin e → Bool

abbrev format (S : Scheme F) (h d e : ℕ) : Format where
  obj := Record S h d e
  pins := (S.Span × Short h d) ⊕ (B S.m × Fin d × Fin e)
  code :=
    { toFun := fun t => Sum.elim (fun v => t.short v.1 v.2) (fun v => t.long v.1 v.2.1 v.2.2)
      invFun := fun x => ⟨fun a b => x (.inl (a, b)), fun a b c => x (.inr (a, b, c))⟩
      left_inv := fun _ => rfl
      right_inv := by intro f; funext i; cases i <;> rfl }

variable [Field F] {S : Scheme F} {r : S.format.obj}
  {G : Diagram F (copies x (2 ^ h * u)) (copies y (2 ^ h * u))} (p : S.Presentation r G)
  (name : Stack.Outer x y ↪ (Fin e → Bool)) (data : Record S h d e)

def Marked (lane : B S.m → Stack.Outer x y → Fin d) : Prop :=
  ∀ (i : Stack.Outer x y) (s : Cell h), ∃ a : S.Span,
    S.width r a = u ∧ data.short a = tag (lane a.1.1 i) s ∧
    data.long a.1.1 (lane a.1.1 i) = name i ∧ ∀ t : Fin u,
      let v := (p.boundary (Stack.bit h u x y ((s, t), i))).val
      v.1 = a ∧ v.2.val = t.val

def Tracks : Prop := ∃ lane, Marked p name data lane

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-!
# Tracking the incoming exterior spans at a new host

A host receives a bounded bank of old names. Each occupied exterior
span points into that bank and selects one old span. Pointwise
preservation of offsets and widths implies preservation of entire
stacks, by injectivity of the two boundary maps.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring Packing Classical
variable {F : Type} {S U : Scheme F} {k : ℕ}

abbrev Stub (S : Scheme F) := B S.h × B S.k × B S.e

def locate (i : B S.m) (q : Stub S) : S.Span := ((i, q.1, q.2.1), q.2.2)
def stub (x : S.Span) : Stub S := (x.1.2.1, x.1.2.2, x.2)

structure Move (S U : Scheme F) (k : ℕ) where
  nav : B U.m → B k → B S.m
  read : U.Span → Option (B k × Stub S)

namespace Move
variable (M : Move S U k)

def previous (q : U.Span) := (M.read q).map (fun p => locate (M.nav q.1.1 p.1) p.2)

variable [Field F] {x y : Wire} {G G' : Diagram F x y} {r : S.format.obj} {R : U.format.obj}
  (p : S.Presentation r G) (q : U.Presentation R G')

structure Agrees : Prop where
  mapped : ∀ j,
    let a := (p.boundary j).val
    let b := (q.boundary j).val
    M.previous b.1 = some a.1 ∧ U.width R b.1 = S.width r a.1 ∧ b.2.val = a.2.val
  active : ∀ w, (M.read w).isSome → ∃ j, (q.boundary j).val.1 = w

variable {M p q}

theorem Agrees.same (h : M.Agrees p q) {a b : slots x ⊕ slots y}
    (hs : (p.boundary a).val.1 = (p.boundary b).val.1) :
    (q.boundary a).val.1 = (q.boundary b).val.1 := by
  let n := (p.boundary b).val.2.val
  have hn : n < U.width R (q.boundary a).val.1 := by
    rw [(h.mapped a).2.1, hs]
    exact (p.boundary b).val.2.isLt
  let t : U.exposed R := ⟨⟨_, ⟨n, hn⟩⟩, (q.boundary a).property⟩
  obtain ⟨c, hc⟩ := q.boundary.surjective t
  have hc' : (q.boundary c).val.1 = (q.boundary a).val.1 := congrArg (fun x => x.val.1) hc
  have he : (p.boundary c).val.1 = (p.boundary b).val.1 := by
    apply Eq.trans _ hs
    apply Option.some.inj
    rw [← (h.mapped c).1, ← (h.mapped a).1, hc']
  have hd : (p.boundary c).val.2.val = (p.boundary b).val.2.val := by
    rw [← (h.mapped c).2.2, hc]
  have : c = b := p.boundary.injective (Subtype.ext (Sigma.ext he
    ((Fin.heq_ext_iff (congrArg (S.width r) he)).mpr hd)))
  exact this ▸ hc'.symm

end Move
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-!
# Candidate origin marks

An incoming channel consists of a local hop and a channel at the
corresponding previous host. Only channels used by an actual span
contribute to the bound on the number of distinct source names.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring Packing Classical

abbrev Candidate (k d : ℕ) := B k × Fin d
abbrev Bits (J K : Type) (h e : ℕ) := (J × (K ⊕ Fin h)) ⊕ (K × Fin e)
abbrev Local {F : Type} (S : Scheme F) (h d e : ℕ) := Bits (Stub S) (Fin d) h e

variable {F : Type} {S U : Scheme F} {k h d e : ℕ}

def Record.row (a : Record S h d e) (v : B S.m) : Local S h d e → Bool :=
  Sum.elim (fun i => a.short (locate v i.1) i.2) (fun t => a.long v t.1 t.2)

/-- Translate a short lane number to a pair of hop and lane number. -/
def mark (p : B k) (x : Short h d → Bool) : Candidate k d ⊕ Fin h → Bool
  | .inl (j, i) => if j = p then x (.inl i) else false
  | .inr t => x (.inr t)

def flagged (c : Candidate k d) (s : Cell h) : Candidate k d ⊕ Fin h → Bool
  | .inl j => decide (j = c)
  | .inr t => tag c.2 s (.inr t)

theorem mark_tag (p : B k) (c : Fin d) (s : Cell h) :
    mark p (tag c s) = flagged (p, c) s := by
  funext q
  rcases q with ⟨j, i⟩ | t
  · by_cases he : j = p <;> simp [mark, tag, flagged, he]
  · rfl

def Move.marked (M : Move S U k) (a : Record S h d e) (q : U.Span) :=
  (M.read q).elim (fun _ => false) (fun t =>
    mark t.1 (a.short (locate (M.nav q.1.1 t.1) t.2)))

def Move.incoming (M : Move S U k) (a : Record S h d e) (v : B U.m) :
    Bits (Stub U) (Candidate k d) h e → Bool :=
  Sum.elim (fun t => M.marked a (locate v t.1) t.2)
    (fun t => a.long (M.nav v t.1.1) t.1.2 t.2)

variable [Field F] {x y : Wire} {u : ℕ}
  {G H : Diagram F (copies x (2 ^ h * u)) (copies y (2 ^ h * u))}
  {r : S.format.obj} {R : U.format.obj} {p : S.Presentation r G} {q : U.Presentation R H}
  {name : Stack.Outer x y ↪ (Fin e → Bool)} {a : Record S h d e} {M : Move S U k}

/-- One original stack becomes one entire span with exactly one incoming
mark. The name may occur through different hops for other stacks. -/
theorem Tracks.incoming (hT : Tracks p name a) (hM : M.Agrees p q) (hu : 0 < u)
    (i : Stack.Outer x y) (s : Cell h) :
    ∃ v c, U.width R v = u ∧ M.marked a v = flagged c s ∧
      a.long (M.nav v.1.1 c.1) c.2 = name i ∧ ∀ t : Fin u,
        let b := (q.boundary (Stack.bit h u x y ((s, t), i))).val
        b.1 = v ∧ b.2.val = t.val := by
  obtain ⟨lane, ht⟩ := hT
  obtain ⟨o, hw, ho, he, hb⟩ := ht i s
  let bit (t : Fin u) := Stack.bit h u x y ((s, t), i)
  let j : Fin u := ⟨0, hu⟩
  let v := (q.boundary (bit j)).val.1
  have h₀ := hM.mapped (bit j)
  have hv : M.previous v = some o := h₀.1.trans (congrArg some (hb j).1)
  obtain ⟨⟨w, t⟩, hr, hs⟩ := Option.map_eq_some_iff.mp hv
  have hloc : locate (M.nav v.1.1 w) t = o := hs
  have hname : M.nav v.1.1 w = o.1.1 := congrArg (fun z => z.1.1) hloc
  refine ⟨v, (w, lane o.1.1 i), h₀.2.1.trans ?_, ?_, ?_, fun t => ?_⟩
  · rw [(hb j).1, hw]
  · simp only [Move.marked, hr, Option.elim_some, hloc, ho, mark_tag]
  · exact hname ▸ he
  · exact ⟨hM.same ((hb t).1.trans (hb j).1.symm), ((hM.mapped _).2.2).trans (hb t).2⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

section
/-! # A short return hop and predecessor-span address -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Coloring Assembly

variable {F : Type}

abbrev pointer (S : Scheme F) (k : ℕ) :=
  Format.pair .bit (.pair (.addr k) (.pair (.addr S.h) (.pair (.addr S.k) (.addr S.e))))

def point {k : ℕ} (S : Scheme F) : Option (B k × Stub S) → (pointer S k).obj
  | none => (false, 0, 0, 0, 0)
  | some p => (true, p)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-! # Padding short predecessor pointers to batch-read addresses -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail

open Assembly Coloring Classical
variable {F : Type} (S U : Scheme F) (k : ℕ)

def addressWidth := 1 + max (k + S.h + S.k + S.e) (U.h + U.k + U.e)

private def pointerSlot : (pointer S k).pins ↪ slots (word (addressWidth S U k)) :=
  choice (Function.Embedding.nonempty_of_card_le (by
    change (pointer S k).width ≤ Fintype.card (slots (word (addressWidth S U k)))
    rw [card_slots, wd_word]
    simp only [pointer, Format.width_pair, Format.width_addr, addressWidth]
    change 1 + (k + (S.h + (S.k + S.e))) ≤ _
    omega))

def projection : slots (word (addressWidth S U k)) → (pointer S k).pins ⊕ Bool :=
  Function.extend (pointerSlot S U k) Sum.inl (fun _ => .inr false)

def addresses : Option (B k × Stub S) ↪ B (addressWidth S U k) where
  toFun p := Control.decode _ (Sum.elim ((pointer S k).code (point S p)) id ∘ projection S U k)
  inj' := by
    intro x y he
    have h := (Control.decode _).injective he
    have hx : point S x = point S y := by
      apply (pointer S k).code.injective
      funext j
      have hh := congrFun h (pointerSlot S U k j)
      simpa only [Function.comp_apply, projection, (pointerSlot S U k).injective.extend_apply,
        Sum.elim_inl] using hh
    cases x <;> cases y <;> simp [point] at hx ⊢
    exact hx

abbrev Controls := Stub U × slots (word (addressWidth S U k))

variable {S U k}

def Move.control (M : Move S U k) (v : B U.m) (q : Controls S U k) : Bool :=
  (Control.decode _).symm (addresses S U k (M.read (locate v q.1))) q.2

theorem Move.control_eq (M : Move S U k) (v : B U.m) (q : Controls S U k) :
    M.control v q = Sum.elim ((pointer S k).code (point S (M.read (locate v q.1)))) id
      (projection S U k q.2) :=
  congrFun ((Control.decode _).symm_apply_apply _) q.2

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-! # Long and short fields of an exterior-tracking step -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring
variable {F : Type} {S U : Scheme F} {k h d e : ℕ}

abbrev rowFormat (S : Scheme F) (h d e : ℕ) : Format :=
  ⟨Local S h d e → Bool, Local S h d e, .refl _⟩

abbrev localCommands (S U : Scheme F) (k : ℕ) : Format :=
  .vec U.h (.vec U.k (.vec U.e (pointer S k)))

abbrev controls (S U : Scheme F) (k : ℕ) := (localCommands S U k).vec U.m

abbrev receipts (S U : Scheme F) (k h d e : ℕ) :=
  Format.vec U.m (.vec k (rowFormat S h d e))

def Move.commands (M : Move S U k) : (controls S U k).obj :=
  fun a b c d => point S (M.read ((a, b, c), d))

def Move.received (M : Move S U k) (data : Record S h d e) : (receipts S U k h d e).obj :=
  fun a b => data.row (M.nav a b)

theorem width_row (S : Scheme F) (h d e : ℕ) :
    (rowFormat S h d e).width = 2 ^ (S.h + S.k + S.e) * (d + h) + d * e := by
  simp [rowFormat, Format.width, Local, Bits, Stub, pow_add, mul_assoc]

theorem width_format (S : Scheme F) (h d e : ℕ) :
    (format S h d e).width = 2 ^ S.m * (rowFormat S h d e).width := by
  simp only [format, rowFormat, Format.width, Local, Bits, Stub, Short, Scheme.Span, Scheme.Vtx,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

theorem width_controls (S U : Scheme F) (k : ℕ) :
    (controls S U k).width = 2 ^ U.m * 2 ^ (U.h + U.k + U.e) * (1 + k + S.h + S.k + S.e) := by
  simp only [controls, localCommands, pointer, Format.width_vec, Format.width_pair,
    Format.width_addr, pow_add]
  rw [Format.width_bit]
  ring

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Coloring Assembly

def hop (k : ℕ) : Option (B k) → B (k + 1)
  | some i => ⟨i.val, by have := i.isLt; rw [pow_succ]; omega⟩
  | none => ⟨2 ^ k, by have := Nat.two_pow_pos k; rw [pow_succ]; omega⟩

def subroundNav {F : Type} {S U : Scheme F} (parent : B U.m → B S.m) (r : S.format.obj)
    (i : B U.m) (j : B (S.d + 1)) : B S.m :=
  if hj : j.val < 2 ^ S.d then (r (parent i)).1 ⟨j.val, hj⟩ else parent i

theorem nav_hop {F : Type} {S U : Scheme F} (parent : B U.m → B S.m) (r : S.format.obj)
    (i : B U.m) (j : Option (B S.d)) :
    subroundNav (U := U) parent r i (hop S.d j) = j.elim (parent i) (r (parent i)).1 := by
  cases j <;> simp [subroundNav, hop]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-!
# Looking up a batch of incoming markers

Each bit of a translated marker is either constant or an old marker
bit. Read the resulting columns at the predecessor pointers, then
append the long names, which require no indirect reads.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail

open Assembly Coloring Classical Install
variable {F : Type} (S U : Scheme F) (k h d e : ℕ)

abbrev ReadInput := (B k × Local S h d e) ⊕ Controls S U k
private abbrev Flag := Candidate k d ⊕ Fin h
private abbrev Column (w : ℕ) := B w ⊕ B w × slots (word w)

private theorem stub_card : Fintype.card (Stub S) = 2 ^ (S.h + S.k + S.e) := by
  simp [Stub, B, pow_add, mul_assoc]

private theorem target_le : Fintype.card (Stub U) ≤ 2 ^ addressWidth S U k := by
  rw [stub_card]
  exact Nat.pow_le_pow_right (by decide) (by unfold addressWidth; omega)

private def target : Stub U ↪ B (addressWidth S U k) :=
  choice (Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin]; exact target_le S U k))

private def tap (q : Flag k h d) : Option (B k × Stub S) → ReadInput S U k h d e ⊕ Bool
  | none => .inr false
  | some (j, i) => match q with
    | .inl (p, b) => if p = j then .inl (.inl (j, .inl (i, .inl b))) else .inr false
    | .inr b => .inl (.inl (j, .inl (i, .inr b)))

private def collect : Flag k h d × Column (addressWidth S U k) → ReadInput S U k h d e ⊕ Bool
  | (j, .inl i) => tap S U k h d e j (Function.invFun (addresses S U k) i)
  | (_, .inr (i, b)) => .inl (.inr (Function.invFun (target S U k) i, b))

private def select (q : Stub U × Flag k h d) := (q.2, target S U k q.1)

private def longTap (q : Candidate k d × Fin e) : ReadInput S U k h d e :=
  .inl (q.1.1, .inr (q.1.2, q.2))

private def incoming (x : ReadInput S U k h d e → Bool) : Bits (Stub U) (Candidate k d) h e → Bool :=
  Sum.elim (fun q => Control.read (addressWidth S U k)
    (fun j => Sum.elim x id (collect S U k h d e (q.2, j))) (target S U k q.1))
    (x ∘ longTap S U k h d e)

private theorem incoming_eq (M : Move S U k) (a : Record S h d e) (v : B U.m) :
    incoming S U k h d e (Sum.elim (fun p => a.row (M.nav v p.1) p.2) (M.control v)) =
      M.incoming a v := by
  funext t
  rcases t with ⟨i, j⟩|⟨⟨p, i⟩, z⟩
  · have hi := Function.leftInverse_invFun (target S U k).injective i
    have ha (p) := Function.leftInverse_invFun (addresses S U k).injective p
    simp only [incoming, Sum.elim_inl, Control.read, collect, hi, Sum.elim_inr, Move.control,
      Equiv.apply_symm_apply, ha, Move.incoming, Move.marked]
    cases hp : M.read (locate v i) with
    | none => rfl
    | some q =>
      rcases j with ⟨p, b⟩|b
      · by_cases h : p = q.1 <;> simp [tap, mark, h, Record.row, locate]
      · rfl
  · rfl

private theorem total {x f o l w n m : ℕ} (hw : w + 1 ≤ m) (hm : 100 ≤ m)
    (hc : 2 ^ w ≤ n) (hx : x ≤ 4 * n * m ^ 2) (hf : f ≤ m ^ 2) (ho : o ≤ n) (hl : l ≤ n * m ^ 2) :
    5 * x + (x + 34 * (f * (2 ^ w + 2 ^ w * w)) + f * (10000 * 2 ^ w * (w + 1) ^ 3) +
      (f * 2 ^ w + 2 * (o * f) + o * f)) + (x + 2 * l + l) ≤ n * m ^ 8 := by
  have hw' : w ≤ m := by omega
  have hpow (j : ℕ) (hj : j ≤ 5) : m ^ j ≤ m ^ 5 := Nat.pow_le_pow_right (by omega) hj
  calc
    _ ≤ 5 * (4 * n * m ^ 2) + (4 * n * m ^ 2 + 34 * (m ^ 2 * (n + n * m)) + m ^ 2 * (10000 * n * m ^ 3) +
       (m ^ 2 * n + 2 * (n * m ^ 2) + n * m ^ 2)) + (4 * n * m ^ 2 + 2 * (n * m ^ 2) + n * m ^ 2) := by gcongr
    _ = n * (69 * m ^ 2 + 34 * m ^ 3 + 10000 * m ^ 5) := by ring
    _ ≤ n * (10103 * m ^ 5) := Nat.mul_le_mul_left _ (by have := hpow 2 (by decide); have := hpow 3 (by decide); omega)
    _ ≤ _ := by
      have h : 10103 ≤ m ^ 3 := (by decide : 10103 ≤ 100 ^ 3) |>.trans (Nat.pow_le_pow_left hm _)
      rw [show m ^ 8 = m ^ 3 * m ^ 5 by ring]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h)

variable (F : Type) [Field F]

theorem incoming_net (S U : Scheme F) (k h d e : ℕ) :
    let w := addressWidth S U k
    ∃ f : (ReadInput S U k h d e → Bool) → Bits (Stub U) (Candidate k d) h e → Bool,
      BNet F f ((2 ^ w + e) * (100 + w + 2 ^ k + h + d) ^ 8) ∧
      ∀ (M : Move S U k) (a : Record S h d e) (v : B U.m),
        f (Sum.elim (fun p => a.row (M.nav v p.1) p.2) (M.control v)) = M.incoming a v := by
  intro w
  refine ⟨incoming S U k h d e, ?_, incoming_eq S U k h d e⟩
  have prep := (tap_depends (collect S U k h d e)).bnet F
  have read := (Control.read_net F w).copies (Flag k h d)
  have out := (BNet.id F (Stub U × Flag k h d)).pull (select S U k h d)
  have long := (BNet.id F (Candidate k d × Fin e)).pull (longTap S U k h d e)
  apply (((prep.comp read).comp out).pair long).mono
  let n := 2 ^ w + e
  let m := 100 + w + 2 ^ k + h + d
  have hkpos : 0 < 2 ^ k := by positivity
  have hwpos : 0 < 2 ^ w := by positivity
  have hc : 2 ^ w ≤ n := by omega
  have hm : 100 ≤ m := by omega
  have hk : 2 ^ k * d + h ≤ m ^ 2 := by
    calc
      _ ≤ (2 ^ k + h) * (d + 1) := by rw [mul_add, add_mul, mul_one]; omega
      _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have ho := (target_le S U k).trans hc
  have hs : 2 ^ k * Fintype.card (Stub S) ≤ n := by
    rw [stub_card, ← pow_add]
    apply le_trans _ hc
    exact Nat.pow_le_pow_right (by decide) (by unfold w addressWidth; omega)
  have hl : Fintype.card (Candidate k d × Fin e) ≤ n * m ^ 2 := by
    simp only [Candidate, B, Fintype.card_prod, Fintype.card_fin]
    rw [mul_comm]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hf : Fintype.card (Flag k h d) ≤ m ^ 2 := by simpa [Flag, Candidate, B] using hk
  have hx : Fintype.card (ReadInput S U k h d e) ≤ 4 * n * m ^ 2 := by
    have hz := Nat.le_pow (a := m) (by decide : 0 < 2)
    have hb : d + h ≤ m ^ 2 := by omega
    have hw : w ≤ m ^ 2 := by omega
    calc
      _ = (2 ^ k * Fintype.card (Stub S)) * (d + h) + Fintype.card (Candidate k d × Fin e) +
          Fintype.card (Stub U) * w := by
        simp only [ReadInput, Local, Bits, Controls, Candidate, Fintype.card_sum, Fintype.card_prod,
          B, Fintype.card_fin, card_slots, wd_word, w]
        ring
      _ ≤ n * m ^ 2 + n * m ^ 2 + n * m ^ 2 := by gcongr
      _ ≤ _ := by ring_nf; omega
  have H := total (by omega : w + 1 ≤ m) hm hc hx hf ho hl
  simpa only [Column, B, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin,
    card_slots, wd_word, show localCost 1 = 34 by decide, n, m, w] using H

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

section
/-! # Cost of updating long names and short marks separately -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring
variable {F : Type} (S U : Scheme F) (k h d d' e : ℕ)

def cost :=
  let w := addressWidth S U k
  let m := 100 + w + 2 ^ k * (d + 1) + h + d + d'
  2 ^ U.m * (2 ^ w * m ^ 10 + (m + e) ^ 104)

private theorem overhead (m e n : ℕ) (hm : 100 ≤ m) :
    160 * (n * m ^ 8 + (m + e) ^ 102) ≤ n * m ^ 10 + (m + e) ^ 104 := by
  have h (x j : ℕ) (hx : 100 ≤ x) : 160 * x ^ j ≤ x ^ (j + 2) := by
    rw [pow_add, mul_comm (x ^ j)]
    exact Nat.mul_le_mul_right _ ((by decide : 160 ≤ 100 ^ 2) |>.trans (Nat.pow_le_pow_left hx 2))
  rw [mul_add, mul_left_comm 160 n]
  exact Nat.add_le_add (Nat.mul_le_mul_left n (h m 8 hm)) (h (m + e) 102 (by omega))

private theorem mixed (m e n : ℕ) (hm : 100 ≤ m) :
    (n + e) * m ^ 8 ≤ n * m ^ 8 + (m + e) ^ 102 := by
  rw [add_mul]
  apply Nat.add_le_add_left
  calc
    _ ≤ (m + e) * (m + e) ^ 8 := by gcongr <;> omega
    _ = (m + e) ^ 9 := (pow_succ' _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

theorem execute_bound :
    let w := addressWidth S U k
    let readCost := (2 ^ w + e) * (100 + w + 2 ^ k + h + d) ^ 8
    let x := 100 + Fintype.card (Candidate k d) + d' + h
    let updateCost := Fintype.card (Stub U) * x ^ 8 + (x + e) ^ 102
    ((receipts S U k h d e).pair (controls S U k)).width +
      34 * (2 ^ U.m * Fintype.card (ReadInput S U k h d e)) +
      2 ^ U.m * (readCost + updateCost) + 3 * (format U h d' e).width ≤ cost S U k h d d' e := by
  intro w readCost x updateCost
  let m := 100 + w + 2 ^ k * (d + 1) + h + d + d'
  let T := 2 ^ w * m ^ 8 + (m + e) ^ 102
  have hm : 100 + w + 2 ^ k + 2 ^ k * d + h + d + d' = m := by unfold m; ring
  have hp : 1 ≤ 2 ^ k := by exact Nat.one_le_pow _ _ (by decide)
  have hm' : 100 ≤ m := by omega
  have ho : 2 ^ (U.h + U.k + U.e) ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by unfold w addressWidth; omega)
  have hi : 2 ^ k * 2 ^ (S.h + S.k + S.e) ≤ 2 ^ w := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by unfold w addressWidth; omega)
  have hmix : (2 ^ w + e) * m ≤ T :=
    (Nat.mul_le_mul_left _ (Nat.le_pow (by decide : 0 < 8))).trans (mixed m e (2 ^ w) hm')
  have hr : readCost ≤ T := by
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8)).trans (mixed m e (2 ^ w) hm')
  have hc : updateCost ≤ T := by
    have h₁ : Fintype.card (Stub U) ≤ 2 ^ w := by simpa [Stub, B, pow_add, mul_assoc] using ho
    have h₂ : x ≤ m := by
      simp only [x, Candidate, B, Fintype.card_prod, Fintype.card_fin]
      omega
    unfold updateCost T
    gcongr
  have ha : 2 ^ k * (rowFormat S h d e).width ≤ T := by
    rw [width_row]
    calc
      _ = (2 ^ k * 2 ^ (S.h + S.k + S.e)) * (d + h) + e * (2 ^ k * d) := by ring
      _ ≤ 2 ^ w * m + e * m := Nat.add_le_add (Nat.mul_le_mul hi (by omega)) (Nat.mul_le_mul_left _ (by omega))
      _ ≤ T := by rw [← add_mul]; exact hmix
  have hb : 2 ^ (U.h + U.k + U.e) * w ≤ T :=
    (Nat.mul_le_mul (ho.trans (Nat.le_add_right _ _)) (by omega)).trans hmix
  have hin : Fintype.card (ReadInput S U k h d e) ≤ 2 * T := by
    rw [Fintype.card_sum, Fintype.card_prod (B k), Fintype.card_fin,
      Fintype.card_prod (Stub U), card_slots, wd_word,
      show Fintype.card (Stub U) = 2 ^ (U.h + U.k + U.e) by simp [Stub, B, pow_add, mul_assoc], two_mul]
    exact Nat.add_le_add ha hb
  have hfeed : ((receipts S U k h d e).pair (controls S U k)).width ≤ 2 ^ U.m * (2 * T) := by
    rw [Format.width_pair, width_controls, Format.width_vec, Format.width_vec, mul_assoc, ← mul_add, two_mul]
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add ha ((Nat.mul_le_mul_left _ (by unfold w addressWidth; omega)).trans hb)
  have hout : (format U h d' e).width ≤ 2 ^ U.m * T := by
    rw [width_format, width_row, mul_comm d']
    apply Nat.mul_le_mul_left
    refine le_trans ?_ hmix
    rw [add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul ho (by omega)) (Nat.mul_le_mul_left _ (by omega))
  calc
    _ ≤ 2 ^ U.m * (2 * T) + 34 * (2 ^ U.m * (2 * T)) + 2 ^ U.m * (T + T) + 3 * (2 ^ U.m * T) := by gcongr
    _ ≤ 2 ^ U.m * (160 * T) := by ring_nf; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (overhead m e _ hm')

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-! # Relabeling incoming spans by a compact table of distinct names -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring Packing Classical Finset

variable {F J K : Type} [Fintype J] [Fintype K] {S U : Scheme F} {k h d e : ℕ}

def pool (x : Bits J K h e → Bool) : Compact.Input K e → Bool
  | (c, none) => decide (∃ j, x (.inl (j, .inl c)) = true)
  | (c, some i) => x (.inr (c, i))

def rename (x : Bits J K h e → Bool) (y : Compact.Output K d e → Bool) :
    Bits J (Fin d) h e → Bool
  | .inl (j, .inl i) => decide (∃ c, x (.inl (j, .inl c)) = true ∧ y (.inr (c, i)) = true)
  | .inl (j, .inr t) => x (.inl (j, .inr t))
  | .inr (i, s) => y (.inl (i, s))

def update (d : ℕ) (x : Bits J K h e → Bool) := rename x (Compact.run d (pool x))

def fromRows (x : B S.m → Local S h d e → Bool) : Record S h d e where
  short j t := x j.1.1 (.inl (stub j, t))
  long j c p := x j (.inr (c, p))

def Move.update (M : Move S U k) (d' : ℕ) (a : Record S h d e) : Record U h d' e :=
  fromRows (fun v => Trail.update d' (M.incoming a v))

variable [Field F] {x y : Wire} {u : ℕ}
  {G H : Diagram F (copies x (2 ^ h * u)) (copies y (2 ^ h * u))}
  {r : S.format.obj} {R : U.format.obj} {p : S.Presentation r G} {q : U.Presentation R H}
  {name : Stack.Outer x y ↪ (Fin e → Bool)} {a : Record S h d e} {M : Move S U k}

def origins (q : U.Presentation R H) (v : B U.m) :=
  univ.filter (fun j : Stack.Outer x y => ∃ s t, (q.boundary (Stack.bit h u x y ((s, t), j))).val.1.1.1 = v)

private theorem names_subset (hT : Tracks p name a) (hM : M.Agrees p q) (hu : 0 < u) (v : B U.m) :
    Compact.names (pool (M.incoming a v)) ⊆ (origins q v).image name := by
  rintro _ hname
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hname
  obtain ⟨j, hj⟩ := of_decide_eq_true (mem_filter.mp hc).2
  change M.marked a (locate v j) (.inl c) = true at hj
  have has : (M.read (locate v j)).isSome := by
    cases hp : M.read (locate v j) with
    | none => simp [Move.marked, hp] at hj
    | some v => rfl
  obtain ⟨t, ht⟩ := hM.active _ has
  obtain ⟨⟨⟨s, t⟩, i⟩, rfl⟩ := (Stack.bit h u x y).surjective t
  obtain ⟨v', c', _, hm, he, hb⟩ := hT.incoming hM hu i s
  have hv := (hb t).1.symm.trans ht
  rw [hv] at hm he
  rw [hm] at hj
  have : c = c' := of_decide_eq_true hj
  subst c'
  refine mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, s, t, ?_⟩, he.symm⟩
  exact congrArg (fun v => v.1.1) ht

/-- The name width is paid once per channel, independently of how
many exterior spans and blocks use it. -/
theorem Tracks.update (hT : Tracks p name a) (hM : M.Agrees p q) (hu : 0 < u)
    {d' : ℕ} (hd : 0 < d') (cap : ∀ v, (origins q v).card ≤ d') :
    Tracks q name (M.update d' a) := by
  let b v := M.incoming a v
  have hc (v) : (Compact.names (pool (b v))).card ≤ d' :=
    (card_le_card (names_subset hT hM hu v)).trans (card_image_le.trans (cap v))
  choose f hf using fun v => Compact.correct hd (pool (b v)) (hc v)
  refine ⟨fun z i => f z (name i), fun i s => ?_⟩
  obtain ⟨v, c, hw, hv, he, hb⟩ := hT.incoming hM hu i s
  let z := v.1.1
  have ht (t) : b z (.inl (stub v, t)) = flagged c s t := congrFun hv t
  have hp : pool (b z) (c, none) = true :=
    decide_eq_true ⟨stub v, by rw [ht]; simp [flagged]⟩
  have hn : Compact.name (pool (b z)) c = name i := he
  obtain ⟨hl, hs⟩ := hf z c hp
  rw [hn] at hl hs
  refine ⟨v, hw, ?_, funext hl, hb⟩
  funext t
  change Trail.update d' (b z) (.inl (stub v, t)) = tag (f z (name i)) s t
  cases t with
  | inl t =>
    simp only [Trail.update, rename, ht, flagged, decide_eq_true_eq, exists_eq_left, hs, tag, Sum.elim_inl]
  | inr t => exact ht (.inr t)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-! # Routing channel flags without repeating the long names per block -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Classical Install

variable {F I J K : Type} [Field F] [Fintype I] [Fintype J] [Fintype K]

private theorem any_gate (p : (I → Bool) → J × K → Bool) (hp : Depends p 2) :
    BNet F (fun x j => decide (∃ k, p x (j, k) = true))
      (Fintype.card I + Fintype.card J * (70 * Fintype.card K + 1)) := by
  have h := (hp.bnet F).comp ((BNet.any F K).copies J)
  apply (h.rename (.refl _) (Equiv.prodUnique J Unit)).mono
  rw [Fintype.card_prod, show localCost 2 = 68 by decide]
  exact le_of_eq (by ring)

private theorem join_gate {p : (I → Bool) → K → Bool} {m : ℕ} (hp : BNet F p m)
    (e : J → I ⊕ K) :
    BNet F (fun x => Sum.elim x (p x) ∘ e)
      (7 * Fintype.card I + Fintype.card K + 3 * Fintype.card J + m) := by
  have h := ((BNet.id F I).pair hp).comp ((BNet.id F J).pull e)
  apply h.mono
  rw [Fintype.card_sum]
  omega

variable {h e d : ℕ}

def poolCost (J K : Type) [Fintype J] [Fintype K] (h e : ℕ) :=
  8 * Fintype.card (Bits J K h e)+ 3 * Fintype.card (Compact.Input K e) +
    Fintype.card K * (70 * Fintype.card J + 2)

theorem pool_net : BNet F (pool (J := J) (K := K) (h := h) (e := e)) (poolCost J K h e) := by
  let p (x : Bits J K h e → Bool) (k : K × J) := x (.inl (k.2, .inl k.1))
  have hd : Depends p 2 := by
    intro k
    exact ⟨{.inl (k.2, .inl k.1)}, by simp, fun _ _ H => H _ (by simp)⟩
  let f : Compact.Input K e → Bits J K h e ⊕ K
    | (k, none) => .inr k
    | (k, some j) => .inl (.inr (k, j))
  have hb := join_gate (any_gate (F := F) p hd) f
  convert hb using 1
  · funext x j
    rcases j with ⟨k, _|t⟩ <;> rfl
  · unfold poolCost
    ring

abbrev Join (J K : Type) (h d e : ℕ) := Bits J K h e ⊕ Compact.Output K d e

def renameCost (J K : Type) [Fintype J] [Fintype K] (h d e : ℕ) :=
  8 * Fintype.card (Join J K h d e) + 3 * Fintype.card (Bits J (Fin d) h e) +
    Fintype.card (J × Fin d) * (70 * Fintype.card K + 2)

theorem rename_net :
    BNet F (fun x : Join J K h d e → Bool => rename (x ∘ Sum.inl) (x ∘ Sum.inr))
      (renameCost J K h d e) := by
  let p (x : Join J K h d e → Bool) (k : (J × Fin d) × K) :=
    x (.inl (.inl (k.1.1, .inl k.2))) && x (.inr (.inr (k.2, k.1.2)))
  have hd : Depends p 2 := by
    intro k
    let a : Join J K h d e := .inl (.inl (k.1.1, .inl k.2))
    let b : Join J K h d e := .inr (.inr (k.2, k.1.2))
    exact ⟨{a, b}, Finset.card_le_two, fun _ _ H => congrArg₂ Bool.and (H a (by simp)) (H b (by simp))⟩
  let f : Bits J (Fin d) h e → Join J K h d e ⊕ (J × Fin d)
    | .inl (j, .inl t) => .inr (j, t)
    | .inl (j, .inr t) => .inl (.inl (.inl (j, .inr t)))
    | .inr p => .inl (.inr (.inl p))
  have hb := join_gate (any_gate (F := F) p hd) f
  convert hb using 1
  · funext x t
    rcases t with ⟨j, i|i⟩|⟨k, u⟩
    · simp only [rename, Function.comp_apply, f, Sum.elim_inr, p, Bool.and_eq_true]
    · rfl
    · rfl
  · unfold renameCost
    ring

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

section
/-! # Cost of updating long channel names and short span tags -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail

open Install

private theorem update_bound (J K : Type) [Fintype J] [Fintype K] (h d e : ℕ) :
    5 * Fintype.card (Bits J K h e) + Fintype.card (Bits J K h e) +
      (poolCost J K h e + (Fintype.card K + d + e + 2) ^ 100) + renameCost J K h d e ≤
      Fintype.card J * (100 + Fintype.card K + d + h) ^ 8 +
        (100 + Fintype.card K + d + h + e) ^ 102 := by
  let k := Fintype.card K
  let T := 100 + k + d + h
  let U := T + e
  let per := 22 * (k + h) + 70 * k + 3 * (d + h) + d * (70 * k + 2)
  let common := 22 * k * e + 3 * k * (e + 1) + 2 * k + 8 * (d * e + k * d) + 3 * d * e
  have hp : per ≤ 200 * T ^ 2 := by unfold per T; ring_nf; omega
  have he : common ≤ 200 * U ^ 2 := by unfold common U T; ring_nf; omega
  have aux (m : ℕ) (hm : 100 ≤ m) : 200 * m ^ 2 ≤ m ^ 4 := by
    rw [show m ^ 4 = m ^ 2 * m ^ 2 from pow_add m 2 2]
    exact Nat.mul_le_mul_right _ ((by decide : 200 ≤ 100 ^ 2).trans (Nat.pow_le_pow_left hm _))
  have hp' : per ≤ T ^ 8 :=
    (hp.trans (aux T (by omega))).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have he' : common ≤ U ^ 100 :=
    (he.trans (aux U (by omega))).trans (Nat.pow_le_pow_right (by omega) (by decide))
  calc
    _ = Fintype.card J * per + (common + (k + d + e + 2) ^ 100) := by
      simp only [poolCost, renameCost, Join, Bits, Compact.Input, Compact.Output,
        Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
      unfold per common k
      generalize (Fintype.card K + d + e + 2) ^ 100 = c
      ring
    _ ≤ Fintype.card J * T ^ 8 + (U ^ 100 + U ^ 100) := by
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hp')
        (Nat.add_le_add he' (Nat.pow_le_pow_left (by omega) _))
    _ ≤ _ := by
      apply Nat.add_le_add_left
      change U ^ 100 + U ^ 100 ≤ U ^ 102
      rw [← mul_two, show U ^ 102 = U ^ 100 * U ^ 2 from pow_add U 100 2]
      exact Nat.mul_le_mul_left _ ((by omega : 2 ≤ U).trans (Nat.le_pow (by decide)))

theorem update_net (F J K : Type) [Field F] [Fintype J] [Fintype K] (h d e : ℕ) :
    BNet F (Trail.update (J := J) (K := K) (h := h) (e := e) d)
      (Fintype.card J * (100 + Fintype.card K + d + h) ^ 8 +
        (100 + Fintype.card K + d + h + e) ^ 102) := by
  have hc := (pool_net (J := J) (h := h)).comp (Compact.net F K d e)
  exact (((BNet.id F _).pair hc).comp rename_net).mono (update_bound J K h d e)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-! # Executing a trail update simultaneously at all hosts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail

open Assembly Coloring Install Classical
variable {F : Type} (S U : Scheme F) (k h d e : ℕ)

abbrev feed := (receipts S U k h d e).pair (controls S U k)
private abbrev inputRow : Format := ⟨ReadInput S U k h d e → Bool, _, .refl _⟩

private def wires : B U.m × ReadInput S U k h d e → (feed S U k h d e).pins ⊕ Bool
  | (v, .inl a) => .inl (.inl (v, a))
  | (v, .inr (a, b)) => Sum.map (fun j => .inr (v, a.1, a.2.1, a.2.2, j)) id (projection S U k b)

private def prepare (x : (feed S U k h d e).obj) (v : B U.m) (i : ReadInput S U k h d e) :=
  Sum.elim ((feed S U k h d e).code x) id (wires S U k h d e (v, i))

private theorem prepare_eq (M : Move S U k) (a : Record S h d e) (v : B U.m) :
    prepare S U k h d e (M.received a, M.commands) v =
      Sum.elim (fun p => a.row (M.nav v p.1) p.2) (M.control v) := by
  funext i
  rcases i with ⟨j, b⟩ | ⟨⟨j, p, q⟩, b⟩
  · rfl
  · simp only [prepare, wires, Sum.elim_inr, Move.control_eq]
    cases projection S U k b <;> rfl

private theorem prepare_net [Field F] :
    Circuit F (feed S U k h d e) (.vec U.m (inputRow S U k h d e)) (prepare S U k h d e)
      ((feed S U k h d e).width + 34 * (2 ^ U.m * Fintype.card (ReadInput S U k h d e))) := by
  have ht := (tap_depends (wires S U k h d e)).bnet F
  unfold Circuit
  convert ht using 1
  · funext x ⟨v, i⟩
    change Sum.elim ((feed S U k h d e).code ((feed S U k h d e).code.symm x)) id _ = _
    rw [Equiv.apply_symm_apply]
    rfl
  · rw [Fintype.card_prod (B U.m), Fintype.card_fin, show localCost 1 = 34 by decide]

private theorem fromRows_net [Field F] :
    Circuit F (.vec U.m (rowFormat U h d e)) (format U h d e) fromRows
      (3 * (format U h d e).width) := by
  let p : (format U h d e).pins → B U.m × Local U h d e
    | .inl (j, b) => (j.1.1, .inl (stub j, b))
    | .inr (v, j, b) => (v, .inr (j, b))
  have q := Circuit.project (F := F) (A := .vec U.m (rowFormat U h d e))
    (D := format U h d e) (f := fromRows) p (by rintro x (j | j) <;> rfl)
  apply q.mono
  rw [width_format, Format.width_vec]
  omega

theorem execute_net (F : Type) [Field F] (S U : Scheme F) (k h d d' e : ℕ) :
    ∃ f, Circuit F (feed S U k h d e) (format U h d' e) f (cost S U k h d d' e) ∧
      ∀ (M : Move S U k) (a : Record S h d e), f (M.received a, M.commands) = M.update d' a := by
  obtain ⟨r, hr, he⟩ := incoming_net F S U k h d e
  have up := update_net F (Stub U) (Candidate k d) h d' e
  have step := Circuit.map (F := F) (A := inputRow S U k h d e) (D := rowFormat U h d' e)
    (fun _ : B U.m => Trail.update d' ∘ r) (fun _ => hr.comp up)
  have net := ((prepare_net S U k h d e).comp step).comp (fromRows_net U h d' e)
  refine ⟨_, net.mono (execute_bound S U k h d d' e), fun M a => ?_⟩
  unfold Move.update
  apply congrArg fromRows
  funext i
  exact congrArg (Trail.update d') ((congrArg r (prepare_eq S U k h d e M a i)).trans (he M a i))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

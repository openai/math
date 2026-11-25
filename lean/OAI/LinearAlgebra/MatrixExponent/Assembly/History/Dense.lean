import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import Mathlib.Data.Nat.Log
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Runs

/-!
# Decoding the weight of a contracted station

Atom arguments refer either to exposed arguments of the new station
or to wires summed out inside it. Neither the decoder nor the atom
values need the absolute names of any exterior or internal wires.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Classical

structure History (F X : Type) where
  A : Type
  E : Type
  [atoms : Fintype A]
  [internal : Fintype E]
  I : A → Type
  value : ∀ a, (I a → Bool) → F
  read : ∀ a, I a → X ⊕ E

attribute [instance] History.atoms History.internal

namespace History
variable {F X V E : Type} [Field F] [Fintype V] [Fintype E] {a b : Wire}

def eval (H : History F X) (x : X → Bool) :=
  ∑ z : H.E → Bool, ∏ t, H.value t (Sum.elim x z ∘ H.read t)

variable {G : Diagram F a b} (C : G.Clustering V E)

/-- Track a port all the way through a cluster. Both ends of a hidden
wire give the very same address. -/
def address : G.End → C.collapse.End ⊕ (Σ v, C.hidden v)
  | .inl (.inl x) => .inl (.inl (.inl x))
  | .inr (.inl y) => .inl (.inr (.inl y))
  | .inl (.inr e) => (C.edges.symm e).map (fun i => .inl (.inr i)) id
  | .inr (.inr e) => (C.edges.symm e).map (fun i => .inr (.inr i)) id

def named (G : Diagram F a b) (v : G.V) : G.Port v ↪ G.End where
  toFun i := G.portEquiv ⟨v, i⟩
  inj' _ _ h := eq_of_heq (Sigma.mk.inj_iff.mp (G.portEquiv.injective h)).2

omit [Field F] in
private theorem sample (G : Diagram F a b) (v : G.V) (x y) :
    Transcript.sample (G.table v) (Sum.elim x y ∘ named G v) = G.weight v x y := rfl

private theorem read_address (w : C.collapse.End → Bool) (z : C.Inside) (p : G.End) :
    Sum.elim w (fun e => z e.1 e.2) (address C p) =
      Sum.elim (C.lift (w ∘ Sum.inl) z) (C.lift (w ∘ Sum.inr) z) p := by
  rcases p with (i|e)|(j|e)
  · rfl
  · change Sum.elim _ _ ((C.edges.symm e).map _ _) = Sum.elim _ _ (C.edges.symm e)
    cases C.edges.symm e <;> rfl
  · rfl
  · change Sum.elim _ _ ((C.edges.symm e).map _ _) = Sum.elim _ _ (C.edges.symm e)
    cases C.edges.symm e <;> rfl

variable (H : History F X) (v : V) (out : C.collapse.Port v ≃ X)

/-- A certificate checked pointwise on the atom and bit names. -/
structure Presents where
  atom : H.A ≃ {t // C.owner t = v}
  hidden : H.E ≃ C.hidden v
  arg : ∀ i, G.Port (atom i).val → H.I i
  localValue : ∀ i w, H.value i w = Transcript.sample (G.table (atom i).val) (w ∘ arg i)
  links : ∀ i j, address C (named G (atom i).val j) =
    (H.read i (arg i j)).map (fun p => named C.collapse v (out.symm p)) (fun e => ⟨v, hidden e⟩)

abbrev Bit := C.collapse.End ⊕ (Σ u, C.hidden u)

def embed (hidden : H.E ≃ C.hidden v) : X ⊕ H.E → Bit C :=
  Sum.map (fun p => named C.collapse v (out.symm p)) (fun e => ⟨v, hidden e⟩)

def factor (t : G.V) (w : Bit C → Bool) : F :=
  G.weight t (w ∘ address C ∘ Sum.inl) (w ∘ address C ∘ Sum.inr)

/-- A local correspondence may omit idle factors. Its tests need no
choice of an ordering of the old atom arguments. -/
structure Traces where
  atom : H.A ↪ {t // C.owner t = v}
  hidden : H.E ≃ C.hidden v
  entry : ∀ i w, H.value i (w ∘ embed C H v out hidden ∘ H.read i) = factor C (atom i) w
  idle : ∀ t ∉ Set.range atom, ∀ w, factor C t.val w = 1

variable {C H v out}

def Presents.traces (p : Presents C H v out) : Traces C H v out where
  atom := p.atom.toEmbedding
  hidden := p.hidden
  idle j hj := (hj (p.atom.surjective j)).elim
  entry i w := by
    rw [p.localValue, factor, ← sample]
    apply congrArg
    funext t
    change w (embed C H v out p.hidden (H.read i (p.arg i t))) = _
    unfold embed
    rw [← p.links]
    simp only [Function.comp_apply]
    cases named G (p.atom i).val t <;> rfl

theorem Traces.correct (p : Traces C H v out) (x : X → Bool) :
    H.eval x = Transcript.sample (C.collapse.table v) (x ∘ out) := by
  let f := named C.collapse v
  let w := Function.extend f (x ∘ out) (fun _ => false)
  have hw (t : C.collapse.Port v) : w (named C.collapse v t) = x (out t) :=
    f.injective.extend_apply _ _ _
  have eqn : x ∘ out = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) ∘ f := by
    funext t; rw [Function.comp_apply, ← hw]
    change w (f t) = Sum.elim _ _ (f t)
    cases f t <;> rfl
  rw [eqn, sample, C.weight_collapse]
  unfold eval
  refine Fintype.sum_equiv (p.hidden.arrowCongr (Equiv.refl Bool)) _ _ ?_
  intro z
  let Z : C.Inside := Function.update (fun _ _ => false) v (z ∘ p.hidden.symm)
  let tape : Bit C → Bool := Sum.elim w (fun e => Z e.1 e.2)
  have hread : Sum.elim x z = tape ∘ embed C H v out p.hidden := by
    funext t
    cases t with
    | inl t => simp [tape, embed, hw]
    | inr e => simp [tape, embed, Z]
  have ha : tape ∘ address C = Sum.elim (C.lift (w ∘ Sum.inl) Z) (C.lift (w ∘ Sum.inr) Z) :=
    funext (read_address C w Z)
  have hf (i : G.V) :
      G.weight i (C.lift (w ∘ Sum.inl) Z) (C.lift (w ∘ Sum.inr) Z) = factor C i tape := by
    unfold factor
    simp only [← Function.comp_assoc, ha]
    rfl
  change _ = ∏ t : {t // C.owner t = v}, G.weight t (C.lift _ Z) (C.lift _ Z)
  simp only [hf, hread, Function.comp_assoc, p.entry]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image p.atom))]
  · rw [Finset.prod_image p.atom.injective.injOn]
  · intro j _ hj
    exact p.idle j (by simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hj) tape

theorem Presents.correct (p : Presents C H v out) (x : X → Bool) :
    H.eval x = Transcript.sample (C.collapse.table v) (x ∘ out) :=
  p.traces.correct x

end History
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Local contraction codes

A port reference describes an entire contiguous fragment. The bit
width of a bundle may exceed the size of the code. A common length
table can, for example, give lengths and offsets in bundle units.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Coloring Classical

abbrev Positions {e : ℕ} (w : B e → ℕ) := Σ i, Fin (w i)

/-- The dictionary and the length scale are fixed across all sites. -/
structure Menu (F : Type) (l s d : ℕ) where
  width : B l → B s → ℕ
  value : (i : B l) → (Positions (width i) → Bool) → F
  length : B d → ℕ

/-- The flag is set for a hidden span. -/
abbrev pointer (e d : ℕ) : Format := .pair .bit (.pair (.addr e) (.addr d))

abbrev code (m e l s d : ℕ) : Format :=
  .pair (.vec e (.addr d)) (.vec m (.pair .bit (.pair (.addr l) (.vec s (pointer e d)))))

theorem width_code (m e l s d : ℕ) :
    (code m e l s d).width = 2 ^ e * d + 2 ^ m * (1 + (l + 2 ^ s * (1 + (e + d)))) := by
  simp [code, pointer]

namespace Menu
variable {F : Type} {m e l s d : ℕ} (M : Menu F l s d)
variable (w : B e → ℕ) (c : (code m e l s d).obj)

abbrev Atom := {i : B m // (c.2 i).1 = true}
abbrev label (i : Atom c) := (c.2 i).2.1
abbrev ref (i : Atom c) (j : B s) := (c.2 i).2.2 j
abbrev hidden (j : B e) := M.length (c.1 j)

def capacity (p : (pointer e d).obj) :=
  if p.1 then M.hidden c p.2.1 else w p.2.1

def Fits : Prop :=
  ∀ (i : Atom c) (j : B s) (t : Fin (M.width (label c i) j)),
    M.length (ref c i j).2.2 + t.val < M.capacity w c (ref c i j)

def resolve (p : (pointer e d).obj) (t : Fin (M.capacity w c p)) :
    Positions w ⊕ Positions (M.hidden c) :=
  if h : p.1 then .inr ⟨p.2.1, ⟨t.val, by simpa [capacity, h] using t.isLt⟩⟩
  else .inl ⟨p.2.1, ⟨t.val, by simpa [capacity, h] using t.isLt⟩⟩

def history (h : M.Fits w c) : History F (Positions w) where
  A := Atom c
  E := Positions (M.hidden c)
  I i := Positions (M.width (label c i))
  value i := M.value (label c i)
  read i p := M.resolve w c (ref c i p.1) ⟨_, h i p.1 p.2⟩

/-- A table is decoded without access to its global station number. -/
def decode [Field F] (x : Positions w → Bool) : F :=
  if h : M.Fits w c then (M.history w c h).eval x else 0

theorem decode_eq [Field F] {V E : Type} [Fintype V] [Fintype E] {a b : Wire}
    {G : Diagram F a b} (C : G.Clustering V E) (v : V)
    (p : C.collapse.Port v ≃ Positions w) (h : M.Fits w c)
    (trace : Traces C (M.history w c h) v p) (x : Positions w → Bool) :
    M.decode w c x = Transcript.sample (C.collapse.table v) (x ∘ p) := by
  rw [decode, dite_eq_left h]
  exact trace.correct x

end Menu
end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-!
# Packing local histories at their actual widths

Every tag is a nonnegative integer. Its length is the number of bits
needed to represent it, with zero using no bits. Store a short length
at every slot and enumerate the truncated tags in the corresponding
product space. The long part of the new tag is bounded by the *sum*
of the occupied lengths, with coefficient one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
open Coloring
open scoped Classical

def used (n : ℕ) := Nat.clog 2 (n + 1)

theorem used_le {n d : ℕ} : used n ≤ d ↔ n < 2 ^ d := by
  exact Nat.clog_le_iff_le_pow (by decide)

@[simp] theorem used_zero : used 0 = 0 := by simp [used]

variable {I : Type} [Fintype I] [DecidableEq I] {l k : ℕ}

def cost (x : I → B l) := ∑ i, used (x i).val

def widths (x : I → B l) (i : I) : B (used l) :=
  ⟨used (x i).val, (used_le.mpr (x i).isLt).trans_lt (used_le.mp le_rfl)⟩

abbrev values (b : I → B (used l)) := (i : I) → B (b i).val

def trim (x : I → B l) : values (widths x) :=
  fun i => ⟨(x i).val, used_le.mp le_rfl⟩

def header (I : Type) [Fintype I] (k l : ℕ) := k + Fintype.card I * used l

private def heads : B k × (I → B (used l)) ≃ B (header I k l) :=
  Fintype.equivOfCardEq (by simp [B, ← pow_mul, mul_comm]; rw [header, pow_add])

private def number {b : I → B (used l)} (v : values b) : ℕ :=
  (Fintype.equivFin (values b) v).val

def pack (z : B k × (I → B l)) : ℕ :=
  (heads (z.1, widths z.2)).val + 2 ^ (header I k l) * number (trim z.2)

theorem length (z : B k × (I → B l)) : used (pack z) ≤ header I k l + cost z.2 := by
  have hn : number (trim z.2) < 2 ^ cost z.2 := by
    have h := (Fintype.equivFin (values (widths z.2)) (trim z.2)).isLt
    change number (trim z.2) < Fintype.card (values (widths z.2)) at h
    change number (trim z.2) < Fintype.card ((i : I) → B ((widths z.2) i).val) at h
    rw [Fintype.card_pi] at h
    simp only [B, Fintype.card_fin, Finset.prod_pow_eq_pow_sum] at h
    exact h
  rw [used_le, pow_add]
  unfold pack
  calc
    _ < 2 ^ (header I k l) + 2 ^ (header I k l) * number (trim z.2) :=
      Nat.add_lt_add_right (heads (z.1, widths z.2)).isLt _
    _ = 2 ^ (header I k l) * (number (trim z.2) + 1) := by rw [mul_add, mul_one, add_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ hn

private theorem number_eq {a b : I → B (used l)} {v : values a} {w : values b}
    (h : a = b) (e : number v = number w) : ∀ i, (v i).val = (w i).val := by
  subst b
  have hh : v = w := (Fintype.equivFin _).injective (Fin.ext e)
  simp only [hh, implies_true]

theorem injective : Function.Injective (pack (I := I) (k := k) (l := l)) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have he := congrArg (· % 2 ^ (header I k l)) h
  simp only [pack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Fin.isLt _)] at he
  have hh := heads.injective (Fin.ext he)
  obtain ⟨rfl, hw⟩ := Prod.mk.inj hh
  have he' : number (trim x) = number (trim y) := by
    unfold pack at h
    rw [he] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel h)
  have hxy : x = y := funext fun i => Fin.ext (number_eq hw he' i)
  rw [hxy]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
end

/-!
# Interpreting the local stub arrays

A colony label is unique only inside its host. A neighbor index is
local to the source host. Neither field needs global address bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring Packing

variable {V E P : Type} {r d h e k ℓ : ℕ}

/-- Common indexing of all local arrays. Source and destination use
the same convention for colony labels. -/
structure Stubs (src dst : E → P) (ix : E → Cell r) (owner : P → V) (d h e ℓ : ℕ) where
  block : Cell r ↪ B h
  tag : P → B ℓ
  separate : ∀ p q, owner p = owner q → tag p = tag q → p = q
  stub : E → B e
  unique : ∀ i j, src i = src j → ix i = ix j → stub i = stub j → i = j
  near : E → B d
  neighbor : ∀ i j, src i = src j → (near i = near j ↔ owner (dst i) = owner (dst j))

namespace Stubs
variable {src dst : E → P} {ix : E → Cell r} {owner : P → V}
  (f : Stubs src dst ix owner d h e ℓ)

def pos (i : E) := (rowIndex h e).symm (f.block (ix i), f.stub i)
def key (p : P) := (Labels h ℓ d).serial (0, f.tag p, 0)

variable (x : V → (Input d h e k ℓ).obj) (c : Color r)

/-- The active records enumerate exactly the outgoing units. Only the
local and remote colony keys on those units must be correct. -/
structure Records : Prop where
  active : ∀ v b j, (((x v).2.1 b).2 j).1 = true ↔
    ∃ i, owner (src i) = v ∧ f.block (ix i) = b ∧ f.stub i = j
  color : ∀ i, (x (owner (src i))).1 (f.block (ix i)) = true ↔ thick c (ix i)
  label : ∀ i, ((x (owner (src i))).2.1 (f.block (ix i))).1 = f.tag (src i)
  slot : ∀ i, (((x (owner (src i))).2.1 (f.block (ix i))).2 (f.stub i)).2.1 = f.near i
  remote : ∀ i, (x (owner (src i))).2.2 (f.block (ix i)) (f.near i) = f.tag (dst i)

theorem represents (rec : f.Records x c) (p : P) :
    (rows (x (owner p))).Represents src dst ix c p f.pos (f.key p) := by
  have addr (i : E) : rowIndex h e (f.pos i) = (f.block (ix i), f.stub i) :=
    (rowIndex h e).apply_symm_apply _
  have source (i : E) : (rows (x (owner (src i)))).src (f.pos i) = f.key (src i) := by
    simp only [Rows.src, rows, addr, rec.label, key]
  have dest (i : E) : (rows (x (owner (src i)))).dest (f.pos i) =
      (Labels h ℓ d).serial (0, f.tag (dst i), f.near i) := by
    simp only [Rows.dest, rows, addr, rec.slot, rec.remote]
  constructor
  · intro i j hi hj eq
    have hr := congrArg (rowIndex h e) eq
    rw [addr, addr] at hr
    exact f.unique i j (hi.trans hj.symm) (f.block.injective (Prod.mk.inj hr).1) (Prod.mk.inj hr).2
  · intro i hi
    simp only [Rows.active, rows, addr]
    exact (rec.active _ _ _).mpr ⟨i, congrArg owner hi, rfl, rfl⟩
  · intro j hj ht
    obtain ⟨i, ho, hb, hs⟩ := (rec.active (owner p) _ _).mp hj
    have hp : f.pos i = j := (rowIndex h e).injective ((addr i).trans (Prod.ext hb hs))
    rw [← ho, ← hp, source] at ht
    have he := (Labels h ℓ d).serial.injective ht
    exact ⟨i, f.separate _ _ ho (congrArg (fun z => z.2.1) he), hp⟩
  · intro i hi
    simpa only [hi] using source i
  · intro i hi
    subst p
    simpa only [Rows.thick, rows, addr] using rec.color i
  · intro i j hi hj
    have ht := dest i
    have hu := dest j
    rw [hi] at ht
    rw [hj] at hu
    rw [ht, hu, Equiv.apply_eq_iff_eq]
    have hn := f.neighbor i j (hi.trans hj.symm)
    constructor
    · intro eq
      exact f.separate _ _ (hn.mp (congrArg (fun z => z.2.2) eq)) (congrArg (fun z => z.2.1) eq)
    · intro eq
      rw [eq, hn.mpr (congrArg owner eq)]
  · intro i j _ _
    simp only [Rows.item, rows, addr, Equiv.apply_eq_iff_eq, Prod.mk.injEq, and_true,
      f.block.injective.eq_iff]

end Stubs
end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

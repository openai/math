import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Choices
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Relation
import OAI.LinearAlgebra.MatrixExponent.Diagram.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame

section
/-!
# Numbering within capacity buckets

The decoder at a bucket first range-checks the index, then reads
the entry at that rank in the ordered list for the bucket.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Selector

variable {I A C : Type}

def domain (S : Selector I C) (e : A ≃ I) : Selector A C where
  write a := S.write (e a)
  read c := (S.read c).map e.symm
  valid c a := by
    rw [Option.map_eq_some_iff]
    simp only [e.symm_apply_eq, exists_eq_right, S.valid]

def fiber {C : A → Type} (k : I → A) (S : ∀ a, Selector {i // k i = a} (C a)) :
    Selector I (Σ a, C a) where
  write i := ⟨k i, (S (k i)).write ⟨i, rfl⟩⟩
  read a := ((S a.1).read a.2).map Subtype.val
  valid a i := by
    rcases a with ⟨a, c⟩
    constructor
    · intro he
      obtain ⟨⟨j, hj⟩, hc, rfl⟩ := Option.map_eq_some_iff.mp he
      change k j = a at hj
      subst a
      exact congrArg (Sigma.mk (k j)) (((S _).valid _ _).mp hc)
    · intro he
      cases he
      rw [((S _).valid _ _).mpr rfl]
      rfl

noncomputable section
open scoped Classical
variable {P V k : ℕ} [Fintype I] [LinearOrder I]

/-- A deterministic ordinal per bucket. -/
def ranked {n : ℕ} (h : Fintype.card I ≤ n) : Selector I (Fin n) :=
  (ordinal _ _ h).domain (Fintype.orderIsoFinOfCardEq I rfl).symm.toEquiv

private def level (f : I → ℕ) (hk : ∀ i, f i ≤ 2 ^ k) (i : I) : Fin (k + 1) :=
  ⟨Nat.clog 2 (f i), Nat.lt_succ_of_le (Nat.clog_le_of_le_pow (hk i))⟩

omit [LinearOrder I] in
private theorem fits (f : I → ℕ) (hp : ∀ i, 0 < f i) (hn : Fintype.card I ≤ P)
    (hs : ∑ i, f i ≤ V) (hk : ∀ i, f i ≤ 2 ^ k) (b : Fin (k + 1)) :
    Fintype.card {i // level f hk i = b} ≤ seats P V b.val := by
  rw [Fintype.card_subtype]
  let S := Finset.univ.filter (fun i => level f hk i = b)
  have hb (i : I) (hi : i ∈ S) : 2 ^ b.val ≤ 2 * f i := by
    have he := congrArg Fin.val (Finset.mem_filter.mp hi).2
    rw [← he]
    exact pow_clog_le_twice (hp i)
  refine le_min ((Finset.card_le_univ _).trans hn) ((Nat.le_div_iff_mul_le (by positivity)).mpr ?_)
  calc
    S.card * 2 ^ b.val = ∑ _ ∈ S, 2 ^ b.val := by simp
    _ ≤ ∑ i ∈ S, 2 * f i := Finset.sum_le_sum hb
    _ ≤ ∑ i, 2 * f i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ 2 * V := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ hs

def packed (f : I → ℕ) (hp : ∀ i, 0 < f i) (hn : Fintype.card I ≤ P)
    (hs : ∑ i, f i ≤ V) (hk : ∀ i, f i ≤ 2 ^ k) : Selector I (Slot P V k) :=
  fiber (level f hk) (fun b => ranked (fits f hp hn hs hk b))

theorem packed_size (f : I → ℕ) (hp : ∀ i, 0 < f i) (hn : Fintype.card I ≤ P)
    (hs : ∑ i, f i ≤ V) (hk : ∀ i, f i ≤ 2 ^ k) (i : I) :
    f i ≤ capacity ((packed f hp hn hs hk).write i) :=
  Nat.le_pow_clog (by decide) _

end
end OAI.LinearAlgebra.MatrixExponent.Transcript.Selector
end

section
/-!
# Named chains of equalities

Each free bit has a distinguished root. All positions must be connected
to their named source and no equality may connect different names.
Redundant checks and changes of edge orientation are harmless.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript

variable {X E T : Type}

structure Copies (X E T : Type) where
  link : X ⊕ T → X ⊕ T → Prop
  root : E → T
  origin : T → X ⊕ E
  root_name : ∀ i, origin (root i) = .inr i
  compatible : ∀ a b, link a b → Sum.elim Sum.inl origin a = Sum.elim Sum.inl origin b
  reaches : ∀ i, Relation.EqvGen link (.inr i) (Sum.map id root (origin i))

namespace Copies
variable (C : Copies X E T) (x : X → Bool)

def source := Sum.elim Sum.inl C.origin

def assign (b : E → Bool) : T → Bool := Sum.elim x b ∘ C.origin

def Agrees (t : T → Bool) : Prop := ∀ a b, C.link a b → Sum.elim x t a = Sum.elim x t b

theorem assign_root (b : E → Bool) : C.assign x b ∘ C.root = b := by
  funext i
  simp [assign, C.root_name]

theorem read (b : E → Bool) (a : X ⊕ T) :
    Sum.elim x (C.assign x b) a = Sum.elim x b (C.source a) := by
  cases a <;> rfl

theorem agrees_assign (b : E → Bool) : C.Agrees x (C.assign x b) := by
  intro i j he
  rw [C.read, C.read, show C.source i = C.source j from C.compatible _ _ he]

theorem determines {t : T → Bool} (h : C.Agrees x t) : t = C.assign x (t ∘ C.root) := by
  have he (i j : X ⊕ T) (hij : Relation.EqvGen C.link i j) : Sum.elim x t i = Sum.elim x t j := by
    induction hij with
    | refl => rfl
    | rel a b hab => exact h a b hab
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  funext i
  have hi := he _ _ (C.reaches i)
  unfold assign Function.comp
  cases ha : C.origin i <;> simpa only [ha, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, id_eq] using hi

def assignments : (E → Bool) ≃ {t // C.Agrees x t} where
  toFun b := ⟨C.assign x b, C.agrees_assign x b⟩
  invFun t := t.val ∘ C.root
  left_inv b := C.assign_root x b
  right_inv t := Subtype.ext (C.determines x t.2).symm

noncomputable section
open scoped Classical

/-- Internal summation over physical tape bits is exactly summation
over the independent roots. -/
theorem contract [Fintype E] [Fintype T] {F : Type} [AddCommMonoid F] (f : (T → Bool) → F) :
    (∑ t, if C.Agrees x t then f t else 0) = ∑ b, f (C.assign x b) := by
  rw [← Finset.sum_filter, Finset.sum_subtype (p := C.Agrees x) _ Finset.mem_filter_univ f]
  exact (Fintype.sum_equiv (C.assignments x) _ _ (fun _ => rfl)).symm

end
end Copies
end OAI.LinearAlgebra.MatrixExponent.Transcript
end

/-! # Transporting diagram ports on a fixed private tape -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript
open scoped Classical

variable {F : Type} {x y : Wire}

abbrev Boundary (x y : Wire) := Bool ⊕ (slots x ⊕ slots y)

def exterior (a : Val x) (b : Val y) : Boundary x y → Bool :=
  Sum.elim id (Sum.elim (bits x a) (bits y b))

abbrev Ports (T : Table F) := slots T.1 ⊕ slots T.2.1

def sample (T : Table F) (z : Ports T → Bool) :=
  T.2.2 ((bits T.1).symm (z ∘ Sum.inl)) ((bits T.2.1).symm (z ∘ Sum.inr))

def wires (G : Diagram F x y) (v : G.V) : Ports (G.table v) → Boundary x y ⊕ G.E
  | .inl i => Sum.map (fun p => .inr (.inl p)) id (G.src ⟨v, i⟩)
  | .inr i => Sum.map (fun p => .inr (.inr p)) id (G.dst ⟨v, i⟩)

theorem sample_wires (G : Diagram F x y) (v : G.V) (a : Val x) (b : Val y) (z : G.E → Bool) :
    sample (G.table v) (Sum.elim (exterior a b) z ∘ wires G v) = G.vertex a b z v := by
  unfold sample Diagram.vertex
  apply congrArg₂ (G.table v).2.2 <;> apply congrArg <;> funext i
  · simp only [Function.comp_apply, wires]
    cases G.src ⟨v, i⟩ <;> rfl
  · simp only [Function.comp_apply, wires]
    cases G.dst ⟨v, i⟩ <;> rfl

/-- Taps name physical bit positions. The origin of each must be the
specified exterior bit or internal edge of the diagram. -/
structure Route (G : Diagram F x y) (T : Type) where
  copies : Copies (Boundary x y) G.E T
  tap : ∀ v, Ports (G.table v) → Boundary x y ⊕ T
  source : ∀ v i, copies.source (tap v i) = wires G v i

namespace Route
variable {G : Diagram F x y} {T : Type} (r : Route G T)

def vertex (a : Val x) (b : Val y) (t : T → Bool) (v : G.V) :=
  sample (G.table v) (Sum.elim (exterior a b) t ∘ r.tap v)

theorem vertex_assign (a : Val x) (b : Val y) (z : G.E → Bool) (v : G.V) :
    r.vertex a b (r.copies.assign (exterior a b) z) v = G.vertex a b z v := by
  rw [← sample_wires]
  unfold vertex
  congr 1
  funext i
  simp only [Function.comp_apply, Copies.read, r.source]

variable [Field F]

def value (a : Val x) (b : Val y) (t : T → Bool) : F :=
  if r.copies.Agrees (exterior a b) t then ∏ v, r.vertex a b t v else 0

theorem contract [Fintype T] (a : Val x) (b : Val y) :
    ∑ t, r.value a b t = G.eval a b := by
  unfold value
  rw [Copies.contract]
  simp only [vertex_assign, Diagram.eval]

end Route
end OAI.LinearAlgebra.MatrixExponent.Transcript
end

section
/-!
# A single dictionary for a whole family of station tables

Use the left-to-right order of the named bit positions. The
argument length is exactly the label length plus the station arity.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript

def positions : (a : Wire) → slots a ≃ Fin (wd a)
  | .unit => Equiv.equivOfIsEmpty Empty (Fin 0)
  | .bit => (Equiv.equivPUnit.{1, 1} Unit).trans (Equiv.equivPUnit (Fin 1)).symm
  | .pair a b => ((positions a).sumCongr (positions b)).trans finSumFinEquiv

variable {F : Type} {d : ℕ}

def query (name : Fin d → Bool) (T : Table F) (u : Ports T → Bool) : List Bool :=
  List.ofFn name ++ List.ofFn (u ∘ (positions (.pair T.1 T.2.1)).symm)

theorem query_length (name : Fin d → Bool) (T : Table F) (u : Ports T → Bool) :
    (query name T u).length = d + (wd T.1 + wd T.2.1) := by simp [query, wd]

noncomputable section
open scoped Classical

/-- Valid labels need only distinguish different station tables. -/
structure Dictionary (F : Type) (d : ℕ) where
  table : (Fin d → Bool) → Table F

namespace Dictionary
variable (D : Dictionary F d)

private abbrev Request := Σ c, Ports (D.table c) → Bool

private def encode (u : D.Request) := query u.1 (D.table u.1) u.2

private theorem injected : Function.Injective D.encode := by
  rintro ⟨a, x⟩ ⟨b, y⟩ he
  unfold encode query at he
  have h : a = b := by
    apply List.ofFn_injective
    simpa using congrArg (List.take d) he
  subst b
  have hy := List.ofFn_injective (List.append_cancel_left he)
  have hxy : x = y := by
    funext i
    simpa using congrFun hy (positions (.pair (D.table a).1 (D.table a).2.1) i)
  subst y
  rfl

def eval [Zero F] : List Bool → F :=
  Function.extend D.encode (fun u => sample (D.table u.1) u.2) (fun _ => 0)

theorem eval_query [Zero F] (name : Fin d → Bool) (T : Table F)
    (h : D.table name = T) (u : Ports T → Bool) : D.eval (query name T u) = sample T u := by
  subst T
  exact D.injected.extend_apply _ _ ⟨name, u⟩

theorem of_card [Zero F] (s : Finset (Table F)) (h : s.card ≤ 2 ^ d) :
    ∃ (D : Dictionary F d) (name : s → Fin d → Bool), ∀ a, D.table (name a) = a.val := by
  obtain ⟨f⟩ : Nonempty (s ↪ (Fin d → Bool)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using h
  let z : Table F := ⟨.unit, .unit, fun _ _ => 0⟩
  refine ⟨⟨Function.extend f Subtype.val (fun _ => z)⟩, f, ?_⟩
  exact fun a => f.injective.extend_apply Subtype.val (fun _ => z) a

end Dictionary
end
end OAI.LinearAlgebra.MatrixExponent.Transcript
end

section
/-!
# Ordered bundles at a station

Positions use the left-to-right order of the incoming and then
outgoing ports. An internal bundle occupies a contiguous interval
at each end. Exterior positions may have arbitrary global names.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

open Transcript

variable {F : Type} {a b : Wire} (G : Diagram F a b)

/-- Side of the local port and, for an internal edge, the remote
station and the offset on the opposite side of that station. -/
def portPeer (v : G.V) : Ports (G.table v) → Bool × Option (G.V × ℕ)
  | .inl i => (false, (G.src ⟨v, i⟩).elim (fun _ => none) fun e =>
      let p := G.dst.symm (.inr e)
      some (p.1, (positions (G.table p.1).2.1 p.2).val))
  | .inr i => (true, (G.dst ⟨v, i⟩).elim (fun _ => none) fun e =>
      let p := G.src.symm (.inr e)
      some (p.1, (positions (G.table p.1).1 p.2).val))

def peer (v : G.V) (i : Fin (G.arity v)) :=
  G.portPeer v ((positions (.pair (G.table v).1 (G.table v).2.1)).symm i)

def advance {V : Type} (p : Bool × Option (V × ℕ)) : Bool × Option (V × ℕ) :=
  (p.1, p.2.map (fun t => (t.1, t.2 + 1)))

def PortOrder (R : ℕ) : Prop :=
  ∀ v, ∃ block : Fin (G.arity v) → Fin R, Monotone block ∧
    ∀ i j, i.val + 1 = j.val → block i = block j → G.peer v j = advance (G.peer v i)

theorem portOrder_of_arity {R : ℕ} (h : ∀ v, G.arity v ≤ R) : G.PortOrder R := by
  intro v
  refine ⟨Fin.castLE (h v), fun _ _ he => he, fun i j he hh => ?_⟩
  have := congrArg Fin.val hh
  change i.val = j.val at this
  omega

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-! # Source offsets in ordered runs of parallel wires -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Transcript

variable {F : Type} {a b : Wire} (G : Diagram F a b)

def srcOffset (e : G.E) : ℕ :=
  let p := G.src.symm (.inr e)
  (positions (G.table p.1).1 p.2).val

theorem srcOffset_inj {e f : G.E} (hs : G.source e = G.source f)
    (ho : G.srcOffset e = G.srcOffset f) : e = f := by
  apply Sum.inr.inj
  apply G.src.symm.injective
  unfold source at hs
  unfold srcOffset at ho
  generalize G.src.symm (.inr e) = p, G.src.symm (.inr f) = q at hs ho ⊢
  rcases p with ⟨v, i⟩
  rcases q with ⟨w, j⟩
  change v = w at hs
  subst w
  have he : i = j := (positions (G.table v).1).injective (Fin.ext ho)
  rw [he]

private abbrev indexAt (v : G.V) : Ports (G.table v) ≃ Fin (G.arity v) :=
  positions (.pair (G.table v).1 (G.table v).2.1)

def wireAt (v : G.V) (i : Fin (G.arity v)) : Boundary a b ⊕ G.E :=
  wires G v ((G.indexAt v).symm i)

private theorem port_next (v : G.V) (i j : Ports (G.table v))
    (hs : (positions (.pair (G.table v).1 (G.table v).2.1) i).val + 1 =
      (positions (.pair (G.table v).1 (G.table v).2.1) j).val)
    (hn : G.portPeer v j = advance (G.portPeer v i)) :
    (∃ x y, wires G v i = .inl x ∧ wires G v j = .inl y) ∨
    (∃ e f, wires G v i = .inr e ∧ wires G v j = .inr f ∧
      G.source e = G.source f ∧ G.target e = G.target f ∧ G.srcOffset e + 1 = G.srcOffset f) := by
  rcases i with i | i <;> rcases j with j | j
  · cases hi : G.src ⟨v, i⟩ <;> cases hj : G.src ⟨v, j⟩ <;>
      simp only [portPeer, advance, hi, hj, Sum.elim_inl, Sum.elim_inr, Option.map_none,
        Option.map_some, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, true_and] at hn
    · exact .inl ⟨_, _, by rw [wires, hi]; rfl, by rw [wires, hj]; rfl⟩
    · rename_i e f
      refine .inr ⟨e, f, by rw [wires, hi]; rfl, by rw [wires, hj]; rfl, ?_, hn.1.symm, ?_⟩
      · simp only [source, ←hi, ←hj, Equiv.symm_apply_apply]
      · unfold srcOffset
        rw [←hi, ←hj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact hs
  · cases congrArg Prod.fst hn
  · cases congrArg Prod.fst hn
  · cases hi : G.dst ⟨v, i⟩ <;> cases hj : G.dst ⟨v, j⟩ <;>
      simp only [portPeer, advance, hi, hj, Sum.elim_inl, Sum.elim_inr, Option.map_none,
        Option.map_some, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, true_and] at hn
    · exact .inl ⟨_, _, by rw [wires, hi]; rfl, by rw [wires, hj]; rfl⟩
    · rename_i e f
      refine .inr ⟨e, f, by rw [wires, hi]; rfl, by rw [wires, hj]; rfl, hn.1.symm, ?_, hn.2.symm⟩
      simp only [target, ←hi, ←hj, Equiv.symm_apply_apply]

/-- On adjacent ports within an ordered block, the side stays fixed
and the source offset of an internal wire advances by one. -/
theorem wireAt_next (v : G.V) {i j : Fin (G.arity v)}
    (hs : i.val + 1 = j.val) (hn : G.peer v j = advance (G.peer v i)) :
    (∃ x y, G.wireAt v i = .inl x ∧ G.wireAt v j = .inl y) ∨
    (∃ e f, G.wireAt v i = .inr e ∧ G.wireAt v j = .inr f ∧
      G.source e = G.source f ∧ G.target e = G.target f ∧ G.srcOffset e + 1 = G.srcOffset f) := by
  apply G.port_next _ _ _ _ hn
  change (G.indexAt v ((G.indexAt v).symm i)).val + 1 = (G.indexAt v ((G.indexAt v).symm j)).val
  simpa only [Equiv.apply_symm_apply] using hs

/-- All indexed positions, including both ends of a loop, are distinct. -/
def endAt : (Σ v, Fin (G.arity v)) ≃ G.End :=
  (Equiv.sigmaCongrRight (fun v => (G.indexAt v).symm)).trans G.portEquiv

theorem station_endAt (p : Σ v, Fin (G.arity v)) : G.station (G.endAt p) = p.1 :=
  G.station_port _

def endWire : G.End → Boundary a b ⊕ G.E
  | .inl i => Sum.map (fun t => .inr (.inl t)) id i
  | .inr j => Sum.map (fun t => .inr (.inr t)) id j

theorem wireAt_eq (v : G.V) (i : Fin (G.arity v)) :
    G.wireAt v i = G.endWire (G.endAt ⟨v, i⟩) := by
  change wires G v _ = G.endWire (G.portEquiv ⟨v, (G.indexAt v).symm i⟩)
  cases (G.indexAt v).symm i <;> rfl

theorem peer_side (v : G.V) (i : Fin (G.arity v)) :
    (G.peer v i).1 = (G.endAt ⟨v, i⟩).isRight := by
  change (G.portPeer v ((G.indexAt v).symm i)).1 = (G.portEquiv ⟨v, (G.indexAt v).symm i⟩).isRight
  cases (G.indexAt v).symm i <;> rfl

theorem wireAt_incident (v : G.V) (i : Fin (G.arity v)) {e : G.E} (h : G.wireAt v i = .inr e) :
    G.source e = v ∨ G.target e = v := by
  have hv := G.station_endAt ⟨v, i⟩
  rw [wireAt_eq] at h
  generalize G.endAt ⟨v, i⟩ = z at hv h
  rcases z with (x|e') | (y|e') <;> cases h
  · exact .inl hv
  · exact .inr hv

theorem wireAt_inj (loopless : ∀ e, G.source e ≠ G.target e) (v : G.V) :
    Function.Injective (G.wireAt v) := by
  intro i j h
  have hi := G.station_endAt ⟨v, i⟩
  have hj := G.station_endAt ⟨v, j⟩
  rw [wireAt_eq, wireAt_eq] at h
  have eq : G.endAt ⟨v, i⟩ = G.endAt ⟨v, j⟩ := by
    generalize G.endAt ⟨v, i⟩ = z at hi h ⊢
    generalize G.endAt ⟨v, j⟩ = w at hj h ⊢
    rcases z with (x|e) | (y|e) <;> rcases w with (x'|e') | (y'|e') <;> cases h <;> try rfl
    · exact (loopless _ (hi.trans hj.symm)).elim
    · exact (loopless _ (hj.trans hi.symm)).elim
  exact eq_of_heq (Sigma.mk.inj (G.endAt.injective eq)).2

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-! # Exterior names in station port order -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Transcript

variable {F E : Type} {a b : Wire}

def pickLeft : Boundary a b ⊕ E → Option (slots a)
  | .inl (.inr (.inl i)) => some i
  | _ => none

def pickRight : Boundary a b ⊕ E → Option (slots b)
  | .inl (.inr (.inr j)) => some j
  | _ => none

variable (G : Diagram F a b) (v : G.V)

def extLeft := (List.ofFn (G.wireAt v)).filterMap pickLeft
def extRight := (List.ofFn (G.wireAt v)).filterMap pickRight

private theorem exterior_spec {X : Type} (pick : Boundary a b ⊕ G.E → Option X)
    (side : X → G.End) (hs : ∀ e t, pick (G.endWire e) = some t ↔ e = side t) :
    ((List.ofFn (G.wireAt v)).filterMap pick).Nodup ∧
      ∀ t, t ∈ (List.ofFn (G.wireAt v)).filterMap pick ↔ G.station (side t) = v := by
  have he i t : pick (G.wireAt v i) = some t ↔ G.endAt ⟨v, i⟩ = side t := by
    rw [wireAt_eq, hs]
  constructor
  · rw [List.ofFn_eq_map, List.filterMap_map]
    apply List.Nodup.filterMap _ (List.nodup_finRange _)
    intro i j t hi hj
    have h := G.endAt.injective (((he i t).mp hi).trans ((he j t).mp hj).symm)
    exact eq_of_heq (Sigma.mk.inj h).2
  · intro t
    constructor
    · rintro ht
      obtain ⟨w, hw, heq⟩ := List.mem_filterMap.mp ht
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      rw [← (he i t).mp heq, station_endAt]
    · intro ht
      obtain ⟨⟨w, i⟩, hi⟩ := G.endAt.surjective (side t)
      have hw : w = v := (G.station_endAt ⟨w, i⟩).symm.trans (hi ▸ ht)
      subst w
      exact List.mem_filterMap.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, (he i t).mpr hi⟩

private theorem left_spec : (G.extLeft v).Nodup ∧
    ∀ i, i ∈ G.extLeft v ↔ Packing.portEnd G (.inl i) = v := by
  apply G.exterior_spec v pickLeft (fun i => .inl (.inl i))
  rintro ((i|e)|(j|e)) t <;> simp [endWire, pickLeft]

private theorem right_spec : (G.extRight v).Nodup ∧
    ∀ j, j ∈ G.extRight v ↔ Packing.portEnd G (.inr j) = v := by
  apply G.exterior_spec v pickRight (fun j => .inr (.inl j))
  rintro ((i|e)|(j|e)) t <;> simp [endWire, pickRight]

theorem extLeft_nodup : (G.extLeft v).Nodup := (G.left_spec v).1

theorem extRight_nodup : (G.extRight v).Nodup := (G.right_spec v).1

@[simp] theorem mem_extLeft (i : slots a) : i ∈ G.extLeft v ↔ Packing.portEnd G (.inl i) = v :=
  (G.left_spec v).2 i

@[simp] theorem mem_extRight (j : slots b) : j ∈ G.extRight v ↔ Packing.portEnd G (.inr j) = v :=
  (G.right_spec v).2 j

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-! # Reading a table from local labels and its two exterior strings -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Transcript

variable {F α : Type} {a b : Wire}

/-- A tagged position reads an internal bit. An untagged position
consumes the next exterior bit on its side. -/
def restore (x : α → Bool) : List (Bool × Option α) → List Bool → List Bool → List Bool
  | [], _, _ => []
  | (_, some i) :: ps, l, r => x i :: restore x ps l r
  | (false, none) :: ps, l, r => l.headD false :: restore x ps l.tail r
  | (true, none) :: ps, l, r => r.headD false :: restore x ps l r.tail

def fromList (T : Table F) (l : List Bool) :=
  sample T (fun i => (l[(positions (.pair T.1 T.2.1) i).val]?).getD false)

variable (G : Diagram F a b) (v : G.V)

theorem exterior_side (i : Fin (G.arity v)) {k : slots a ⊕ slots b}
    (he : G.wireAt v i = .inl (.inr k)) : (G.peer v i).1 = k.isRight := by
  rw [peer_side]
  rw [wireAt_eq] at he
  generalize G.endAt ⟨v, i⟩ = j at he ⊢
  rcases j with (u|e)|(t|e) <;> cases he <;> rfl

theorem vertex_restore (p : Fin (G.arity v) → Bool × Option α) (x : α → Bool)
    (s : Val a) (t : Val b) (z : G.E → Bool)
    (hp : ∀ i e, G.wireAt v i = .inr e → ∃ j, (p i).2 = some j ∧ z e = x j)
    (hl : ∀ i k, G.wireAt v i = .inl (.inr k) → p i = (k.isRight, none)) :
    G.vertex s t z v = fromList (G.table v) (restore x (List.ofFn p)
      ((G.extLeft v).map (bits a s)) ((G.extRight v).map (bits b t))) := by
  let read i := Sum.elim (exterior s t) z (G.wireAt v i)
  have go (l : List (Fin (G.arity v))) :
      restore x (l.map p) (((l.map (G.wireAt v)).filterMap pickLeft).map (bits a s))
        (((l.map (G.wireAt v)).filterMap pickRight).map (bits b t)) = l.map read := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      cases he : G.wireAt v i with
      | inl k =>
        rcases k with c | (u | w)
        · rw [wireAt_eq] at he
          generalize G.endAt ⟨v, i⟩ = j at he
          rcases j with (u|e)|(t|e) <;> cases he
        · simp [he, hl i _ he, restore, read, exterior, pickLeft, pickRight, -List.filterMap_map]
          exact ih
        · simp [he, hl i _ he, restore, read, exterior, pickLeft, pickRight, -List.filterMap_map]
          exact ih
      | inr e =>
        obtain ⟨j, hj, hz⟩ := hp i e he
        obtain ⟨d, hd⟩ : ∃ d, p i = (d, some j) := ⟨_, Prod.ext rfl hj⟩
        simp [he, hd, restore, read, hz, pickLeft, pickRight, -List.filterMap_map]
        exact ih
  have hr : restore x (List.ofFn p) ((G.extLeft v).map (bits a s))
      ((G.extRight v).map (bits b t)) = List.ofFn read := by
    simpa only [extLeft, extRight, List.ofFn_eq_map] using go (List.finRange _)
  rw [hr, ← sample_wires, fromList]
  apply congrArg
  funext i
  let ord : Ports (G.table v) ≃ Fin (G.arity v) := positions (.pair (G.table v).1 (G.table v).2.1)
  change _ = ((List.ofFn read)[(ord i).val]?).getD false
  simp only [List.getElem?_ofFn, dite_eq_left (ord i).isLt, Option.getD_some]
  change _ = Sum.elim (exterior s t) z (wires G v (ord.symm (ord i)))
  rw [Equiv.symm_apply_apply]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

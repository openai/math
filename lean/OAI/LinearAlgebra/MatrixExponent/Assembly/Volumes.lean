import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Assembly.Fragments
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.PortRelay
import OAI.LinearAlgebra.MatrixExponent.Assembly.RetagStore

/-!
# Joining a controller to its data path

The controller may have a weighted sum of possible outputs. Contract
only its command block against the transfer operation. New metadata
and transferred payload remain available for the next stage.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Kernel

open Coloring
open scoped Classical
variable {F : Type} [Field F] {u m n : ℕ} {L : Set (Table F)}
  {X Y C A B : Format}

/-- Feed the command block across, without copying either payload. -/
theorem with_channels [Fintype C.obj] {f : X.obj → (Y.pair C).obj → F}
    {g : (C.pair A).obj → B.obj → F} (hf : Kernel F u L X (.pair Y C) f n)
    (hg : Kernel F u L (.pair C A) B g m) :
    Kernel F u L (.pair X A) (.pair Y B)
      (fun x y => ∑ t, f x.1 (y.1, t) * g (t, x.2) y.2) (n + m) := by
  let a := word A.width
  let b := word B.width
  let c := word C.width
  let x := word X.width
  let y := word Y.width
  obtain ⟨s, hs, hf⟩ := hf x (.pair y c) (names X) ((names Y).sumCongr (names C))
  obtain ⟨t, ht, hg⟩ := hg (.pair c a) b ((names C).sumCongr (names A)) (names B)
  let pre := (Rewire.assoc x a c).comp ((Rewire.id x).par (Rewire.swap a c))
  let post := ((Rewire.assoc y b c).comp ((Rewire.id y).par (Rewire.swap b c))).comp
    (Rewire.assoc' y c b)
  have h := (((hf.par hg).pre pre).post post).trace
  apply of_layout (a := .pair x a) (b := .pair y b) ((names X).sumCongr (names A))
    ((names Y).sumCongr (names B))
  refine ⟨s + t, Nat.add_le_add hs ht, ?_⟩
  convert h using 1
  funext i j
  exact ((view C (names C)).sum_comp (fun w =>
    f (view X (names X) i.1) (view Y (names Y) j.1, w) *
      g (w, view A (names A) i.2) (view B (names B) j.2))).symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.Kernel
end

/-!
# Computing loads from local span widths

No exterior bit identifier or global neighbor name enters a count.
The two ends of a loop both contribute to the internal degree.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing
open scoped Classical

variable {F T : Type} {m d k e : ℕ}

def Pattern.volume (P : Pattern F d k e) (inside : Bool) :=
  ∑ i, if (P.peer 0 i).isSome = inside then P.width 0 i else 0

namespace Scheme
variable (S : Scheme F) (r : S.format.obj)

private theorem by_span (v : B S.m) (c : B S.h) (inside : Bool) :
    ∑ q : S.Pin r, (if q.1.1 = (v, c, 0) ∧ (S.peer r q.1).isSome = inside then 1 else 0) =
      (S.decode ((r v).2 c)).volume inside := by
  change (∑ q : Σ p : S.Span, Fin (S.width r p), _) = _
  rw [Fintype.sum_sigma]
  change (∑ p : S.Span, ∑ _ : Fin (S.width r p),
    if p.1 = (v, c, 0) ∧ (S.peer r p).isSome = inside then (1 : ℕ) else 0) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single ((v, c, 0) : S.Vtx)]
  · unfold Pattern.volume
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [peer, Option.isSome_map, true_and]
    rfl
  · intro i hi
    simp [hi]

namespace Posting
variable [Field F] {S r} {x y : Wire} {L : Fringe x y T} {u h : ℕ}
  {G : HostNet F L h u} (p : S.Posting r G) (v : G.V × Cell h)

def atBlock := S.decode ((r (p.host v.1)).2 (p.block v.2))

private theorem end_at (t : G.diagram.End) :
    (p.toSeating.ends t).1.1 = (p.host v.1, p.block v.2, 0) ↔ G.units.place (G.diagram.station t) = v := by
  obtain ⟨⟨w, i⟩, rfl⟩ := G.diagram.portEquiv.surjective t
  rw [p.toSeating.ends_at, Diagram.station_port]
  change p.vertex w = _ ↔ _
  rw [p.vertex_eq]
  simp only [Prod.mk.injEq, p.host.injective.eq_iff, p.block.injective.eq_iff, and_true]
  exact Prod.ext_iff.symm

private theorem tabs (i : G.diagram.E) :
    (S.peer r (p.toSeating.ends (.inl (.inr i))).1).isSome = true ∧
    (S.peer r (p.toSeating.ends (.inr (.inr i))).1).isSome = true := by
  rw [(p.internal i).1, (p.proper _ _ (p.internal i).1).1]
  exact ⟨rfl, rfl⟩

theorem internal_volume : (p.atBlock v).volume true = degree G.pair v * u := by
  unfold atBlock
  rw [← S.by_span r, ← p.toSeating.ends.sum_comp]
  simp only [Fintype.sum_sum_type, p.input, p.output, (p.tabs _).1, (p.tabs _).2, Option.isSome_none,
    Bool.false_eq_true, and_false, ite_false, Finset.sum_const_zero, zero_add, and_true, p.end_at]
  rw [← degree_bundle G.pair u v, degree_sum, ← Finset.sum_add_distrib]
  refine Fintype.sum_equiv G.units.bits _ _ fun i => ?_
  change (if G.units.place (G.diagram.source i) = v then 1 else 0) +
    (if G.units.place (G.diagram.target i) = v then 1 else 0) = _
  rw [G.units.left, G.units.right]
  unfold arityCost HostNet.pair
  congr

theorem exterior_volume : (p.atBlock v).volume false = G.tetherLoad v := by
  unfold atBlock
  rw [← S.by_span r, ← p.toSeating.ends.sum_comp]
  simp only [Fintype.sum_sum_type, p.input, p.output, (p.tabs _).1, (p.tabs _).2, Option.isSome_none,
    Bool.true_eq_false, and_false, ite_false, Finset.sum_const_zero, add_zero, and_true, p.end_at]
  unfold HostNet.tetherLoad Packing.exterior
  simp only [Fintype.card_subtype, Finset.card_filter]
  congr

end Posting
end Scheme
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# A weighted stage controller and an independent payload transfer

The controller never reads exterior bits. It writes the new state
and commands, charges the scalar factors, and rejects spare selector
words. Only legal commands need to specify a transfer.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Encoding
open Coloring Transcript
open scoped Classical

universe v
variable {F : Type} [Field F] {x y : Wire} {I J : Type v}
  {G : I → Diagram F x y} {H : J → Diagram F x y}
  (E : Encoding G) (D : Encoding H) {C T : Format} {u m n : ℕ} {L : Set (Table F)}

abbrev info (i : I) : E.control.obj := (E.rows i, E.data i)

def body (i : I) (a : Val x) (b : Val y) : E.payload.obj := (E.frame i a b).2

variable (R : Selected E.snapshot D.snapshot C)

/-- A shared port between the controller and payload check carries
exactly one command record per branch. -/
theorem transfer (hu : 3 ≤ u) (cmd : ∀ i, R.choice i → T.obj)
    {f : (E.control.pair C).obj → (D.control.pair T).obj → F}
    (hk : Kernel F u L (.pair E.control C) (.pair D.control T) f m)
    (he : ∀ i c y, f (E.info i, c) y = ((R.index i).read c).elim 0 fun j =>
      if (D.info (R.next i j), cmd i j) = y then R.scalar i j else 0)
    {g : (T.pair E.payload).obj → D.payload.obj → F}
    (hg : Kernel F u L (.pair T E.payload) D.payload g n)
    (hv : ∀ i j a b y, g (cmd i j, E.body i a b) y =
      if D.body (R.next i j) a b = y then 1 else 0) :
    Transforms F u L E.snapshot D.snapshot (m + 4 * C.width + n) := by
  let _ := Fintype.ofFinite C.obj
  let _ := Fintype.ofFinite T.obj
  have h := (Kernel.sum_hidden hu hk).with_channels hg
  refine ⟨_, h, fun i => ⟨R.choice i, inferInstance, R.next i, R.scalar i, R.expands i, ?_⟩⟩
  rintro a b ⟨z, w⟩
  change I at i
  let _ := R.finite i
  change (∑ t, (∑ c, f (E.info i, c) (z, t)) * g (t, E.body i a b) w) = _
  have hs (t : T.obj) : (∑ c, f (E.info i, c) (z, t)) =
      ∑ j, if (D.info (R.next i j), cmd i j) = (z, t) then R.scalar i j else 0 :=
    (Finset.sum_congr rfl fun c _ => he i c (z, t)).trans ((R.index i).sum _)
  simp only [hs, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = @ite F ((D.info (R.next i j), D.body (R.next i j) a b) = (z, w))
    (Classical.propDecidable _) (R.scalar i j) 0
  by_cases e : D.info (R.next i j) = z
  · simp only [Prod.mk.injEq, e, true_and, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    rw [hv i j a b w, mul_ite, mul_one, mul_zero]
  · simp only [Prod.mk.injEq, e, false_and, ite_false, zero_mul, Finset.sum_const_zero]

/-- A partially specified computation is enough. On a rejected selector
there is no constraint on its output, since its weight is zero. -/
theorem transfer_of_computes (hu : 3 ≤ u) (cmd : ∀ i, R.choice i → T.obj)
    (out : I × C.obj → (D.control.pair T).obj)
    (ho : ∀ i j, out (i, (R.index i).write j) = (D.info (R.next i j), cmd i j))
    (h : Computes F u L (.pair E.control C) (.pair D.control T)
      (fun z => (E.info z.1, z.2)) out (fun z => ((R.index z.1).read z.2).elim 0 (R.scalar z.1)) m)
    {g : (T.pair E.payload).obj → D.payload.obj → F}
    (hg : Kernel F u L (.pair T E.payload) D.payload g n)
    (hv : ∀ i j a b y, g (cmd i j, E.body i a b) y =
      if D.body (R.next i j) a b = y then 1 else 0) :
    Transforms F u L E.snapshot D.snapshot (m + 4 * C.width + n) := by
  obtain ⟨f, hf, he⟩ := h
  refine E.transfer D R hu cmd hf ?_ hg hv
  intro i c y
  have h := he (i, c) y
  cases e : (R.index i).read c with
  | none => simp only [e, Option.elim_none, ite_self] at h ⊢; exact h
  | some j =>
    have ho' := ho i j
    rw [← ((R.index i).valid _ _).mp e] at ho'
    simp only [ho', e, Option.elim_some] at h
    exact h

end OAI.LinearAlgebra.MatrixExponent.Assembly.Encoding
end

/-!
# A weighted scalar-withdrawal stage

One common short table is used at every occurrence. Physical labels,
the supplemental record, and all external bits pass through unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

universe v
variable {F : Type} [Field F] {x y : Wire} {I : Type v} {u n : ℕ} {L : Set (Table F)}

theorem Transforms.of_action {X Y : Snapshot.{v} F x y} (q : X.state → Y.state)
    (c : X.state → F) (f : X.port.obj → Y.port.obj) (w : X.port.obj → F)
    (h : Action F u L X.port Y.port f w n)
    (he : ∀ i a b, X.eval i a b = c i * Y.eval (q i) a b)
    (hf : ∀ i a b, f (X.encode i a b) = Y.encode (q i) a b)
    (hw : ∀ i a b, w (X.encode i a b) = c i) : Transforms F u L X Y n := by
  refine ⟨_, h, fun i => ⟨Unit, inferInstance, fun _ => q i, fun _ => c i, ?_, ?_⟩⟩
  · intro a b
    simp only [he, Fintype.sum_unique]
  · intro a b t
    simp only [hf, hw, Fintype.sum_unique]

namespace Encoding
variable {G : I → Diagram F x y} (E : Encoding G)

abbrev sweep : Encoding (fun i => (G i).sweep) :=
  { E with scheme := E.scheme.sweep, presents := fun i => (E.presents i).sweep }

def sweepTable := weightTable (A := .addr E.scheme.ℓ) (D := .addr E.scheme.ℓ) id E.scheme.scalar

def sweepCost := updateCost E.scheme.m E.scheme.d E.scheme.h (.addr E.scheme.ℓ) (.addr E.scheme.ℓ) +
  4 * E.extra.width + 4 * E.payload.width

theorem sweep_stage (hu : 3 ≤ u) (hw : 2 * E.scheme.ℓ ≤ u) (hl : E.sweepTable ∈ L) :
    Transforms F u L E.snapshot E.sweep.snapshot E.sweepCost := by
  let A := Format.addr E.scheme.ℓ
  have h := update (m := E.scheme.m) (d := E.scheme.d) (h := E.scheme.h)
    (A := A) (D := A) id E.scheme.scalar hu (by simpa [A, two_mul] using hw) hl
  have keep (X : Format) := Action.of_map (Map.circuit (L := L) hu (Circuit.id F X))
  have k := (h.par (keep E.extra)).par (keep E.payload)
  simp only [mul_one] at k
  refine Transforms.of_action (X := E.snapshot) (Y := E.sweep.snapshot) (fun i => i)
    (fun i => Fmt.weight E.scheme.scalar (E.rows i)) _ _ k ?_ ?_ ?_
  · exact fun i a b => (E.presents i).sweep_eval a b
  · intro i a b
    rfl
  · exact fun _ _ _ => rfl

end Encoding
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # A cut through a bundle exposes its full width -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj} {x y : Wire}
  {G : Diagram F x y} (p : S.Presentation r G) (Z : Freeze G) (live : B S.m → Bool)
  (hl : ∀ v, live (p.vertex v).1 = true ↔ ¬Z.frozen v)

theorem freeze_borderWidth {u : ℕ} (hw : p.Uniform u) (j : (p.freeze Z live hl).BorderSpan) :
    (p.freeze Z live hl).borderWidth j = u := by
  let q := p.freeze Z live hl
  let b : q.BorderBit := ⟨j, ⟨0, j.property.1⟩⟩
  let i := q.exteriorBits b
  have ht : S.width r (p.toSeating.ends (fullEnd Z (boundaryEnd Z.core i))).1 = u := by
    cases i with
    | inl t => exact p.wirePin_width hw (Z.input t).val false
    | inr t => exact p.wirePin_width hw (Z.output t).val true
  have he : (p.toSeating.ends (fullEnd Z (boundaryEnd Z.core i))).1 = (q.vertex j.val.1, j.val.2) :=
    (p.span_full Z live hl _).symm.trans (congrArg Sigma.fst (q.border_pin b))
  rw [he] at ht
  unfold borderWidth
  have ha : live ((p.freeze Z live hl).vertex j.val.1).1 = true := (hl _).mpr j.val.1.property
  rw [S.width_cut, ite_eq_left ha]
  exact ht

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-!
# Payload and header costs

The field extension is used for station weights. A tagged permutation
over the ground field already gives the required graph over the extension.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring Transcript
open scoped Classical
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem tag_map {j v m : ℕ} (ht : Radix.Tag F j v m) : Radix.Tag K j v m := by
  unfold Radix.Tag Tagged.tag Tagged.permuted at ht ⊢
  simpa only [apply_ite (algebraMap F K), map_one, map_zero] using ht.map (algebraMap F K)

theorem wide_cost (h : Radix.WideTag F) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n j v : ℕ, 1 ≤ j → j ≤ n → n ^ A ≤ v →
      ∃ m ≤ ⌈C * (n : ℝ) ^ ζ⌉₊*(2 ^ j * v), Radix.Tag F j v m := by
  obtain ⟨A, _, C, ht⟩ := h ζ hζ
  refine ⟨A, max C 0, le_max_right _ _, fun n j v hj hle hv => ?_⟩
  obtain ⟨m, hm, hb⟩ := ht j v hj ((Nat.pow_le_pow_left hle _).trans hv)
  refine ⟨m, ?_, hm⟩
  have h' : (m : ℝ) ≤ ⌈max C 0 * (n : ℝ) ^ ζ⌉₊ * ((2 : ℝ) ^ j * v) := by
    calc
      _ ≤ (C * (j : ℝ) ^ ζ) * ((2 : ℝ) ^ j * v) := by linarith only [hb]
      _ ≤ (max C 0 * (n : ℝ) ^ ζ) * ((2 : ℝ) ^ j * v) := by gcongr; exact le_max_left _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  exact_mod_cast h'

variable (m V k m' V' k' d : ℕ)

abbrev payloadChannels := (payloadBank m V k m' V' k').channels (max k k') d

theorem bank_capacity : (payloadBank m V k m' V' k').capacity =
    (Fmt.payload m V k).width + (Fmt.payload m' V' k').width := by
  unfold Bank.capacity payloadBank
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fmt.payload, Format.width, Fintype.card_sigma, Fintype.card_fin]
  rfl

theorem bank_slots : Fintype.card (payloadBank m V k m' V' k').Slot ≤
    (max k k' + 1) * (2 ^ m + 2 ^ m') := by
  change Fintype.card (Slot (2 ^ m) V k ⊕ Slot (2 ^ m') V' k') ≤ _
  rw [Fintype.card_sum, mul_add]
  refine Nat.add_le_add ((Transcript.card_slots ..).trans ?_) ((Transcript.card_slots ..).trans ?_)
  · exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (le_max_left _ _) _)
  · exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (le_max_right _ _) _)

private theorem budget {q a b H V d T v : ℕ} (ha : a ≤ 2 * (q + 1) * V) (hb : b ≤ (q + 1) * H) :
    20000 * T * (1 + a + (q + 1) * (10 * a + 4 * d * b * v)) ≤ 500000 * T * (q + 1) ^ 2 * (1 + V + d * H * v) := by
  calc
    _ ≤ 20000 * T * (1 + 2 * (q + 1) * V + (q + 1) * (10 * (2 * (q + 1) * V) + 4 * d * ((q + 1) * H) * v)) := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem payload_kernel {L : Set (Table K)} {u H W A : ℕ}
    (hu : 3 ≤ u) (hn : d * ((max k k' + 1) * (2 ^ m + 2 ^ m')) < 2 ^ H)
    (ht : ∀ j v, 1 ≤ j → j ≤ H → H ^ A ≤ v → ∃ s ≤ W * (2 ^ j * v), Radix.Tag F j v s) :
    let S := payloadChannels m V k m' V' k' d
    let ℓ := max k k'
    Kernel K u L (S.control.pair (Fmt.payload m V k)) (Fmt.payload m' V' k') (S.kernel K)
      (500000 * ((102 + ℓ) ^ 8 + W) * (ℓ + 1) ^ 2 * (1 + (V + V') + d * (2 ^ m + 2 ^ m') * (H ^ A + H + 1))) := by
  intro S ℓ
  let P := payloadBank m V k m' V' k'
  let T := (102 + ℓ) ^ 8 + W
  let v := H ^ A + H + 1
  have hdepth (i : P.Slot) : P.depth i ≤ ℓ := by
    rcases i with i | i
    · exact (Nat.lt_succ_iff.mp i.1.isLt).trans (le_max_left _ _)
    · exact (Nat.lt_succ_iff.mp i.1.isLt).trans (le_max_right _ _)
  have hs := bank_slots m V k m' V' k'
  have hw := P.realize (F := K) (L := L) ℓ d H T v hu hdepth
    ((Nat.mul_le_mul_left d hs).trans_lt hn)
    (Nat.le_add_right _ _) (by unfold v; omega) (by
      intro a b ha hb hbig
      obtain ⟨t, he, ht⟩ := ht a b ha hb (le_trans (by unfold v; omega) hbig)
      exact ⟨t, he.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)), tag_map ht⟩)
  have hcap : P.capacity ≤ 2 * (ℓ + 1) * (V + V') := by
    rw [bank_capacity]
    calc
      _ ≤ (k + 1) * (2 * V) + (k' + 1) * (2 * V') := Nat.add_le_add (Fmt.width_payload ..) (Fmt.width_payload ..)
      _ ≤ (ℓ + 1) * (2 * V) + (ℓ + 1) * (2 * V') := by gcongr <;> unfold ℓ <;> omega
      _ = _ := by ring
  intro a b i j
  obtain ⟨s, hs', hnet⟩ := hw a b i j
  refine ⟨s, hs'.trans ?_, hnet⟩
  rw [add_assoc 1, ← bank_capacity]
  exact budget (q := ℓ) (T := T) (v := v) (d := d) hcap hs

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Exterior transfer between snapshots

An exterior position has a name independent of the snapshot. The
two boundary bijections therefore determine a permutation between
the occupied prefixes of the banks.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring
open scoped Classical

namespace Payload
variable {a b c a' b' c' d : ℕ} {x : Payload a b c} {y : Payload a' b' c'}

/-- The two host lists may repeat entries. Use the first matching
slot for each contact. -/
def contacts (f : y.Bit ↪ x.Bit) (left : B a → Fin d → B a') (right : B a' → Fin d → B a)
    (hl : ∀ i, ∃ k, left (f i).1 k = i.1) (hr : ∀ i, ∃ k, right i.1 k = (f i).1) :
    Contacts f d := by
  let E := {e : B a × B a' // ∃ i, ((f i).1, i.1) = e}
  have hs (e : E) : ∃ k, left e.val.1 k = e.val.2 := by
    obtain ⟨i, h⟩ := e.property
    rw [← h]; exact hl i
  have ht (e : E) : ∃ k, right e.val.2 k = e.val.1 := by
    obtain ⟨i, h⟩ := e.property
    rw [← h]; exact hr i
  let l (e : E) := (Finset.univ.filter (fun k => left e.val.1 k = e.val.2)).min'
    (Finset.filter_nonempty_iff.mpr (by simpa using hs e))
  let r (e : E) := (Finset.univ.filter (fun k => right e.val.2 k = e.val.1)).min'
    (Finset.filter_nonempty_iff.mpr (by simpa using ht e))
  have h₁ (e : E) : left e.val.1 (l e) = e.val.2 :=
    (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun k => left e.val.1 k = e.val.2)) _)).2
  have h₂ (e : E) : right e.val.2 (r e) = e.val.1 :=
    (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun k => right e.val.2 k = e.val.1)) _)).2
  refine { E := E
           src := ⟨fun e => (e.val.1, l e), ?_⟩
           dst := ⟨fun e => (e.val.2, r e), ?_⟩
           edge := fun i => ⟨((f i).1, i.1), i, rfl⟩
           from_host := fun _ => rfl
           to_host := fun _ => rfl
           no_repeat := f.injective }
  · intro u v he
    obtain ⟨ha, hb⟩ := Prod.mk.inj he
    exact Subtype.ext (Prod.ext ha ((h₁ u).symm.trans ((congrArg₂ left ha hb).trans (h₁ v))))
  · intro u v he
    obtain ⟨ha, hb⟩ := Prod.mk.inj he
    exact Subtype.ext (Prod.ext ((h₂ u).symm.trans ((congrArg₂ right ha hb).trans (h₂ v))) ha)

end Payload

namespace Encoding

universe v
variable {F : Type} [Field F] {x y : Wire} {I J : Type v}
  {G : I → Diagram F x y} {H : J → Diagram F x y}
  (E : Encoding G) (D : Encoding H)

def relabel (i : I) (j : J) : D.scheme.exposed (D.rows j) ≃ E.scheme.exposed (E.rows i) :=
  (D.presents j).boundary.symm.trans (E.presents i).boundary

def sources (i : I) (j : J) : (D.scheme.payload (D.rows j) (D.fits j)).Bit ≃
    (E.scheme.payload (E.rows i) (E.fits i)).Bit :=
  (D.scheme.index _ _).symm.trans ((E.relabel D i j).trans (E.scheme.index _ _))

abbrev channels (d : ℕ) :=
  payloadChannels E.scheme.m E.volume E.height D.scheme.m D.volume D.height d

/-- Check the payload independently of the controller's branch weights. -/
theorem routed {d : ℕ} (i : I) (j : J) (M : Payload.Contacts (E.sources D i j) d)
    (a : Val x) (b : Val y) (z : D.payload.obj) :
    (E.channels D d).kernel F (M.traffic.links.plan.control, E.body i a b) z =
      if D.body j a b = z then 1 else 0 := by
  let f := E.relabel D i j
  have he : (E.presents i).exterior a b ∘ f = (D.presents j).exterior a b := by
    funext p
    obtain ⟨u, rfl⟩ := (D.presents j).boundary.surjective p
    simp only [Function.comp_apply, f, relabel, Equiv.trans_apply, Equiv.symm_apply_apply,
      Scheme.Presentation.exterior_boundary]
  have hc := Scheme.transfer_kernel E.scheme D.scheme (E.fits i) (D.fits j) f M
    ((E.presents i).exterior a b) z
  rw [he] at hc
  change _ = if D.scheme.store _ _ _ = z then 1 else 0
  refine hc.trans ?_
  exact if_congr eq_comm rfl rfl

end Encoding
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Contiguous spans in one channel bank

The weighted prefix includes exactly the earlier order indices in the
same contact. Equal order indices are never counted against one
another, so inactive rows can safely duplicate any index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring Finset

variable {w p n : ℕ}

/-- Fields are contact, length, order and bank start. -/
abbrev Entry (w p n : ℕ) := Format.pair (.addr p) (.pair (.addr w) (.pair (.addr n) (.addr w)))
abbrev Input (w p n : ℕ) := Format.vec n (Entry w p n)

def pack (x : (Input w p n).obj) : (Fragments.Input w p n).obj :=
  (fun c => ∑ j with (x j).1 = c, (x j).2.1,
   fun i => ((x i).1, (∑ j with (x j).1 = (x i).1 ∧ (x j).2.2.1 < (x i).2.2.1, (x j).2.1),
      (x i).2.1, (x i).2.2.2))

def Fits (x : (Input w p n).obj) : Prop :=
  ∀ c, (∑ i with (x i).1 = c, (x i).2.1.val) < 2 ^ w

theorem val_sum {I : Type} (S : Finset I) (y : I → B w)
    (h : (∑ i ∈ S, (y i).val) < 2 ^ w) :
    (∑ i ∈ S, y i).val = ∑ i ∈ S, (y i).val := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [sum_insert hi] at h
    rw [sum_insert hi, sum_insert hi, Fin.val_add, ih (by omega), Nat.mod_eq_of_lt h]

theorem lengths (x : (Input w p n).obj) (h : Fits x) (c : B p) :
    ((pack x).1 c).val = ∑ j with (x j).1 = c, (x j).2.1.val := val_sum _ _ (h c)

theorem starts (x : (Input w p n).obj) (h : Fits x) (i : B n) :
    ((pack x).2 i).2.1.val = ∑ j with (x j).1 = (x i).1 ∧ (x j).2.2.1 < (x i).2.2.1,
      (x j).2.1.val := by
  apply val_sum
  exact (sum_le_sum_of_subset (by intro j hj; simpa using (mem_filter.mp hj).2.1)).trans_lt (h (x i).1)

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! Compute strict weighted prefixes by looking up the start of the sorted run. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring Finset
variable {w k n : ℕ}

def earlier (f : B n → B k) (x : B n → B w) (i : B n) := ∑ j with f j < f i, x j

private theorem earlier_sorted (f : B n → B k) (x : B n → B w) (i : B n) :
    earlier f x i = ∑ j with j < leader (f ∘ order f) ((order f).symm i), x (order f j) := by
  have hm := order_mono f
  let j := leader (f ∘ order f) ((order f).symm i)
  obtain ⟨he, hl⟩ := leader_spec _ hm ((order f).symm i)
  have hj : f (order f j) = f i := by simpa using he
  have key (t : B n) : f (order f t) < f i ↔ t < j := by
    constructor
    · exact fun h => lt_of_not_ge fun hu => h.not_ge (hj ▸ hm hu)
    · intro h
      refine lt_of_le_of_ne ((hm h.le).trans_eq hj) (fun eq => h.not_ge (hl t ?_))
      simpa using eq
  unfold earlier
  simp only [sum_filter]
  rw [← Equiv.sum_comp (order f) (fun t => if f t < f i then x t else 0)]
  simp only [key, j]

variable (F : Type) [Field F] {t : ℕ}

theorem cheap_prefix (hw : w ≤ t) :
    Cheap F n t (Column n w) (Column n w) (fun x j => ∑ i with i < j, x i) 5 := by
  refine ⟨_, BatchDescent.prefix_sum F n w, ?_⟩
  have he : 2 * w + 100000 * (1 + w) ≤ (100 + t) ^ 5 := by ring_nf; omega
  simp only [Column, Format.width_vec, Format.width_addr]
  linarith only [Nat.mul_le_mul_left (2 ^ n) he]

private abbrev Columns (n k w : ℕ) := Format.pair (Column n k) (Column n w)

theorem cheap_earlier (h : n + k + w ≤ t) :
    Cheap F n t (Columns n k w) (Column n w) (fun z => earlier z.1 z.2) 110 := by
  have hk : n + k ≤ t := by omega
  have hn : n ≤ t := by omega
  have hw : w ≤ t := by omega
  have hi : (Columns n k w).width ≤ 2 ^ n * (100 + t) ^ 1 := by
    simp only [Columns, Column, Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have z := Cheap.id F hi
  have σ := z.fst.comp ((cheap_order F n k).widen hk)
  have read := Cheap.lookup F n t (.addr w) hn (by simpa using hw)
  have weights := (z.snd.pair σ).comp read
  have scan := weights.comp (cheap_prefix F hw)
  have l := z.fst.comp ((cheap_sorted_leader F n k).widen hk)
  have inv := z.fst.comp ((cheap_inverse_order F n k).widen hk)
  have key := (l.pair inv).comp (Cheap.lookup F n t (.addr n) hn (by simpa using hn))
  have net := ((scan.pair key).comp read).mono (d := 110) (by decide)
  convert net using 1
  funext z i
  exact earlier_sorted z.1 z.2 i

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-!
# Channel starts

Subtract the prefix in contact order from the prefix in lexicographic
(contact, position) order. Modular arithmetic suffices even if the sum
across different channels overflows.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan

open Coloring Finset
variable {w p n t : ℕ}

private def joint (x : (Entry w p n).obj) : B (p + n) :=
  (Match.rowIndex p n).symm (x.1, x.2.2.1)

private theorem joint_lt (x y : (Entry w p n).obj) :
    joint x < joint y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2.2.1 < y.2.2.1) := by
  have h (x y : (Entry w p n).obj) (h : x.1 < y.1) : joint x < joint y := by
    change x.2.2.1.val + 2 ^ n * x.1.val < y.2.2.1.val + 2 ^ n * y.1.val
    have he := Nat.mul_le_mul_left (2 ^ n) (show x.1.val + 1 ≤ y.1.val from h)
    rw [mul_add, mul_one] at he
    have hx := x.2.2.1.isLt
    omega
  rcases lt_trichotomy x.1 y.1 with he | he | he
  · simp [he, h x y he]
  · change (x.2.2.1.val + 2 ^ n * x.1.val < y.2.2.1.val + 2 ^ n * y.1.val) ↔ _
    rw [he]
    simp
  · simp [he.not_gt, he.ne', (h y x he).not_gt]

private theorem start_eq (x : (Input w p n).obj) (i : B n) :
    ((pack x).2 i).2.1 =
      earlier (joint ∘ x) (fun j => (x j).2.1) i -
        earlier (fun j => (x j).1) (fun j => (x j).2.1) i := by
  simp only [pack, earlier, sum_filter, Function.comp_apply, ← sum_sub_distrib, joint_lt]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : (x j).1 < (x i).1
  · simp [h, h.ne]
  · simp [h]

variable (F : Type) [Field F]

theorem entry_width (h : 2 * n + p + w ≤ t) : (Entry w p n).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by
  simp [Entry]; ring_nf; omega

private theorem cheap_joint (h : 2 * n + p + w ≤ t) :
    Cheap F 0 t (Entry w p n) (.addr (p + n)) joint 10 := by
  have x := Cheap.id F (entry_width h)
  have a : Cheap F 0 t (.pair (.addr p) (.addr n)) (.addr (p + n)) (Match.rowIndex p n).symm 2 := by
    refine ⟨_, Match.append_address F p n, ?_⟩
    simp; ring_nf; omega
  exact ((x.fst.pair x.snd.snd.fst).comp a).mono (by decide)

private theorem cheap_sub (h : w ≤ t) :
    Cheap F 0 t (.pair (.addr w) (.addr w)) (.addr w) (fun y => y.1 - y.2) 20 := by
  have x := Cheap.id F (show (Format.pair (.addr w) (.addr w)).width ≤ 2 ^ 0 * (100 + t) ^ 2 by
    simp; ring_nf; omega)
  have neg := x.snd.comp ((Intervals.cheap_neg F w).widen h)
  convert ((x.fst.pair neg).comp (Intervals.cheap_add F h)).mono (d := 20) (by decide) using 1
  funext y
  exact sub_eq_add_neg _ _

theorem cheap_fragments (h : 2 * n + p + w ≤ t) :
    Cheap F n t (Input w p n) (.vec n (Fragments.Entry w p)) (fun x => (pack x).2) 130 := by
  have x := Cheap.id F (entry_width h)
  have keys := Cheap.map _ (fun _ : B n => cheap_joint F h)
  have contacts := Cheap.map _ (fun _ : B n => x.fst)
  have weights := Cheap.map _ (fun _ : B n => x.snd.fst)
  have banks := Cheap.map _ (fun _ : B n => x.snd.snd.snd)
  have before := (keys.pair weights).comp (cheap_earlier F (show n + (p + n) + w ≤ t by omega))
  have base := (contacts.pair weights).comp (cheap_earlier F (show n + p + w ≤ t by omega))
  have sub := Cheap.map _ (fun _ : B n => cheap_sub F (show w ≤ t by omega))
  have start := (before.pair base).zip.comp sub
  have lenPtr := (weights.pair banks).zip
  have record := (contacts.pair (start.pair lenPtr).zip).zip
  convert record.mono (d := 130) (by decide) using 1
  funext x i
  exact Prod.ext rfl (Prod.ext (start_eq x i) rfl)

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! Generate the channel totals and contiguous fragment runs. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring Finset
variable (F : Type) [Field F] {w p n t : ℕ}

theorem cheap_sum (h : w ≤ t) :
    Cheap F n t (Column n w) (.addr w) (fun y => ∑ i, y i) 10 := by
  have ha : (Format.addr w).width ≤ 2 ^ n * (100 + t) ^ 1 := by
    rw [Format.width_addr, pow_one]
    exact le_trans (by omega) (Nat.le_mul_of_pos_left _ (by positivity))
  have get := Cheap.project F (A := Column n w) (D := .addr w) (f := fun y => y ⊤)
    (column_width n h) ha (fun j => (⊤, j)) (fun _ _ => rfl)
  have add := Peers.lift F (Intervals.cheap_add F h) (Nat.zero_le n)
  have total := (((cheap_prefix F h).comp get).pair get).comp add
  convert total.mono (d := 10) (by decide) using 1
  funext y
  change (∑ i, y i) = (∑ i with i < ⊤, y i) + y ⊤
  rw [show ({i : B n | i < ⊤} : Finset _) = univ.erase ⊤ by ext; simp [lt_top_iff_ne_top]]
  exact (sum_erase_add _ _ (mem_univ _)).symm

private theorem cheap_amount (h : 2 * n + p + w ≤ t) (a : B p) :
    Cheap F 0 t (Entry w p n) (.addr w) (fun x => if x.1 = a then x.2.1 else 0) 12 := by
  have hi := entry_width h
  have hp : (Format.addr p).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp; ring_nf; omega
  have hw : (Format.addr w).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp; ring_nf; omega
  have x := Cheap.id F hi
  have eq := (x.fst.pair (Cheap.const F hi hp a)).comp (cheap_eq F (show p ≤ t by omega))
  have args := (x.snd.fst.pair (Cheap.const F hi hw 0)).pair eq
  have net := args.comp ((cheap_select F w).widen (show w ≤ t by omega))
  convert net.mono (d := 12) (by decide) using 1
  funext z
  simp

private theorem cheap_lengths (h : 2 * n + p + w ≤ t) :
    Cheap F (n + p) t (Input w p n) (Column p w) (fun x => (pack x).1) 15 := by
  let A := Input w p n
  have one (a : B p) : Cheap F n t A (.addr w) (fun x => (pack x).1 a) 13 := by
    have f := (Cheap.map _ (fun _ : B n => cheap_amount F h a)).comp
      (cheap_sum F (show w ≤ t by omega))
    convert f.mono (d := 13) (by decide) using 1
    funext x
    simp only [pack, Function.comp_apply, sum_filter]
  let C := 2 ^ n * (100 + t) ^ 13
  have each (a : B p) : Circuit F A (.addr w) (fun x => (pack x).1 a) C := by
    obtain ⟨m, hm, hb⟩ := one a
    exact hm.mono (by unfold C; omega)
  let D := Format.vec p A
  have copy : Circuit F A D (fun x _ => x) (A.width + 2 * D.width) :=
    Circuit.project (fun i => i.2) (fun _ _ => rfl)
  have k := copy.comp (Circuit.map _ each)
  refine ⟨_, k, ?_⟩
  obtain ⟨m, _, hb⟩ := one 0
  change A.width + (Format.addr w).width + m ≤ C at hb
  have he := Nat.mul_le_mul_left (2 ^ p) hb
  have hc := Nat.le_mul_of_pos_left C (Nat.two_pow_pos p)
  have hu : 10 * (2 ^ p * C) ≤ 2 ^ (n + p) * (100 + t) ^ 15 := by
    rw [show 2 ^ (n + p) * (100 + t) ^ 15 = (2 ^ p * C) * (100 + t) ^ 2 by
      unfold C; rw [pow_add, show 15 = 13 + 2 from rfl, pow_add]; ac_rfl, mul_comm 10]
    exact Nat.mul_le_mul_left _ (by ring_nf; omega)
  change A.width + (Column p w).width + (A.width + 2 * D.width + 2 ^ p * C) ≤ _
  simp only [Column, D, Format.width_vec]
  linarith only [hu, hb, he, hc, Nat.zero_le (2 ^ p * m), Nat.zero_le (2 ^ p * (Format.addr w).width)]

theorem cheap (w p n : ℕ) :
    Cheap F (n + p) (2 * n + p + w) (Input w p n) (Fragments.Input w p n) pack 131 := by
  have h₁ := cheap_lengths F (le_rfl : 2 * n + p + w ≤ 2 * n + p + w)
  have h₂ := Peers.lift F (cheap_fragments F (le_rfl : 2 * n + p + w ≤ 2 * n + p + w)) (Nat.le_add_right n p)
  exact h₁.pair h₂

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! # Computing bank offsets and lengths from the ordered spans -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring Finset

abbrev header (w p n : ℕ) := Format.pair (.addr p) (.pair (.addr w) (.addr n))
abbrev entries (w p n : ℕ) := Format.vec n (header w p n)

variable {w p n : ℕ} (x : (entries w p n).obj)

def total := ∑ i, (x i).2.1

def offsets : (Input w p n).obj := fun i =>
  ((x i).1, (x i).2.1, (x i).2.2, ∑ j with j < i, (x j).2.1)

theorem total_val (hx : (∑ i, (x i).2.1.val) < 2 ^ w) :
    (total x).val = ∑ i, (x i).2.1.val := val_sum _ _ hx

theorem offset_val (hx : (∑ i, (x i).2.1.val) < 2 ^ w) (i : B n) :
    ((offsets x i).2.2.2).val = ∑ j with j < i, (x j).2.1.val :=
  val_sum _ _ ((sum_le_sum_of_subset (subset_univ _)).trans_lt hx)

abbrev Row (w p n : ℕ) := Format.pair (.addr w) (Fragments.Input w p n)

def compile : (Row w p n).obj := (total x, pack (offsets x))

variable (F : Type) [Field F]

theorem cheap_entries (w p n : ℕ) :
    Cheap F (n + p) (2 * n + p + w) (entries w p n) (Row w p n) compile 140 := by
  let t := 2 * n + p + w
  have ht : w ≤ t := Nat.le_add_left _ _
  have h₁ : (header w p n).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by
    simp only [header, Format.width_pair, Format.width_addr, pow_zero, one_mul]
    ring_nf
    omega
  have h₂ : (Format.pair (header w p n) (.addr w)).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by
    simp only [header, Format.width_pair, Format.width_addr, pow_zero, one_mul]
    ring_nf
    omega
  have h₃ : (entries w p n).width ≤ 2 ^ n * (100 + t) ^ 2 := by
    rw [entries, Format.width_vec]
    exact Nat.mul_le_mul_left _ (by simpa using h₁)
  have strip := Cheap.map _ (fun _ : B n => (Cheap.id F h₁).snd.fst)
  have size := strip.comp (cheap_sum F ht)
  have offsets' := strip.comp (cheap_prefix F ht)
  have rekey : Cheap F 0 t (.pair (header w p n) (.addr w)) (Entry w p n)
      (fun x => (x.1.1, x.1.2.1, x.1.2.2, x.2)) 3 := by
    let key : (Entry w p n).pins → (Format.pair (header w p n) (.addr w)).pins
      | .inl i => .inl (.inl i)
      | .inr (.inl i) => .inl (.inr (.inl i))
      | .inr (.inr (.inl i)) => .inl (.inr (.inr i))
      | .inr (.inr (.inr i)) => .inr i
    exact Cheap.project F h₂ (entry_width le_rfl) key (by rintro _ (i|i|i|i) <;> rfl)
  have h := (((Cheap.id F h₃).pair offsets').zip.comp (Cheap.map _ (fun _ => rekey)))
  have h' := (Peers.lift F h (Nat.le_add_right n p)).comp (cheap F w p n)
  exact ((Peers.lift F size (Nat.le_add_right n p)).pair h').mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! # Recording coincidences among paths from one host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
open Coloring
variable (F : Type) [Field F] {m q t : ℕ}

theorem cheap_equal (hm : m ≤ t) (hq : 2 ^ q ≤ t) :
    Cheap F m t (Rows m q) (.vec m (Format.vec q (.vec q .bit)))
      (fun a x i j => decide (a x i = a x j)) 25 := by
  have cols (i j : B q) := ((column F hm hq i).pair (column F hm hq j)).zip
  have test (i j : B q) := (cols i j).comp (Cheap.map _ (fun _ => cheap_eq F hm))
  have all := Cheap.share _ (fun i => Cheap.share _ (test i) hq) hq
  let X := Format.vec q (.vec q (.vec m .bit))
  let Y := Format.vec m (Format.vec q (.vec q .bit))
  have hb : Y.width ≤ 2 ^ m * (100 + t) ^ 2 := by
    simp only [Y, Format.width_vec]
    rw [Format.width_bit, mul_one]
    apply Nat.mul_le_mul_left
    nlinarith only [Nat.mul_le_mul hq hq]
  have hc : X.width = Y.width := by simp only [X, Y, Format.width_vec]; ring
  have copy : Cheap F m t X Y (fun a x i j => a i j x) 3 :=
    Cheap.project F (hc.le.trans hb) hb (fun z => (z.2.1, z.2.2.1, z.1, z.2.2.2)) fun _ _ => rfl
  exact (all.comp copy).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
end

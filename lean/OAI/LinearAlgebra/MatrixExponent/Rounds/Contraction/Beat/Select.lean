import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat.HeaderCost
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Factor
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Apply
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.ShortNet
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat.Fanout
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Issue
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Label
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanSupplies
import OAI.LinearAlgebra.MatrixExponent.Packing.FieldLift
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Pass

/-! # Shared parameters of a contraction with its border attached -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Assembly.History
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F}
    (Q : Gadget F) (A : Attachment T) (L : BorderLimit F x y)
    (v : ℕ) (hv : 0 < v) (z Δ C B r : ℕ)

abbrev k := BatchDescent.Beat.k Δ
abbrev b := BatchDescent.Beat.b Q
abbrev gain := BatchDescent.Beat.gain Δ
def e := Nat.clog 2 (gain Δ * B)
def copies := B * gain Δ * B
def c := Nat.clog 2 (copies Δ B * z + 1)

abbrev meter := Template.Meter.bounded (c z Δ B) (1 / (L.denom : ℝ)) (1 / (2 : ℝ) ^ L.discount)

abbrev book (Q : Gadget F) (_A : Attachment T) (v : ℕ) (hv : 0 < v) (z B : ℕ) :=
  Book.make T.scheme Q v hv T.order (Finset.range (B * z + 1))
abbrev cap := (book Q A v hv z B).overhead (e Δ B) + 2 ^ (e Δ B) * T.scheme.ℓ
abbrev raw := T.after (T.scheme.h - r) Δ C (book Q A v hv z B) (e Δ B)
  (cap Q A v hv z Δ B) (meter L z Δ B)
abbrev next := (raw Q A L v hv z Δ C B r).sweep
abbrev slots := T.scheme.h - (T.scheme.h - r) + A.k
abbrev out := A.transport (next Q A L v hv z Δ C B r) (slots A r)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Separating short metadata costs from wide exterior transfers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Assembly.History Coloring
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {T : Template F}
    (Q : Gadget F) (A : Attachment T) (L : BorderLimit F x y)
    (v : ℕ) (hv : 0 < v) (z Δ C B r : ℕ) (p : Prices F)

local notation "a" => (T.scheme.h - r)
local notation "n" => (T.scheme.h - a)
local notation "m" => T.scheme.m
local notation "d" => T.scheme.d
local notation "Y" => next Q A L v hv z Δ C B r
local notation "M" => book Q A v hv z B
local notation "𝓔" => e Δ B
local notation "𝓒" => cap Q A v hv z Δ B
local notation "𝓚" => meter L z Δ B
local notation "q" => ((d + 1) * n)

abbrev target := A.shrink Y (slots A r) (copies Δ B)
abbrev input := A.format.pair (T.Candidate a (b Q))
abbrev headed := A.format.pair (T.Headed a (b Q) Δ C)
abbrev requests := A.Requests Y (slots A r) (d + 1)
def precision (T : Template F) (Δ C r : ℕ) :=
  let g := T.scheme.h - r
  T.size g + 2 ^ (Window.Tile.radius T.scheme.d + (T.scheme.h - g + 1)) + 2 ^ (T.degree g Δ C)

def prepareCost (Q : Gadget F) (T : Template F) (r : ℕ) (p : Prices F) :=
  let g := T.scheme.h - r
  let u := BatchDescent.Beat.parcel T r
  let v := BatchDescent.Beat.labels T r
  T.prepareCost g (b Q) u (p.fee (T.scheme.m + (T.scheme.d + 1) * (T.scheme.h - g)) u)
    v (p.fee (T.scheme.m + T.scheme.d) v)

def firstCost := 1000 * ((input Q A r).width + (headed Q A Δ C r).width) +
  prepareCost Q T r p + T.headedCost a (b Q) Δ C (BatchDescent.Beat.profile Q)
def secondCost :=
  let t := BatchDescent.Beat.walk Q T r
  A.groupedCost a (b Q) Δ C M 𝓔 𝓒 𝓚 t (p.fee (m + d) t) (precision T Δ C r)
def rebuildCost :=
  let u := 2 ^ d * m + 2 ^ T.scheme.h * A.ℓ
  let t := (Attachment.Inspect.Packet m d (d + 1) a (A.bundle Y (slots A r) (d + 1))).width
  A.rebuildCost Y (slots A r) (d + 1) u (p.fee (m + d) u) t (p.fee ((Y).scheme.m + (Y).scheme.d) t)

def issueWidth := T.issueWidth a (b Q) Δ C M 𝓔 𝓒 𝓚 (A.Supplement a 𝓔)
def arity := T.arity a (b Q) + BatchDescent.Beat.markWidth Q T r +
  issueWidth Q A L v hv z Δ C B r + 2 * (Y).scheme.ℓ + A.rebuildWidth Y (slots A r) (d + 1)
def range := (d + 1) * n + T.degree a Δ C + n + 1

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Grouping and matching with a retained border -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)

local notation "a" => (T.scheme.h - r)
local notation "X" => frame A L (Q.b * v) z payload Δ C P

include h in
theorem pos : 0 < v := h.zpos.trans_le h.vpos

include h in
theorem cost_pos : 0 < P.load :=
  (Nat.cast_pos.mpr (Nat.mul_pos Q.pos (pos h))).trans_le h.load

include h in
theorem slack_pos : 0 ≤ σ := by
  have := cost_pos h
  exact nonneg_of_mul_nonneg_left (le_trans (by positivity) h.slack) (by positivity)

include h in
theorem enough (hK : 2 ^ (k Δ) ≤ K) : k Δ ≤ T.scheme.h - a := by
  rw [Nat.sub_sub_self h.group]
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hK.trans h.room)

include h in
theorem slack (hK : 2 ^ (k Δ) ≤ K) (v : ℕ) (hv : v ≤ 2 ^ T.scheme.m) :
    (2 : ℝ) ^ (k Δ) * P.load * (v * 2 ^ a : ℕ) ≤ σ := by
  have := cost_pos h
  apply le_of_mul_le_mul_right _ (show (0 : ℝ) < 2 ^ r by positivity)
  apply le_trans _ h.slack
  push_cast
  rw [mul_assoc, mul_assoc (v : ℝ), ← pow_add, Nat.sub_add_cancel h.group, pow_add]
  gcongr
  · exact_mod_cast hK
  · exact_mod_cast hv

variable (q : (frame A L (Q.b * v) z payload Δ C P).state)

abbrev Poll := T.Selection a (Nat.sub_le _ _) (b Q) (k Δ) P.load Δ C q.val.q.core σ
  (Nat.mul_pos Q.pos (pos h))

theorem elect (hd : 0 < Δ) (hc : Δ ≤ C) (hk : 2 ^ (k Δ) ≤ K) : Nonempty (Poll h q) := by
  have hv : Fintype.card q.val.G.V ≤ 2 ^ T.scheme.m := by
    simpa using Fintype.card_le_of_injective _ q.val.q.core.post.host.injective
  exact T.selection a (Nat.sub_le _ _) (b Q) (k Δ) P.load Δ C q.val.q.core σ _
    hd (hd.trans_le hc) (BatchDescent.Beat.positive Δ) (enough h hk)
    (cost_pos h) q.property.1.bounded (BatchDescent.Beat.bins Δ) (slack h hk _ hv) (by simp [h.full])

abbrev Ticket := T.Branch Q a (Nat.sub_le _ _) (b Q) (k Δ) P.load Δ C v σ (Nat.mul_pos Q.pos (pos h))

def ticket (s : Poll h q) (i : s.choices) : Ticket (Δ := Δ) (C := C) h where
  T := q.val.T
  x := q.val.a
  y := q.val.b
  L := q.val.L
  G := q.val.G
  r := q.val.raw.1
  p := q.val.q.core
  s := s
  i := i
  v := ((Classical.choice q.property.1.live, 0), ⟨0, 0⟩)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Core budgets for a contraction with a retained border -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)
  (q : (frame A L (Q.b * v) z payload Δ C P).state) (s : Poll h q) (i : s.choices)
  (hd : 0 < Δ) (hc : Δ ≤ C)

local notation "t" => ticket h q s i
local notation "hb" => BatchDescent.Beat.choices Q
local notation "G" => Template.Branch.layout t hc
local notation "St" => Template.Branch.state t hb
local notation "M" => book Q A v (pos h) z B

include hd in
theorem estimates :
    (G).Bounded ((4 * Δ) ^ 900) ((4 * C) ^ 900) (gain Δ * P.load) ∧
    ((G).X : ℝ) ≤ Q.ratio * P.width + (L.total + σ) ∧
    q.val.G.Preserves G ∧ ((G).mass : ℝ) ≤ P.mass + 2 * P.width := by
  obtain ⟨bounds, width, preserve, mass, _⟩ :=
    (t).estimates hc hd (slack_pos h) (cost_pos h).le q.property.1.bounded
  refine ⟨⟨bounds.1, bounds.2.1, ?_⟩, ?_, preserve, ?_⟩
  · intro u j
    refine (bounds.2.2 u j).trans ?_
    simp only [gain, BatchDescent.Beat.gain, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
    have := cost_pos h
    gcongr; norm_num
  · exact width.trans (add_le_add (mul_le_mul_of_nonneg_left q.property.1.width Q.ratio_bounds.1)
      (add_le_add_left q.property.1.total _))
  · rw [mass, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact add_le_add q.property.1.mass (mul_le_mul_of_nonneg_left q.property.1.width (by norm_num))

include hd in
theorem mass : (G).mass ≤ q.val.L.cap := by
  rw [q.property.1.cap]
  exact Nat.cast_le.mp ((estimates h q s i hd hc).2.2.2.trans h.history)

include hd in
theorem room : (St).Room (e Δ B) := by
  apply (t).room hb hd (cost_pos h).le q.property.1.bounded _ q.property.1.span
  have hh := Nat.le_pow_clog (by decide : 1 < 2) (gain Δ * B)
  have hv : gain Δ * B * z ≤ 2 ^ (e Δ B) * v := Nat.mul_le_mul hh h.vpos
  calc
    _ = (gain Δ : ℝ) * P.load := by simp only [gain, BatchDescent.Beat.gain, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (gain Δ : ℝ) * (B * z) := mul_le_mul_of_nonneg_left h.ceiling (Nat.cast_nonneg _)
    _ ≤ _ := by rw [← mul_assoc]; exact_mod_cast hv

local notation "rm" => room h q s i hd

theorem ready : (t).Ready hb hc M rm (cap Q A v (pos h) z Δ B) := by
  apply (t).direct hb hc hd M rm q.property.1.neutral
  intro j
  exact History.Book.represent T.scheme Q v (pos h) T.order (Finset.range (B * z + 1))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (size_bound h q j)))

include hd in
theorem valid : (meter L z Δ B).Valid G :=
  valid_of_charge h q (gain Δ) G (mass h q s i hd hc) (estimates h q s i hd hc).1.2.2

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # The core and frozen border of a selected contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)
  (q : (frame A L (Q.b * v) z payload Δ C P).state) (s : Poll h q) (i : s.choices)
  (hd : 0 < Δ) (hc : Δ ≤ C)

local notation "t" => ticket h q s i
local notation "hb" => BatchDescent.Beat.choices Q
local notation "G" => Template.Branch.layout t hc
local notation "M" => book Q A v (pos h) z B
local notation "rm" => room h q s i hd
local notation "𝓚" => meter L z Δ B
local notation "𝓒" => cap Q A v (pos h) z Δ B
local notation "Y" => raw Q A L v (pos h) z Δ C B r
local notation "U" => out Q A L v (pos h) z Δ C B r

abbrev query : A.Query Y (slots A r) (T.scheme.d + 1) := A.query M 𝓒 𝓚 hb hc t rm q.val.raw.2
abbrev posted : (Y).Encodes (query h q s i hd hc).fresh G := (t).encodes hb hc M rm 𝓒 𝓚 hd (ready h q s i hd hc) (valid h q s i hd hc)

local notation "S" => query h q s i hd hc
local notation "E" => posted h q s i hd hc

theorem active : Attachment.Relocation.WriteActive E (S).active := by
  intro x j
  exact ((t).board hb).live_at M rm 𝓒 hc ((t).s.canonical_live hb (t).i (t).v) x j

theorem moves : (S).R.Moves q.val.q E (A.newSlot t q.val.q.slot) :=
  A.grouped_moves t M _ 𝓒 𝓚 hc hb hd rm (ready h q s i hd hc) (valid h q s i hd hc) q.val.q rfl

theorem agrees : (S).M.Agrees q.val.q.core.post.toPresentation (E).post.toPresentation :=
  (t).move_agrees hb hc M rm 𝓒 (ready h q s i hd hc)

local notation "hm" => moves h q s i hd hc
local notation "ha" => active h q s i hd hc
local notation "hx" => agrees h q s i hd hc

def result := (S).apply hm ha hx (show (Y).full = true from h.full)

theorem fits : (result h q s i hd hc).Fits payload := (S).fits hm ha hx (show (Y).full = true from h.full) q.property.2

theorem spare : A.Sparse (Y).sweep (slots A r) (copies Δ B) (result h q s i hd hc).raw := by
  obtain ⟨δ, hδ, hl, hb'⟩ := charges h q (gain Δ) G (estimates h q s i hd hc).1.2.2
  exact (S).spare hm ha hx (show (Y).full = true from h.full) hδ hl hb'

theorem exterior (l : MatrixExponent.slots x ⊕ MatrixExponent.slots y) :
    let a := ((result h q s i hd hc).q.pres.boundary l).val
    let b := (q.val.q.pres.boundary l).val
    (S).sweep.R.kept q.val.raw a.1.1 = some b.1.1 ∧ a.1.2 = A.outer (Y).sweep b.1.2 ∧ a.2.val = b.2.val :=
  (S).exterior hm ha hx (show (Y).full = true from h.full) l

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Retaining the entire original frame during selector validation -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)

local notation "a" => (T.scheme.h - r)
local notation "n" => (T.scheme.h - a)
local notation "X" => frame A L (Q.b * v) z payload Δ C P
local notation "Z" => T.Candidate a (b Q)
local notation "D" => Attachment.payload x y payload T.scheme.m
local notation "Mid" => Format.pair (headed Q A Δ C r) D
local notation "Pr" => BatchDescent.Beat.profile Q

variable (hd : 0 < Δ) (hc : Δ ≤ C) (hk : 2 ^ (k Δ) ≤ K)
    (hs : range (T := T) Δ C r ≤ T.scheme.m)

include h hk hs in
theorem address (j : ℕ) (lo : T.scheme.m ≤ j) (hi : j ≤ T.scheme.m + range (T := T) Δ C r) :
    1 ≤ j ∧ j ≤ p.w := by
  have hh := h.upper
  have := (BatchDescent.Beat.positive Δ).trans (enough h hk)
  unfold range at *
  omega

variable (s : ∀ q : (frame A L (Q.b * v) z payload Δ C P).state, Poll h q)

def start (i : (X).state) (l : (Z).obj) (u : Val x) (w : Val y) : (Mid).obj :=
  ((i.val.raw, T.headed a (Nat.sub_le ..) (b Q) Δ C Q
    (T.prepared a (Nat.sub_le ..) (b Q) (k Δ) P.load Δ C (i.val.raw.1, l))), i.val.data i.property.2 u w)

include hk hs in
theorem first {u : ℕ} {W : Set (Table F)} (hu : 3 ≤ u)
    (fit : arity Q A L v (pos h) z Δ C B r ≤ u)
    (keys : (T.keys a (b Q) (k Δ) P.load Δ C : Set _) ⊆ W) (mark : T.markTable a (b Q) ∈ W) :
    Computes F u W ((X).port.pair Z) Mid
      (fun t : ((X).state × (Z).obj) × Val x × Val y => ((X).encode t.1.1 t.2.1 t.2.2, t.1.2))
      (fun t => start (Q := Q) (r := r) t.1.1 t.1.2 t.2.1 t.2.2)
      (fun t => if (((s t.1.1).selector (BatchDescent.Beat.choices Q)).read t.1.2).isSome then 1 else 0)
      (firstCost Q A Δ C r p + 200 * (D).width) := by
  let A₀ := (A.port x y payload).pair Z
  let A₁ := (T.format.pair (A.port x y payload)).pair Z
  let A₂ := (T.Headed a (b Q) Δ C).pair (T.scheme.format.pair (A.port x y payload))
  let I := ((X).state × (Z).obj) × Val x × Val y
  let load : A₀.obj → A₁.obj := fun x => ((x.1.1.1, x.1), x.2)
  let save : A₂.obj → (Mid).obj := fun x => ((x.2.2.1, x.1), x.2.2.2)
  have hload : Circuit F A₀ A₁ load (A₀.width + 2 * A₁.width) :=
    Circuit.project (Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inl) Sum.inr)
      (by rintro x ((i|i)|i) <;> rfl)
  have hsave : Circuit F A₂ Mid save (A₂.width + 2 * (Mid).width) :=
    Circuit.project (Sum.elim (Sum.elim (Sum.inr ∘ Sum.inr ∘ Sum.inl) Sum.inl) (Sum.inr ∘ Sum.inr ∘ Sum.inr))
      (by rintro x ((i|i)|i) <;> rfl)
  let E (t : I) : A₀.obj := ((X).encode t.1.1 t.2.1 t.2.2, t.1.2)
  have h₁ := Computes.of_map (L := W) (x := E) (Map.circuit hu hload) (fun _ => rfl)
  have hpos := (BatchDescent.Beat.positive Δ).trans (enough h hk)
  have hb := address h hk hs (T.scheme.m + (T.scheme.d + 1) * n) (Nat.le_add_right ..) (by unfold range; omega)
  have hj : T.scheme.m + T.scheme.d ≤ T.scheme.m + (T.scheme.d + 1) * n :=
    Nat.add_le_add_left ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hpos)) _
  have hm := address h hk hs (T.scheme.m + T.scheme.d) (Nat.le_add_right ..) (by unfold range; omega)
  unfold arity at fit
  have ar : BatchDescent.Beat.markWidth Q T r ≤ u := by omega
  have hp : 4 * Q.b ≤ 2 ^ Pr := (Nat.le_add_left ..).trans Nat.lt_two_pow_self.le
  have hs' := T.start_net Q a (Nat.sub_le ..) (b Q) (k Δ) P.load Δ C (A.port x y payload)
    hu hpos (p.access hu hb.1 hb.2 (BatchDescent.Beat.parcel T r)) le_rfl
    (p.access hu hm.1 hm.2 (BatchDescent.Beat.labels T r)) le_rfl (by omega) keys ar mark
    Pr (Nat.le_add_right ..) hp (load ∘ E) (fun i => i.1.1.val.q.core.reciprocal)
  have all := (h₁.comp hs').comp (Computes.of_map (Map.circuit hu hsave) (fun _ => rfl))
  simp only [one_mul, mul_one] at all
  obtain ⟨f, hf, he⟩ := all
  refine ⟨f, hf.mono ?_, fun i t => (he i t).trans ?_⟩
  · unfold firstCost prepareCost
    simp only [A₀, A₁, A₂, input, headed, Attachment.port, Attachment.format, Format.width_pair, Template.format]
    omega
  · have hw := (s i.1.1).valid_eq (BatchDescent.Beat.choices Q) i.1.2
    change (@ite F (start (Q := Q) (r := r) i.1.1 i.1.2 i.2.1 i.2.2 = t) (Classical.propDecidable _) (T.valid a (b Q) Q
      (T.prepared a (Nat.sub_le ..) (b Q) (k Δ) P.load Δ C (i.1.1.val.raw.1, i.1.2))) 0) = _
    rw [hw]
    dsimp only
    cases ((s i.1.1).selector (BatchDescent.Beat.choices Q)).read i.1.2 <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Effect of the contraction on the expansion and its invariants -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)
  (q : (frame A L (Q.b * v) z payload Δ C P).state) (s : Poll h q)
  (hd : 0 < Δ) (hc : Δ ≤ C)

theorem expands (x' : Val x) (y' : Val y) :
    ∑ i : s.choices, (query h q s i hd hc).sweep_weight * (result h q s i hd hc).diagram.eval x' y' =
      q.val.diagram.eval x' y' := by
  let G (i : s.choices) : Diagram F q.val.a q.val.b := ((ticket h q s i).layout hc).diagram
  have he (a b) : ∑ i, (G i).eval a b = q.val.G.diagram.eval a b :=
    s.group.eval_contract s.matching Q (q.val.G.regroup _ (Nat.sub_le _ _)).units (pos h) a b
  refine Eq.trans ?_ (q.val.Z.attach_sum q.val.G.diagram G he x' y')
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (q.val.Z.attach_factor (posted h q s i hd hc).post.toPresentation x' y').symm

variable (i : s.choices)
local notation "t" => ticket h q s i
local notation "G" => Template.Branch.layout t hc
local notation "N" => next Q A L v (pos h) z Δ C B r
local notation "U" => out Q A L v (pos h) z Δ C B r
local notation "V" => target Q A L v (pos h) z Δ C B r
local notation "X" => result h q s i hd hc

set_option maxHeartbeats 400000 in
theorem preserved (hΔ : 3 ≤ Δ) (hg : gain Δ ≤ K) :
    Ready (A.transport (raw Q A L v (pos h) z Δ C B r).sweep (slots A r)) L z (Δ ^ degreePower) (C ^ degreePower) (after L P K Q.ratio 1 σ) X := by
  have env := estimates h q s i hd hc
  have bounds := env.1
  have width := env.2.1
  have stayed := env.2.2.1
  have mass := env.2.2.2
  have ha := q.property.1
  let post := posted h q s i hd hc
  let root := query h q s i hd hc
  have live : Nonempty (G).V := ⟨((t).v.1.1, (t).v.2)⟩
  have low : ∀ j, v ≤ post.post.toPresentation.borderWidth j :=
    (ready h q s i hd hc).floor (fun j => (Nat.le_mul_of_pos_left _ Q.pos).trans (ha.span j))
  refine moved_ready q.val root G q.val.q post _ (moves h q s i hd hc) (active h q s i hd hc)
    (agrees h q s i hd hc) (show (raw Q A L v (pos h) z Δ C B r).full = true from h.full)
    ha live ?_ low stayed ⟨?_, ?_, ?_⟩ ?_ mass
  · intro he
    have hit : Δ ^ 1 < Δ ^ degreePower := Nat.pow_lt_pow_right (by omega) (by decide)
    exact (not_lt_of_ge he (hΔ.trans_lt (by rw [pow_one] at hit; exact hit))).elim
  · exact fun j => (bounds.1 j).trans (Reduction.power_growth hΔ 900 degreePower rfl)
  · exact fun j => (bounds.2.1 j).trans (Reduction.power_growth (hΔ.trans hc) 900 degreePower rfl)
  · intro u j
    change (G).load u j ≤ (K : ℝ) * P.load
    exact (bounds.2.2 u j).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hg) (cost_pos h).le)
  · change ((G).X : ℝ) ≤ Q.ratio * P.width + 1 * (L.total + σ)
    rw [one_mul]
    exact width

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Issuing the history and frozen-seat requests, and extracting scalar factors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)
  (s : ∀ q : (frame A L (Q.b * v) z payload Δ C P).state, Poll h q)
  (hd : 0 < Δ) (hc : Δ ≤ C) (hk : 2 ^ (k Δ) ≤ K) (hs : range (T := T) Δ C r ≤ T.scheme.m)

local notation "a" => (T.scheme.h - r)
local notation "n" => (T.scheme.h - a)
local notation "hb" => BatchDescent.Beat.choices Q
local notation "M" => book Q A v (pos h) z B
local notation "𝓒" => cap Q A v (pos h) z Δ B
local notation "𝓚" => meter L z Δ B
local notation "Y" => raw Q A L v (pos h) z Δ C B r
local notation "N" => next Q A L v (pos h) z Δ C B r
local notation "k'" => slots A r
local notation "p'" => (T.scheme.d + 1)

abbrev Path := Σ q : (frame A L (Q.b * v) z payload Δ C P).state, (s q).choices

def mid (i : Path h s) : (headed Q A Δ C r).obj := (i.1.val.raw, (ticket h i.1 (s i.1) i.2).head hb)

abbrev issued (i : Path h s) := query h i.1 (s i.1) i.2 hd hc

include hk hs in
theorem second : ∃ gate : Table F, Processor.arity gate = issueWidth Q A L v (pos h) z Δ C B r ∧
    ∀ {u : ℕ} {W : Set (Table F)}, 3 ≤ u → arity Q A L v (pos h) z Δ C B r ≤ u →
    gate ∈ W → BatchDescent.Snapshot.sweepTable Y ∈ W →
    Computes F u W (headed Q A Δ C r) (requests Q A L v (pos h) z Δ C B r)
      (mid h s) (fun i => (issued h s hd hc i).sweep.requests)
      (fun i => (issued h s hd hc i).sweep_weight)
      (secondCost Q A L v (pos h) z Δ C B r p + A.sweepCost Y k' p') := by
  let q (i : Path h s) := ticket h i.1 (s i.1) i.2
  let rm (i : Path h s) := room h i.1 (s i.1) i.2 hd
  obtain ⟨gate, hw, hnet⟩ := A.grouped_net M 𝓒 𝓚 hb hc q rm (fun i => i.1.val.raw.2)
    (fun i => ready h i.1 (s i.1) i.2 hd hc)
  refine ⟨gate, hw, ?_⟩
  intro u W hu fit hg hgate
  let l := precision T Δ C r
  have hl : T.size a ≤ l := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have hh : 2 ^ (Window.Tile.radius T.scheme.d + (n + 1)) ≤ l :=
    (Nat.le_add_left ..).trans (Nat.le_add_right ..)
  have hq : 2 ^ (T.degree a Δ C) ≤ l := Nat.le_add_left ..
  unfold arity at fit
  have hi : issueWidth Q A L v (pos h) z Δ C B r ≤ u := by omega
  have he : 2 * (N).scheme.ℓ ≤ u := by omega
  have hn := (BatchDescent.Beat.positive Δ).trans (enough h hk)
  have hd' : T.scheme.d ≤ (T.scheme.d + 1) * n := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hn)
  have ha := address h hk hs (T.scheme.m + T.scheme.d) (Nat.le_add_right ..) (by unfold range; omega)
  have out := hnet hu hg hi (p.access hu ha.1 ha.2 (BatchDescent.Beat.walk Q T r)) le_rfl hl hh hq
  have run := out.comp (Attachment.Query.sweep_net (issued h s hd hc) hu he hgate)
  simp only [one_mul] at run
  exact run

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Applying the common border decoder to a contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Coloring BatchDescent.Trail
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)
  (s : ∀ q : (frame A L (Q.b * v) z payload Δ C P).state, Poll h q)
  (hd : 0 < Δ) (hc : Δ ≤ C) (hk : 2 ^ (k Δ) ≤ K) (hs : range (T := T) Δ C r ≤ T.scheme.m)

local notation "a" => (T.scheme.h - r)
local notation "n" => (T.scheme.h - a)
local notation "N" => next Q A L v (pos h) z Δ C B r
local notation "k'" => slots A r
local notation "p'" => (T.scheme.d + 1)
local notation "self" => hop T.scheme.d none

abbrev swept (i : Path h s) := (issued h s hd hc i).sweep
abbrev moved (i : Path h s) := result h i.1 (s i.1) i.2 hd hc

private def step (d : ℕ) (i : Coloring.B (d + 1)) : Option (Coloring.B d) :=
  if h : i.val < 2 ^ d then some ⟨i.val, h⟩ else none

private theorem nav (i : Path h s) (j : Coloring.B (N).scheme.m) (l : Coloring.B p') :
    (swept h s hd hc i).M.nav j l =
      (step T.scheme.d l).elim (T.parent a j) (T.nav (swept h s hd hc i).old.1 (T.parent a j)) := by
  change subroundNav (U := (N).scheme) (T.parent a) i.1.val.raw.1.1 j l = _
  unfold subroundNav step
  split <;> rfl

private theorem parent (i : Path h s) (j : Coloring.B (N).scheme.m) :
    (swept h s hd hc i).M.nav j self = (swept h s hd hc i).R.parent j :=
  nav_hop (U := (N).scheme) (T.parent a) i.1.val.raw.1.1 j none

include hk hs in
theorem rebuild {u : ℕ} {W : Set (Table F)} (hu : 3 ≤ u)
    (fit : arity Q A L v (pos h) z Δ C B r ≤ u)
    (allow : A.rebuildGate N k' p' self ∈ W) :
    Computes F u W (requests Q A L v (pos h) z Δ C B r) (A.transport N k').format
      (fun i => (swept h s hd hc i).requests) (fun i => (swept h s hd hc i).result)
      (fun _ => 1) (rebuildCost Q A L v (pos h) z Δ C B r p) := by
  have hn := (BatchDescent.Beat.positive Δ).trans (enough h hk)
  have hd' : T.scheme.d ≤ (T.scheme.d + 1) * n := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hn)
  have old := address h hk hs (T.scheme.m + T.scheme.d) (Nat.le_add_right ..) (by unfold range; omega)
  have fresh := address h hk hs (T.scheme.m + (n + 1) + T.degree a Δ C) (by omega) (by unfold range; omega)
  have hf : A.rebuildWidth N k' p' ≤ u := (Nat.le_add_left ..).trans fit
  exact Attachment.Query.rebuild_net hu (Nat.sub_le ..) (p.access hu old.1 old.2 _) le_rfl
    (p.access hu fresh.1 fresh.2 _) le_rfl (T.parent a) (step T.scheme.d) (swept h s hd hc) self
    (nav h s hd hc) (fun i => i.1.val.q.core.reciprocal)
    (fun i => (posted h i.1 (s i.1) i.2 hd hc).reciprocal)
    (parent h s hd hc) hf allow

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # A common selector for contractions of different attached networks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {T : Template F} {Q : Gadget F}
  {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
  {r v z payload d B K H Δ C : ℕ} {σ : ℝ}
  (h : Input A L P p r Q.b (Q.b * v) v z payload d B K H σ)

abbrev stage (Δ C : ℕ) :=
  interim A (raw Q A L v (pos h) z Δ C B r).sweep (slots A r) (copies Δ B) L v z payload
    (Δ ^ degreePower) (C ^ degreePower) (after L P K Q.ratio 1 σ)

variable (s : ∀ q : (frame A L (Q.b * v) z payload Δ C P).state, Poll h q)
  (hd : 0 < Δ) (hc : Δ ≤ C) (hΔ : 3 ≤ Δ) (hg : gain Δ ≤ K)

local notation "a" => (T.scheme.h - r)
local notation "X" => frame A L (Q.b * v) z payload Δ C P
local notation "Y" => stage h Δ C
local notation "Z" => T.Candidate a (b Q)

def selected : Selected X Y Z where
  choice q := (s q).choices
  index q := (s q).selector (BatchDescent.Beat.choices Q)
  next q i := ⟨result h q (s q) i hd hc, ⟨preserved h q (s q) hd hc i hΔ hg, spare h q (s q) i hd hc⟩,
    fits h q (s q) i hd hc⟩
  scalar q i := (query h q (s q) i hd hc).sweep_weight
  expands q x y := (expands h q (s q) hd hc x y).symm

abbrev CaseBit := Path h s × Val x × Val y

def oldBits (i : CaseBit h s) := i.1.1.val.data i.1.1.property.2 i.2.1 i.2.2

def output (i : CaseBit h s) :=
  let j := i.1
  let q := result h j.1 (s j.1) j.2 hd hc
  (q.raw, q.data (fits h j.1 (s j.1) j.2 hd hc) i.2.1 i.2.2)

theorem start_at (i : CaseBit h s) :
    start (Q := Q) (r := r) i.1.1 (((s i.1.1).selector (BatchDescent.Beat.choices Q)).write i.1.2) i.2.1 i.2.2 =
      (mid h s i.1, oldBits h s i) :=
  Prod.ext (Prod.ext rfl ((ticket h i.1.1 (s i.1.1) i.1.2).headed_eq (BatchDescent.Beat.choices Q))) rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Description size in a contraction with a retained border -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Assembly History Packing Case Coloring
open scoped Classical

variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)
local notation "I" => Case κ Q.b d B
local notation "E" => e Δ B

abbrev plan (i : I) := raw (Q.extend i.F) i.A i.L i.v i.positive i.z Δ C B i.r
abbrev fresh (i : I) := (plan Q Δ C d B i).sweep
abbrev pack (i : I) := target (Q.extend i.F) i.A i.L i.v i.positive i.z Δ C B i.r
abbrev menu (i : I) := book (Q.extend i.F) i.A i.v i.positive i.z B
abbrev added (i : I) := (Post.headerFmt (i.T.degree i.a Δ C) E (menu Q d B i).d).width +
  (menu Q d B i).overhead E

private theorem log_bound (x y z : ℕ) (h : z ≤ (x + 1) * (1 + y)) :
    Nat.clog 2 z ≤ x + Nat.clog 2 (1 + y) := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_add]
  exact h.trans (Nat.mul_le_mul Nat.lt_two_pow_self (Nat.le_pow_clog (by decide) _))

theorem meter_bound : Base (fun i : I => (meter i.L i.z Δ B).count) := by
  refine (base_const 3).mul (((base_const (copies Δ B)).add units).mono fun i => ?_)
  exact log_bound _ _ _ (by simp only [add_mul, mul_add, one_mul, mul_one]; omega)

def maxDegree := (d + Nat.clog 2 ((4 * C) ^ 300) + 1) * 3

theorem child_degree (i : I) : i.T.degree i.a Δ C ≤ maxDegree C d := by
  simp only [Template.degree, Template.bound, i.h.full, ↓reduceIte]
  exact Nat.mul_le_mul_right 3 (Nat.add_le_add_right (Nat.add_le_add i.h.degree (min_le_right ..)) 1)

theorem child_slots : Base (fun i : I => 2 ^ i.T.degree i.a Δ C) :=
  (base_const (2 ^ maxDegree C d)).mono fun i => Nat.pow_le_pow_right (by decide) (child_degree Q Δ C d B i)

theorem child_factor : Base (fun i : I => 2 ^ (i.n + 1)) := tiles.exp_add (base_const (2 ^ 1))
theorem place_factor : Base (fun i : I => 2 ^ slots i.A i.r) := tiles.exp_add stations
theorem hop_factor : Base (fun i : I => 2 ^ (i.T.scheme.d + 1)) := Case.slots.exp_add (base_const (2 ^ 1))

private theorem length_bound : Base (fun i : I => (menu Q d B i).d) := by
  refine ((base_const (B + 4)).add units).mono fun i => ?_
  change Nat.clog 2 ((Finset.range (B * i.z + 1)).card + 3) ≤ _
  rw [Finset.card_range]
  exact log_bound _ _ _ (by simp only [add_mul, mul_add, one_mul, mul_one]; omega)

private theorem role_bound : Base (fun i : I => Kind.width i.T.scheme (Q.extend i.F) (i.T.scheme.e + 2)) := by
  have h : Base (fun i : I => 1 + (Fintype.card (Role Q) + 2 ^ (i.T.scheme.e + 2))) :=
    (base_const 1).add ((base_const _).add (spans.exp_add (base_const (2 ^ 2))))
  refine ((h.add (base_const 1)).clog).mono fun i => ?_
  simp only [Kind.width, Kind.Small, Fintype.card_sum, Fintype.card_fin, Dense.used, i.h.single, pow_zero]
  rfl

private theorem overhead_bound : Base (fun i : I => (menu Q d B i).overhead E) := by
  have he : Base (fun _ : I => 2 ^ E) := base_const _
  have hs : Base (fun i : I => 2 ^ (menu Q d B i).s) :=
    (spans.exp_add (base_const (2 ^ 2))).exp_add (base_const (2 ^ Nat.clog 2 (Q.b + 1)))
  have hd := length_bound Q d B
  have hr := role_bound Q d B
  have hl : Base (fun i : I => Dense.used (i.T.scheme.ℓ + Kind.width i.T.scheme (Q.extend i.F) (i.T.scheme.e + 2))) := by
    refine (hr.add lengths).mono fun i => ?_
    rw [add_assoc 1]
    exact log_bound _ _ _ (by simp only [add_mul, mul_add, one_mul, mul_one]; omega)
  have hw := (he.mul hd).add (he.mul ((base_const 1).add
    ((base_const 0).add (hs.mul ((base_const 1).add ((base_const E).add hd))))))
  refine ((hw.add (he.mul hl)).add (he.mul hr)).mono fun i => ?_
  rw [Book.overhead, Post.bookkeeping, Dense.overhead, width_code]

theorem added_bound : Base (added Q Δ C d B) := by
  have hd := (child_slots Q Δ C d B).of_exp
  have core := Width.pair (Width.addr hd) (Width.addr (base_const E))
  have bit : Base (fun _ : I => Format.bit.width) := base_const _
  have row := Width.pair (Width.addr (length_bound Q d B)) (Width.pair bit (Width.pair bit core))
  exact (Width.pair bit (Width.vec (base_const (2 ^ E)) row)).add (overhead_bound Q Δ d B)

theorem bits_eq (i : I) : (plan Q Δ C d B i).scheme.ℓ = added Q Δ C d B i + 2 ^ E * i.T.scheme.ℓ := by
  change (Post.record _ _ _ (.addr _)).width = _
  simp only [added, cap, Post.record, Post.headerFmt, Format.width_pair, Format.width_addr, add_assoc]

theorem child_bound : Child (plan Q Δ C d B) (fun i => i.n + 1) where
  extent _ := Nat.sub_le ..
  allocation _ := le_rfl
  growth := (child_factor Q d B).short
  single _ := rfl
  spans := short_const (2 ^ E)
  neighbors := (child_slots Q Δ C d B).short
  bits := ((added_bound Q Δ C d B).short.add ((short_const (2 ^ E)).mul Case.bits)).mono
    fun i => (bits_eq Q Δ C d B i).le
  count := (meter_bound Q Δ d B).short

theorem fresh_bound : Child (fresh Q Δ C d B) (fun i => i.n + 1) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := child_bound Q Δ C d B
  exact ⟨a, b, c, d, e, f, g, h⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Exterior transfer in one beat -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Packing
variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)

theorem carryWidth_bound : Case.Short (fun i : Case κ Q.b d B =>
    i.A.carryWidth (fresh Q Δ C d B i) (slots i.A i.r) (i.n + 1) i.payload) :=
  (fresh_bound Q Δ C d B).carryWidth (place_factor Q d B).short (child_factor Q d B).short

theorem carrySize_bound : Case.Total (fun i : Case κ Q.b d B =>
    i.A.carryCost (fresh Q Δ C d B i) (slots i.A i.r) (i.T.scheme.d + 1) (i.n + 1)
      i.x i.y i.payload i.p) :=
  (fresh_bound Q Δ C d B).carryCost (place_factor Q d B).short (hop_factor Q d B).short
    (child_factor Q d B).short

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

/-! # Linear dependence on the length of old contraction labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
open Assembly Packing Case

variable {κ : Type} [Field κ] (Q : Gadget κ) (Δ C d B : ℕ)
local notation "I" => Case κ Q.b d B
local notation "Y" => fresh Q Δ C d B
local notation "E" => e Δ B
local notation "N" => copies Δ B

private def links (i : I) :=
  2 ^ (slots i.A i.r) * (1 + i.A.k + 2 ^ max i.A.e E * (2 + i.T.degree i.a Δ C + slots i.A i.r + max i.A.e E))

private theorem links_bound : Base (links Q Δ C d B) := by
  have q := place_factor Q d B
  have t := Width.expMax (ports : Base (fun i : I => _)) (base_const (2 ^ E))
  have d := (child_slots Q Δ C d B).of_exp
  exact q.mul (((base_const 1).add stations.of_exp).add
    (t.mul ((((base_const 2).add d).add q.of_exp).add t.of_exp)))

theorem labels_bound : ∃ H : ℕ, ∀ i : I,
    (Y i).scheme.ℓ + (pack Q Δ C d B i).ℓ ≤ H * (i.T.scheme.ℓ + i.A.ℓ) + i.base ^ H := by
  obtain ⟨j, hj⟩ := (((base_const 2).mul (added_bound Q Δ C d B)).add (links_bound Q Δ C d B)).bound
  let H := j + 2 * 2 ^ E + N
  refine ⟨H, fun i => ?_⟩
  have h₁ : 2 * 2 ^ E * i.T.scheme.ℓ + N * i.A.ℓ ≤ H * (i.T.scheme.ℓ + i.A.ℓ) := by
    rw [mul_add]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ ((Nat.le_add_left ..).trans (Nat.le_add_right ..)))
      (Nat.mul_le_mul_right _ (Nat.le_add_left ..))
  have h₂ : 2 * added Q Δ C d B i + links Q Δ C d B i ≤ i.base ^ H :=
    (hj i).trans (Nat.pow_le_pow_right (lt_of_lt_of_le (by decide) i.base_two)
      ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))
  have he : (pack Q Δ C d B i).ℓ = (Y i).scheme.ℓ + N * i.A.ℓ + links Q Δ C d B i :=
    i.A.short_width (Y i) _ N
  have hh : (Y i).scheme.ℓ = _ := bits_eq Q Δ C d B i
  rw [he, hh]
  rw [mul_assoc] at h₁
  omega

theorem range_bound : Short (fun i : I => range (T := i.T) Δ C i.r) :=
  (((hop_factor Q d B).short.of_exp.mul tiles.short.of_exp).add
    (child_slots Q Δ C d B).short.of_exp |>.add tiles.short.of_exp).add (short_const 1)

theorem shrinkWidth_bound : Short (fun i : I => i.A.shrinkWidth (Y i) (slots i.A i.r) N) :=
  (fresh_bound Q Δ C d B).shrinkWidth (place_factor Q d B).short N

theorem rebuildCost_bound : Cost (fun i : I =>
    rebuildCost (Q.extend i.F) i.A i.L i.v i.positive i.z Δ C B i.r i.p) :=
  (fresh_bound Q Δ C d B).rebuildCost (place_factor Q d B).short (hop_factor Q d B).short

theorem sweepCost_bound : Cost (fun i : I =>
    i.A.sweepCost (plan Q Δ C d B i) (slots i.A i.r) (i.T.scheme.d + 1)) :=
  (child_bound Q Δ C d B).sweepCost (place_factor Q d B).short (hop_factor Q d B).short

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat
end

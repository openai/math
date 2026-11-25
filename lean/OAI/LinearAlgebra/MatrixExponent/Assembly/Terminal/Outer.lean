import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.DictionaryHeaders
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanTiles
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Keys
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.OuterRows
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.ContractRates
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.BoardPush
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep

/-! Permute whole padded chunks, fixing each zero-width or exterior span. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical

variable {F : Type} (S : Scheme F) (r : S.format.obj)

def partner (s : S.Span) := if S.width r s = 0 then s else (S.peer r s).getD s

theorem partner_edge {s v : S.Span} (h : S.peer r s = some v) (hw : 0 < S.width r s) :
    partner S r s = v := by simp [partner, h, hw.ne']

theorem partner_cases (s : S.Span) : partner S r s = s ∨
    (S.peer r s = some (partner S r s) ∧ 0 < S.width r s) := by
  by_cases h : S.width r s = 0
  · exact .inl (ite_eq_left h)
  cases hs : S.peer r s with
  | none => simp [partner, h, hs]
  | some v => exact .inr ⟨by simp [partner, h, hs], Nat.pos_of_ne_zero h⟩

theorem partner_width (ok : S.Proper r) (s : S.Span) : S.width r (partner S r s) = S.width r s := by
  rcases partner_cases S r s with h|⟨h, _⟩
  · rw [h]
  · exact (ok _ _ h).2.1.symm

theorem partner_inv (ok : S.Proper r) : Function.Involutive (partner S r) := by
  intro s
  rcases partner_cases S r s with h|⟨h, hp⟩
  · rw [h, h]
  · exact partner_edge _ _ (ok _ _ h).1 ((partner_width S r ok s).symm ▸ hp)

theorem partner_live (ok : S.Proper r) (s : S.Span) (h : Active S r s.1) :
    Active S r (partner S r s).1 := by
  rcases partner_cases S r s with he|⟨_, hp⟩
  · rwa [he]
  · exact ⟨(partner S r s).2, 0, (partner_width S r ok s).symm ▸ hp⟩

theorem partner_chunk (ok : S.Proper r) (t : ℕ) (s : S.Span) :
    chunk S r t (partner S r s) = chunk S r t s := by
  have hi : Active S r (partner S r s).1 ↔ Active S r s.1 :=
    ⟨fun h => by simpa only [partner_inv S r ok s] using partner_live S r ok _ h, partner_live S r ok s⟩
  simp only [chunk, hi]

variable (t : ℕ) {w z : ℕ}

def Lengths (a : SpanPlan.Entries S.m w z S.spanRows) : Prop :=
  ∀ s, (a s.1.1 (S.spanIndex s)).2.1.val = chunk S r t s

def endpoint (a : SpanPlan.Entries S.m w z S.spanRows) (s : S.Span) :=
  (Match.rowIndex S.m z).symm (s.1.1, (a s.1.1 (S.spanIndex s)).1)

structure Inner (peer : B (S.m + z) → B (S.m + z)) (send take : SpanPlan.Entries S.m w z S.spanRows) : Prop where
  bij : Function.Bijective peer
  lengths : Lengths S r t send
  paired : ∀ s, send s.1.1 (S.spanIndex s) =
    ((take s.1.1 (S.spanIndex s)).1, (take s.1.1 (S.spanIndex s)).2.1, S.spanIndex (partner S r s))
  order : ∀ s, (take s.1.1 (S.spanIndex s)).2.2 = S.spanIndex s
  contacts : ∀ s, 0 < chunk S r t s → peer (endpoint S send s) = endpoint S take (partner S r s)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! The two sides of each contact reserve the same space in destination order. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Inner
open Coloring

variable {F : Type} {S : Scheme F} {r : S.format.obj} {t w z : ℕ}
  {peer : B (S.m + z) → B (S.m + z)} {send take : SpanPlan.Entries S.m w z S.spanRows}
  (h : Inner S r t peer send take) (ok : S.Proper r)

abbrev src (S : Scheme F) (z : ℕ) := Match.rowIndex S.m z
def dst := (Equiv.ofBijective peer h.bij).trans (src S z)

local notation "A" => Equiv.toEmbedding (src S z)
local notation "D" => Equiv.toEmbedding (dst h)
local notation "L" => SpanPlan.offsets ∘ send
local notation "R" => SpanPlan.offsets ∘ take

include h
theorem target_lengths : Lengths S r t take := by
  intro s
  have hh := h.lengths s
  rwa [h.paired] at hh

theorem send_order (s : S.Span) :
    (send s.1.1 (S.spanIndex s)).2.2 = S.spanIndex (partner S r s) := by rw [h.paired]

theorem taken (s : S.Span) (hs : 0 < chunk S r t s) :
    h.dst (endpoint S send s) =
      ((partner S r s).1.1, (take (partner S r s).1.1 (S.spanIndex (partner S r s))).1) := by
  change src S z (peer (endpoint S send s)) = _
  rw [h.contacts s hs]
  exact (src S z).apply_symm_apply _

theorem target_unique (v : B S.m) : SpanPlan.Unique (SpanPlan.offsets (take v)) := by
  have key (i : B S.spanRows) : (take v i).2.2 = i := by
    simpa only [Scheme.hostSpan_owner, Scheme.spanIndex_hostSpan] using h.order (S.hostSpan (v, i))
  intro i j _ _ _ he
  exact (key i).symm.trans (he.trans (key j))

omit h in
private theorem source_endpoint (e : B (S.m + z)) (i : B S.spanRows)
    (hi : SpanPlan.port ((L) (src S z e).1) i = (src S z e).2) :
    endpoint S send (S.hostSpan ((src S z e).1, i)) = e := by
  simp only [endpoint, Scheme.hostSpan_owner, Scheme.spanIndex_hostSpan]
  change (send _ _).1 = _ at hi
  rw [hi]
  exact (src S z).symm_apply_apply _

theorem is_pair {e : B (S.m + z)} {i j : B S.spanRows} (q : SpanPlan.Paired le_rfl A D (L) (R) e i j) :
    partner S r (S.hostSpan ((src S z e).1, i)) = S.hostSpan ((h.dst e).1, j) := by
  let s := S.hostSpan ((src S z e).1, i)
  have hp : 0 < chunk S r t s := by
    rw [← h.lengths s, S.spanIndex_hostSpan]
    exact q.left
  have he := h.taken s hp
  rw [source_endpoint (send := send) e i q.source] at he
  let v := S.hostSpan ((h.dst e).1, j)
  have ho : S.spanIndex (partner S r s) = S.spanIndex v := by
    rw [← h.send_order, ← h.order v]
    simp only [s, v, Scheme.hostSpan_owner, Scheme.spanIndex_hostSpan]
    exact q.order
  exact S.hostSpan.symm.injective (Prod.ext (congrArg Prod.fst he).symm ho)

include ok
theorem source_unique (v : B S.m) : SpanPlan.Unique (SpanPlan.offsets (send v)) := by
  intro i j hi hj hc ho
  let s := S.hostSpan (v, i)
  let u := S.hostSpan (v, j)
  have hs : 0 < chunk S r t s := by rw [← h.lengths s, S.spanIndex_hostSpan]; exact hi
  have hu : 0 < chunk S r t u := by rw [← h.lengths u, S.spanIndex_hostSpan]; exact hj
  have hh : endpoint S send s = endpoint S send u := by
    simp only [endpoint, s, u, Scheme.hostSpan_owner, Scheme.spanIndex_hostSpan]
    exact congrArg (fun a => (src S z).symm (v, a)) hc
  have ha := (h.taken s hs).symm.trans ((congrArg h.dst hh).trans (h.taken u hu))
  have hb : S.spanIndex (partner S r s) = S.spanIndex (partner S r u) := by
    rw [← h.send_order, ← h.send_order]
    simp only [s, u, Scheme.hostSpan_owner, Scheme.spanIndex_hostSpan]
    exact ho
  have hv : (partner S r s).1.1 = (partner S r u).1.1 := by
    have eq := congrArg Prod.fst ha
    exact eq
  have eq : partner S r s = partner S r u :=
    S.hostSpan.symm.injective (Prod.ext hv hb)
  exact congrArg Prod.snd (S.hostSpan.injective ((partner_inv S r ok).injective eq))

theorem matched : SpanPlan.Match le_rfl A D (L) (R) := by
  intro e o
  let x := SpanPlan.offsets (send (src S z e).1)
  let y := SpanPlan.offsets (take (h.dst e).1)
  change SpanPlan.amount x (src S z e).2 o = SpanPlan.amount y (h.dst e).2 o
  have equal (s : S.Span) (hs : 0 < chunk S r t s)
      (he : endpoint S send s = e) (ho : S.spanIndex (partner S r s) = o) :
      SpanPlan.amount x (src S z e).2 o = SpanPlan.amount y (h.dst e).2 o := by
    have hv := h.taken s hs
    rw [he] at hv
    have hu : src S z e = (s.1.1, (send s.1.1 (S.spanIndex s)).1) := by
      rw [← he]; exact (src S z).apply_symm_apply _
    let a := partner S r s
    have A₁ := SpanPlan.amount_at _ (h.source_unique ok s.1.1) (S.spanIndex s) (hs.trans_eq (h.lengths s).symm)
    have A₂ := SpanPlan.amount_at _ (h.target_unique a.1.1) (S.spanIndex a)
      ((hs.trans_eq (partner_chunk S r ok t s).symm).trans_eq (h.target_lengths a).symm)
    unfold x y
    rw [hu, hv, ← ho]
    simp only [SpanPlan.port, SpanPlan.pos, SpanPlan.len, SpanPlan.offsets] at A₁ A₂
    rw [h.send_order s, h.lengths s] at A₁
    rw [h.order a, h.target_lengths a, partner_chunk S r ok] at A₂
    exact A₁.trans A₂.symm
  by_cases hs : 0 < SpanPlan.amount x (src S z e).2 o
  · obtain ⟨i, hi, hc, ho⟩ := SpanPlan.amount_pos _ _ _ hs
    let s := S.hostSpan ((src S z e).1, i)
    exact equal s (by rw [← h.lengths s, S.spanIndex_hostSpan]; exact hi)
      (source_endpoint (send := send) _ _ hc) (by rw [← h.send_order, S.spanIndex_hostSpan]; exact ho)
  by_cases ht : 0 < SpanPlan.amount y (h.dst e).2 o
  · obtain ⟨i, hi, hc, ho⟩ := SpanPlan.amount_pos _ _ _ ht
    let u := S.hostSpan ((h.dst e).1, i)
    let s := partner S r u
    have hp : 0 < chunk S r t s := by
      rw [partner_chunk S r ok, ← h.target_lengths u, S.spanIndex_hostSpan]
      exact hi
    have hv : partner S r s = u := partner_inv S r ok u
    apply equal s hp
    · apply h.dst.injective
      rw [h.taken s hp, hv, S.spanIndex_hostSpan]
      exact Prod.ext rfl hc
    · rw [hv, ← h.order u, S.spanIndex_hostSpan]
      exact ho
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Inner
end

/-! Matching full padded chunks is exactly the internal-wire condition. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {t V : ℕ}

def segment (i : Data S r t) : S.Span := (i.1.val, i.2.1)

def mate (ok : S.Proper r) (i : Data S r t) : Data S r t :=
  let u := partner S r (segment i)
  (⟨u.1, partner_live _ _ ok _ i.1.property⟩, u.2, i.2.2)

theorem data_ext {a b : Data S r t} (hs : segment a = segment b) (hi : a.2.2 = b.2.2) : a = b :=
  Prod.ext (Subtype.ext (congrArg Prod.fst hs)) (Prod.ext (congrArg Prod.snd hs) hi)

theorem mate_inv (ok : S.Proper r) : Function.Involutive (mate (t := t) ok) :=
  fun i => data_ext (partner_inv S r ok (segment i)) rfl

variable (h : Fits S r V t) (ok : S.Proper r)

theorem mate_join (i j : S.Pin r) (e : S.Joins r i j) : mate ok (pin S r h i) = pin S r h j :=
  data_ext (partner_edge S r e.1 (Nat.zero_lt_of_lt i.2.isLt)) (Fin.ext e.2)

theorem mate_iff (a : S.Pin r → Bool) :
    (∀ i, store S r h a (slot S r h i) = store S r h a (slot S r h (mate ok i))) ↔
      ∀ i j, S.Joins r i j → a i = a j := by
  constructor
  · intro eq i j he
    have e := eq (pin S r h i)
    rw [mate_join h ok i j he] at e
    exact (read_store S r h a i).symm.trans (e.trans (read_store S r h a j))
  · intro eq i
    by_cases hi : i ∈ Set.range (pin S r h)
    · obtain ⟨p, rfl⟩ := hi
      rcases partner_cases S r p.1 with he|⟨he, _⟩
      · rw [show mate ok (pin S r h p) = pin S r h p from data_ext he rfl]
      · let q : S.Pin r := ⟨partner S r p.1, p.2.cast (partner_width S r ok p.1).symm⟩
        have e : S.Joins r p q := ⟨he, rfl⟩
        rw [mate_join h ok p q e]
        exact (read_store S r h a p).trans ((eq p q e).trans (read_store S r h a q).symm)
    · have le : S.width r (segment i) ≤ i.2.2.val := le_of_not_gt (mt (pin_range S r h i).mpr hi)
      have le' : S.width r (partner S r (segment i)) ≤ i.2.2.val := (partner_width S r ok _).trans_le le
      exact ((padded h a).2 i le).trans ((padded h a).2 (mate ok i) le').symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! Turning length declarations into actual addresses in the padded argument bank. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {t V w z : ℕ}

theorem segment_lt (i : Data S r t) : i.2.2.val < chunk S r t (segment i) := by
  rw [chunk, ite_eq_left (show Active S r (segment i).1 from i.1.property)]
  exact i.2.2.isLt

def cell (s : S.Span) (j : ℕ) (hj : j < chunk S r t s) : Data S r t :=
  let hp : Active S r s.1 := by by_contra he; simp [chunk, he] at hj
  (⟨s.1, hp⟩, s.2, ⟨j, by simpa only [chunk, ite_eq_left hp] using hj⟩)

namespace Lengths
variable {a : SpanPlan.Entries S.m w z S.spanRows} (hl : Lengths S r t a)
  (h : Fits S r V t) (hw : height S t < w)
include hl

theorem at_row (v : B S.m) (j : B S.spanRows) :
    (a v j).2.1.val = chunk S r t (S.hostSpan (v, j)) := by
  simpa only [Scheme.hostSpan_owner, Scheme.spanIndex_hostSpan] using hl (S.hostSpan (v, j))

theorem sum (v : B S.m) : (∑ j, (a v j).2.1.val) = (bank S r h).length v := by
  simp_rw [hl.at_row]
  exact chunks_sum h v

include h hw

theorem small (v : B S.m) : (∑ j, (a v j).2.1.val) < 2 ^ w :=
  (hl.sum h v).trans_lt (((bank S r h).longest v).trans_lt (Nat.pow_lt_pow_right (by decide) hw))

theorem total (v : B S.m) : (SpanPlan.total (a v)).val = (bank S r h).length v :=
  (SpanPlan.total_val _ (hl.small h hw v)).trans (hl.sum h v)

theorem offset (s : S.Span) :
    SpanPlan.offset (SpanPlan.offsets (a s.1.1)) (S.spanIndex s) = chunkStart S r t s := by
  change ((SpanPlan.offsets (a s.1.1) (S.spanIndex s)).2.2.2).val = _
  rw [SpanPlan.offset_val _ (hl.small h hw _)]
  simp_rw [hl.at_row]
  rfl

theorem offset_row (v : B S.m) (j : B S.spanRows) :
    SpanPlan.offset ((SpanPlan.offsets ∘ a) v) j = chunkStart S r t (S.hostSpan (v, j)) := by
  simpa only [Scheme.hostSpan_owner, Scheme.spanIndex_hostSpan, Function.comp_apply] using
    hl.offset h hw (S.hostSpan (v, j))

theorem covers : SpanPlan.Covers (bank S r h) (SpanPlan.offsets ∘ a) := by
  intro v j hj
  obtain ⟨i, hi⟩ := (index S r h).surjective ⟨v, j, hj⟩
  have hv : (segment i).1.1 = v := congrArg Sigma.fst hi
  have ho : (index S r h i).2.val = j := congrArg (fun b => b.2.val) hi
  rw [← hv]
  refine ⟨S.spanIndex (segment i), i.2.2.val, ?_, ?_⟩
  · exact (segment_lt i).trans_eq (hl _).symm
  · rw [Function.comp_apply, hl.offset h hw]
    exact (index_val h i).symm.trans ho

theorem side (place : B (S.m + z) ≃ B S.m × B z) (hu : ∀ v, SpanPlan.Unique (SpanPlan.offsets (a v))) :
    SpanPlan.Side (bank S r h) le_rfl place.toEmbedding (SpanPlan.offsets ∘ a) := by
  let length (v : B S.m) (i : B S.spanRows) := (a v i).2.1.val
  have address (v i) : SpanPlan.offset ((SpanPlan.offsets ∘ a) v) i = Routing.offset (length v) Fin.val i :=
    SpanPlan.offset_val _ (hl.small h hw v) i
  refine ⟨?_, hu, ?_, ?_, ?_⟩
  · intro v c
    exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans_lt (hl.small h hw v)
  · intro v i hi
    rw [address, ← hl.sum h v]
    change Routing.offset (length v) Fin.val i + length v i ≤ ∑ k, length v k
    have hp : 0 < length v i := hi
    have lt := (Routing.offsetIndex (length v) Fin.val ⟨i, _, Nat.sub_lt hp Nat.one_pos⟩).isLt
    change Routing.offset (length v) Fin.val i + (length v i - 1) < _ at lt
    omega
  · intro v i j k l hk hl' he
    rw [address, address] at he
    let order := Routing.pack (length v) Fin.val (fun _ _ _ _ eq => Fin.ext eq)
    have eq : order ⟨i, k, hk⟩ = order ⟨j, l, hl'⟩ := Fin.ext he
    exact congrArg Sigma.fst (order.injective eq)
  · intro v j _
    exact ⟨place.symm (v, (a v j).1), congrArg Prod.fst (place.apply_symm_apply _),
      congrArg Prod.snd (place.apply_symm_apply _)⟩

end Lengths
end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! Each physical transmission carries one padded bit to its partner. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Inner
open Coloring
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {t V w z : ℕ}
  {peer : B (S.m + z) → B (S.m + z)} {send take : SpanPlan.Entries S.m w z S.spanRows}
  (h : Inner S r t peer send take) (ok : S.Proper r) (fit : Fits S r V t) (hw : height S t < w)

def traffic : Payload.Traffic (bank S r fit) (bank S r fit) (2 ^ z) :=
  SpanPlan.traffic (h.lengths.side fit hw (src S z) (h.source_unique ok))
    (h.target_lengths.side fit hw h.dst h.target_unique) (h.matched ok)
    (h.target_lengths.covers fit hw)

theorem valid : Payload.Script.Valid (h.traffic ok fit hw) le_rfl (SpanPlan.emit peer (send, take)) := by
  refine SpanPlan.valid _ _ _ _ _ _ _ (h.lengths.total fit hw) (h.target_lengths.total fit hw) ?_
  intro e _
  change peer ((src S z).symm (src S z e)) = (src S z).symm (src S z (peer e))
  simp

private theorem eq_bit {m V k : ℕ} (P : Payload m V k) {a b : P.Bit}
    (he : a.1 = b.1) (hb : a.2.val = b.2.val) : a = b :=
  Sigma.ext he ((Fin.heq_ext_iff (congrArg _ he)).mpr hb)

theorem carries_bit (e : B (S.m + z)) (i : Fin ((h.traffic ok fit hw).length e)) :
    ∃ a : Data S r t, (h.traffic ok fit hw).source e i = index S r fit a ∧
      (h.traffic ok fit hw).target e i = index S r fit (mate ok a) := by
  obtain ⟨u, v, j, q, hj, hs, hd⟩ := SpanPlan.transmission
    (h.lengths.side fit hw (src S z) (h.source_unique ok))
    (h.target_lengths.side fit hw h.dst h.target_unique) (h.matched ok)
    (h.target_lengths.covers fit hw) e i
  let s := S.hostSpan ((src S z e).1, u)
  let a := cell s j (hj.trans_eq (h.lengths.at_row _ _))
  have he : partner S r s = S.hostSpan ((h.dst e).1, v) := h.is_pair q
  refine ⟨a, ?_, ?_⟩
  · have hi := index_val fit a
    change _ = chunkStart S r t s + j at hi
    rw [h.lengths.offset_row fit hw] at hs
    exact eq_bit (bank S r fit) rfl (hs.trans hi.symm)
  · have hv : (h.dst e).1 = (index S r fit (mate ok a)).1 :=
      (congrArg (fun t : S.Span => t.1.1) he).symm
    have hi := index_val fit (mate ok a)
    change _ = chunkStart S r t (partner S r s) + j at hi
    rw [he] at hi
    rw [h.target_lengths.offset_row fit hw] at hd
    exact eq_bit (bank S r fit) hv (hd.trans hi.symm)

local notation "P" => PeerLayout.S S.m V (height S t) S.m V (height S t) (2 ^ z)
local notation "C" => Payload.Script.decode le_rfl (SpanPlan.emit peer (send, take))

include h hw in
theorem carries (a : Tape S V t) :
    (P).Carries C a a ↔ outerZero fit a ∧ ∀ i, a (slot S r fit i) = a (slot S r fit (mate ok i)) := by
  let M := h.traffic ok fit hw
  rw [(h.valid ok fit hw).carries]
  change M.links.Matches a a ↔ _
  unfold Bank.Links.Matches
  simp only [show ∀ i, M.links.pad i = true ↔ i ∉ Set.range (bank S r fit).wire from
    fun _ => decide_eq_true_iff]
  apply and_congr_right
  intro _
  change (∀ e j, a ((bank S r fit).wire (M.source e j)) = a ((bank S r fit).wire (M.target e j))) ↔ _
  constructor
  · intro eq i
    obtain ⟨e, j, hj⟩ := M.covers (index S r fit (mate ok i))
    change M.target e j = _ at hj
    obtain ⟨b, hb, hb'⟩ := h.carries_bit ok fit hw e j
    have eq' := eq e j
    rw [hb, hb'] at eq'
    have he : b = i := (mate_inv ok).injective ((index S r fit).injective (hb'.symm.trans hj))
    rwa [he] at eq'
  · intro eq e j
    obtain ⟨i, hi, hi'⟩ := h.carries_bit ok fit hw e j
    rw [hi, hi']
    exact eq i

include h hw ok in
theorem carries_store (a : S.Pin r → Bool) :
    (P).Carries C (store S r fit a) (store S r fit a) ↔ ∀ i j, S.Joins r i j → a i = a j := by
  rw [h.carries ok fit hw, and_iff_right (padded fit a).1, mate_iff]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Inner
end

/-! # Projecting the terminal assignment to its exterior payload -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
open Coloring
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj}
  {V t V' k' w z : ℕ} (h : Fits S r V t) (hx : S.Fits r V' k')

private def fromBank (i : (S.payload r hx).Bit) :=
  place S r h ((S.index r hx).symm i).val

private theorem from_host (i : (S.payload r hx).Bit) : (fromBank h hx i).1 = i.1 := by
  obtain ⟨i, rfl⟩ := (S.index r hx).surjective i
  rw [fromBank, Equiv.symm_apply_apply]
  rfl

private def send (v : B S.m) : Fin (S.load r v) ↪ Fin ((bank S r h).length v) where
  toFun i := ⟨(fromBank h hx ⟨v, i⟩).2.val, by
    have := (fromBank h hx ⟨v, i⟩).2.isLt
    exact this.trans_eq (congrArg _ (from_host h hx ⟨v, i⟩))⟩
  inj' i j he := by
    have eq : fromBank h hx ⟨v, i⟩ = fromBank h hx ⟨v, j⟩ := by
      have e := (from_host h hx ⟨v, i⟩).trans (from_host h hx ⟨v, j⟩).symm
      exact Sigma.ext e ((Fin.heq_ext_iff (congrArg _ e)).mpr (congrArg Fin.val he))
    have hv := (S.index r hx).symm.injective (Subtype.ext ((place S r h).injective eq))
    exact eq_of_heq (Sigma.mk.inj hv).2

private def post (m : ℕ) : B m ↪ B m × Fin 1 :=
  ⟨fun v => (v, 0), fun _ _ he => congrArg Prod.fst he⟩

private def traffic : Payload.Traffic (bank S r h) (S.payload r hx) 1 where
  E := B S.m
  src := post _
  dst := post _
  length := S.load r
  send := send h hx
  get _ := .refl _
  disjoint_send i j a b he hv := by
    change i = j at he
    subst j
    exact ⟨rfl, congrArg Fin.val ((send h hx i).injective (Fin.ext hv))⟩
  disjoint_get _ _ _ _ he hv := ⟨he, hv⟩
  covers i := ⟨i.1, i.2, rfl⟩

private theorem transfer (v : B S.m) (i : Fin (S.load r v)) :
    fromBank h hx ((traffic h hx).target v i) = (traffic h hx).source v i :=
  Sigma.ext (from_host h hx ⟨v, i⟩)
    ((Fin.heq_ext_iff (congrArg _ (from_host h hx ⟨v, i⟩))).mpr rfl)

private theorem matches_named (v : S.Pin r → Bool) (x : S.exposed r → Bool) :
    (traffic h hx).links.Matches (store S r h v) (S.store r hx x) ↔ ∀ i, v i.val = x i := by
  unfold store
  rw [(traffic h hx).matches_iff _ (transfer h hx)]
  have eq : Function.extend (place S r h) v (fun _ => false) ∘ fromBank h hx =
      (fun i : S.exposed r => v i.val) ∘ (S.index r hx).symm := by
    funext i
    exact (place S r h).injective.extend_apply _ _ _
  rw [eq]
  change S.store r hx x = S.store r hx _ ↔ _
  constructor
  · intro he i
    simpa using congrFun he.symm (S.wire r hx i)
  · intro he; rw [funext he]

variable (a : SpanPlan.Entries S.m w z S.spanRows) (b : SpanPlan.Entries S.m w 0 S.spanRows)
  (hw : height S t < w) (hw' : k' < w)
  (ha : Lengths S r t a) (hb : ∀ i j, (b i j).2.1.val = S.extent r i j)
  (ho : ∀ i j, (b i j).2.2 = j)
include hw hw' ha hb ho

private theorem valid : Payload.Script.Valid (traffic h hx) le_rfl (script (a, b)) := by
  let l := fun i => outgoing (a i) (b i)
  let u := SpanPlan.offsets ∘ b
  have hl : Aligned S r l := ⟨hb, ho⟩
  have hu : Aligned S r u := ⟨hb, ho⟩
  have total (v : B S.m) : (SpanPlan.total (b v)).val = S.load r v := by
    rw [SpanPlan.total_val _ (hu.small hx hw' v)]
    simp only [hb, S.load_eq]
  have src (i : S.exposed r) :
      Payload.Script.At (SpanPlan.pack (l (S.owner r i))).2 0 (S.index r hx i).2.val
        (place S r h i.val).2.val := by
    have H := hl.at_bit hx hw' i
    change Payload.Script.At _ _ _
      (SpanPlan.offset (SpanPlan.offsets (a i.val.1.1.1)) (S.spanIndex i.val.1) + i.val.2.val) at H
    rw [ha.offset h hw i.val.1] at H
    change Payload.Script.At _ _ _ (index S r h (pin S r h i.val)).2.val
    rw [index_val]
    exact H
  have dst (i : S.exposed r) : Payload.Script.At (SpanPlan.pack (u (S.owner r i))).2 0
      (S.index r hx i).2.val (S.index r hx i).2.val := by
    have he : SpanPlan.offset (u (S.owner r i)) (S.spanIndex i.val.1) =
        S.start r (S.owner r i) (S.spanIndex i.val.1) := by
      refine (SpanPlan.offset_val _ (hu.small hx hw' _) _).trans ?_
      simp only [hb, Scheme.start]
    have hh := hu.at_bit hx hw' i
    dsimp only at hh
    rwa [he, ← S.index_val r hx i] at hh
  refine ⟨?_, fun i => SpanPlan.bounds (l i) (hl.fits hx hw' _) (hl.unique _),
    fun i => SpanPlan.bounds (u i) (hu.fits hx hw' _) (hu.unique _), ?_, ?_⟩
  · exact ⟨ha.total h hw, total, hl.length hx hw', hu.length hx hw',
      fun i j _ => ⟨i, rfl, (zero j).symm⟩, fun i j _ => ⟨i, rfl, (zero j).symm⟩, fun _ _ => rfl⟩
  · intro v j
    let i := (S.index r hx).symm ⟨v, j⟩
    have hi : S.index r hx i = ⟨v, j⟩ := (S.index r hx).apply_symm_apply _
    have hv : S.owner r i = v := congrArg Sigma.fst hi
    have he := src i
    rw [hi, hv] at he
    exact he
  · intro v j
    let i := (S.index r hx).symm ⟨v, j⟩
    have hi : S.index r hx i = ⟨v, j⟩ := (S.index r hx).apply_symm_apply _
    have hv : S.owner r i = v := congrArg Sigma.fst hi
    have he := dst i
    rw [hi, hv] at he
    exact he

/-- The one-port script reads only exterior bits from the padded
argument bank, in the order of the original exterior payload. -/
theorem correct (v : S.Pin r → Bool) (x : S.exposed r → Bool) :
    (PeerLayout.S S.m V (height S t) S.m V' k' 1).Carries
      (Payload.Script.decode le_rfl (script (a, b))) (store S r h v) (S.store r hx x) ↔
      ∀ i, v i.val = x i :=
  ((valid h hx a b hw hw' ha hb ho).carries _ _).trans (matches_named h hx v x)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
end

/-! # Span records for the two terminal transfers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical
variable {F : Type} (S : Scheme F) (r : S.format.obj)

def path (s : S.Span) : Option (B S.d) :=
  if (partner S r s).1.1 = s.1.1 then none else ((S.pattern r s.1).peer s.1.2.2 s.2).map Prod.fst

private theorem path_link {s q : S.Span} (h : partner S r s = q) (ne : s.1.1 ≠ q.1.1) :
    ∃ i, path S r s = some i ∧ (r s.1.1).1 i = q.1.1 := by
  rcases partner_cases S r s with e|⟨a, _⟩
  · exact (ne (congrArg (fun p => p.1.1) (e.symm.trans h))).elim
  rw [h, Scheme.peer] at a
  cases b : (S.pattern r s.1).peer s.1.2.2 s.2 with
  | none => simp [b] at a
  | some v =>
    rw [b, Option.map_some, Option.some.injEq] at a
    exact ⟨v.1, by simp only [path, h, ite_eq_right ne.symm, b, Option.map_some], congrArg (fun p => p.1.1) a⟩

private theorem route (proper : S.Proper r) (hr : Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) r) (s : S.Span) :
    perm S r (contact S s.1.1 (path S r s)) =
      contact S (partner S r s).1.1 (path S r (partner S r s)) := by
  have inv := partner_inv S r proper s
  by_cases he : s.1.1 = (partner S r s).1.1
  · simp only [path, inv, ← he, ite_true, perm_self]
  · obtain ⟨i, hi, hi'⟩ := path_link S r rfl he
    obtain ⟨j, hj, hj'⟩ := path_link S r inv (Ne.symm he)
    rw [hi, hj]
    exact perm_link S r hr _ _ _ _ he hi' hj'

abbrev flanks (w : ℕ) := SpanPlan.Entries S.m w (S.d + 1) S.spanRows

def send (S : Scheme F) (t w : ℕ) (r : S.format.obj) : flanks S w := fun i j =>
  let s := S.hostSpan (i, j)
  (hop (path S r s), Fin.ofNat _ (chunk S r t s), S.spanIndex (partner S r s))

def take (S : Scheme F) (t w : ℕ) (r : S.format.obj) : flanks S w := fun i j =>
  let s := S.hostSpan (i, j)
  (hop (path S r s), Fin.ofNat _ (chunk S r t s), j)

def outer (S : Scheme F) (w : ℕ) (r : S.format.obj) : SpanPlan.Entries S.m w 0 S.spanRows :=
  fun i j => (0, Fin.ofNat _ (S.extent r i j), j)

theorem inner_plan (proper : S.Proper r) (hr : Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) r)
    {t w : ℕ} (ht : t < w) : Inner S r t (perm S r) (send S t w r) (take S t w r) where
  bij := (perm_involutive S r hr).bijective
  lengths s := by
    simp only [send, Scheme.hostSpan_spanIndex]
    have le : chunk S r t s ≤ 2 ^ t := by unfold chunk; split <;> simp
    exact Nat.mod_eq_of_lt (le.trans_lt (Nat.pow_lt_pow_right (by decide) ht))
  paired s := by simp only [send, take, Scheme.hostSpan_spanIndex]
  order _ := rfl
  contacts s _ := by
    simp only [endpoint, send, take, Scheme.hostSpan_spanIndex]
    exact route S r proper hr s

theorem outer_length {V t w : ℕ} (h : Fits S r V t) (ht : t < w) (i : B S.m) (j : B S.spanRows) :
    (outer S w r i j).2.1.val = S.extent r i j := by
  have he : S.extent r i j ≤ 2 ^ t := by
    dsimp only [Scheme.extent]
    split
    · exact h.width _
    · exact Nat.zero_le _
  exact Nat.mod_eq_of_lt (he.trans_lt (Nat.pow_lt_pow_right (by decide) ht))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! # Terminal commands and station headers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal

variable {F : Type} (S : Scheme F) (V t w : ℕ)

def orders (r : S.format.obj) : (instruction S V t (S.d + 1) w S.spanRows).obj :=
  ((SpanPlan.emit (perm S r) (send S t w r, take S t w r),
    Outer.script (send S t w r, outer S w r)), Header.eval S V t r)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# Preparing a terminal lane

The local table reads the short block label, lane index, and flags
indicating which neighbors are aliases of the same host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Prepare
open Coloring
open scoped Classical
variable {F : Type} (S : Scheme F) (t w : ℕ)

abbrev key := Format.pair (.addr S.spanRows) (.pair (.addr S.ℓ) (.vec S.d .bit))
abbrev answer := Format.pair (SpanPlan.header w (S.d + 1) S.spanRows)
    (.pair (SpanPlan.header w (S.d + 1) S.spanRows) (SpanPlan.header w 0 S.spanRows))

def get (r : S.format.obj) (b : (Flags S).obj) (s : S.Span) : (key S).obj :=
  (S.spanIndex s, (r s.1.1).2 s.1.2.1, b s.1.1)

def read (x : (key S).obj) : (answer S w).obj :=
  let s := S.hostSpan (0, x.1)
  let p := S.decode x.2.1
  let v := s.1.2.2
  let L := p.width v s.2
  let R := p.peer v s.2
  let A := if L = 0 then none else R
  let c := hop (A.bind fun i => if x.2.2 i.1 then none else some i.1)
  let j := A.elim x.1 fun i => S.spanIndex ((0, s.1.2.1, i.2.1), i.2.2)
  let n := Fin.ofNat (2 ^ w) (if Nonempty (Σ i, Fin (p.width v i)) then 2 ^ t else 0)
  ((c, n, j), (c, n, x.1), (0, Fin.ofNat _ (if R = none then L else 0), x.1))

theorem read_get (r : S.format.obj) (s : S.Span) :
    read S t w (get S r (flags S r) s) =
    (send S t w r s.1.1 (S.spanIndex s), take S t w r s.1.1 (S.spanIndex s),
      outer S w r s.1.1 (S.spanIndex s)) := by
  have he : S.hostSpan (0, S.spanIndex s) = ((0, s.1.2), s.2) := by
    exact S.hostSpan_spanIndex ((0, s.1.2), s.2)
  let R := (S.pattern r s.1).peer s.1.2.2 s.2
  let A := if S.width r s = 0 then none else R
  have hp : (A.bind fun i => if flags S r s.1.1 i.1 then none else some i.1) = path S r s := by
    unfold path partner
    by_cases h : S.width r s = 0
    · simp [A, h]
    unfold Scheme.peer
    simp only [A, R, h, ite_false]
    cases (S.pattern r s.1).peer s.1.2.2 s.2 <;> simp [flags]
  have hj : (A.elim (S.spanIndex s) fun i => S.spanIndex ((0, s.1.2.1, i.2.1), i.2.2)) =
      S.spanIndex (partner S r s) := by
    unfold partner
    by_cases h : S.width r s = 0
    · simp [A, h]
    unfold Scheme.peer
    simp only [A, R, h, ite_false]
    cases (S.pattern r s.1).peer s.1.2.2 s.2 <;> rfl
  have hR : R = none ↔ S.peer r s = none := by simp [R, Scheme.peer]
  simp only [read, get, he, send, take, outer, Scheme.extent, Scheme.hostSpan_spanIndex]
  simp only [← hp, ← hj, ← hR]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Prepare
end

/-! # Parallel span instructions from one shared lookup table -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Prepare
open Coloring
open scoped Classical
variable {F : Type} [Field F] (S : Scheme F) (t w : ℕ)

abbrev permFmt := Perm (S.m + (S.d + 1))
abbrev nav := (permFmt S).pair (Flags S)
abbrev input := S.format.pair (nav S)
abbrev grid (A : Format) := (permFmt S).pair (.vec S.m (.vec S.spanRows A))
abbrev source := grid S (key S)
abbrev target := grid S (answer S w)

def query (x : (input S).obj) : (source S).obj :=
  (x.2.1, fun i j => get S x.1 x.2.2 (S.hostSpan (i, j)))

def plan (r : S.format.obj) : (target S w).obj :=
  (perm S r, fun i j => (send S t w r i j, take S t w r i j, outer S w r i j))

def arity := (key S).width + (answer S w).width

def label : Table F := lookup F (key S) (answer S w) (fun x y => @ite F (read S t w x = y) (Classical.propDecidable _) 1 0)

def cost (n : ℕ) :=
  4 * (5 * S.format.width + S.format.width + n + ((input S).width + 34 * (source S).width)) +
    (4 * (permFmt S).width + 2 ^ S.m * (2 ^ S.spanRows * (1 + (key S).width + (answer S w).width)))

private theorem query_net : Circuit F (input S) (source S) (query S)
    ((input S).width + 34 * (source S).width) := by
  apply Window.Tile.project_const
  rintro (i | ⟨i, j, k|k|k⟩)
  · exact .inl ⟨.inr (.inl i), fun _ => rfl⟩
  · exact .inr ⟨(Format.addr S.spanRows).code (S.spanIndex (S.hostSpan (i, j))) k, fun _ => rfl⟩
  · exact .inl ⟨.inl (i, .inr ((S.hostSpan (i, j)).1.2.1, k)), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inr (i, k)), fun _ => rfl⟩

theorem realize {u n : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    (ha : arity S w ≤ u) (hl : label S t w ∈ L)
    (hn : Circuit F S.format (nav S) (fun r => (perm S r, flags S r)) n) :
    Map F u L S.format (target S w) (plan S t w) (cost S w n) := by
  have a := ((Circuit.id F S.format).pair hn).comp (query_net S)
  have b : Map F u L (key S) (answer S w) (read S t w) (1 + (key S).width + (answer S w).width) :=
    Kernel.lookup ha hl
  have c := (Map.circuit (L:=L) hu (Circuit.id F (permFmt S))).par
    (Map.vec _ fun _ : B S.m => Map.vec _ fun _ : B S.spanRows => b)
  have h := (Map.circuit hu a).comp c
  have e : (fun r => (perm S r, fun i j => read S t w (get S r (flags S r) (S.hostSpan (i, j))))) =
      plan S t w := by
    funext r
    refine Prod.ext rfl ?_
    funext i j
    simpa only [plan, Scheme.spanIndex_hostSpan, Scheme.hostSpan_owner] using read_get S t w r (S.hostSpan (i, j))
  rw [← e]
  exact h

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Prepare
end

/-! # The three shared terminal lookup tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical
variable {F : Type} [Field F] (S : Scheme F) (t w : ℕ)

def labels : Finset (Table F) := {Dictionary.label S t, Header.label S, Prepare.label S t w}

theorem labels_card : (labels S t w).card ≤ 3 := by
  unfold labels
  have := Finset.card_insert_le (Header.label S) {Prepare.label S t w}
  have := Finset.card_insert_le (Dictionary.label S t) {Header.label S, Prepare.label S t w}
  simp only [Finset.card_singleton] at *
  omega

def arity := Dictionary.arity S t + Header.arity S + Prepare.arity S w

theorem arity_le (i : Rates.Size) : arity i.S i.t i.w ≤ 2 ^ (i.S.e + i.t) + 64 * i.T := by
  simp only [arity, Dictionary.arity, Dictionary.header, Header.arity, Header.key, Prepare.arity,
    Prepare.key, Prepare.answer, SpanPlan.header]
  repeat' rw [Format.width_pair]
  rw [Format.width_vec, Format.width_bit, mul_one]
  repeat' rw [Format.width_addr]
  unfold Scheme.spanRows Rates.Size.w Rates.Size.T Rates.Size.B Rates.Size.k height
  have := Nat.lt_two_pow_self (n := i.S.d)
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! # Compiling both transfer scripts in parallel -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Prepare
open Coloring
variable {F : Type} (S : Scheme F) (t w : ℕ)
local notation "m" => S.m
local notation "z" => S.d + 1
local notation "n" => S.spanRows

abbrev both := (Emit.source m z w n).pair (Outer.input m z w n)
abbrev commands := (Payload.Script m m z w n).pair (Payload.Script m m 0 w n)

def separate (x : (target S w).obj) : (both S w).obj :=
  let a := fun i j => (x.2 i j).1
  ((x.1, a, fun i j => (x.2 i j).2.1), (a, fun i j => (x.2 i j).2.2))

def programs (r : S.format.obj) : (commands S w).obj :=
  (SpanPlan.emit (perm S r) (send S t w r, take S t w r), Outer.script (send S t w r, outer S w r))

def spending (c : ℕ) := cost S w c +
  4 * ((target S w).width + 2 * (both S w).width + (Emit.cost m z w n + Outer.cost m z w n))

variable [Field F]

private theorem divide : Circuit F (target S w) (both S w) (separate S w)
    ((target S w).width + 2 * (both S w).width) := by
  let e : (both S w).pins → (target S w).pins
    | .inl (.inl i) => .inl i
    | .inl (.inr (.inl (i, j, k))) => .inr (i, j, .inl k)
    | .inl (.inr (.inr (i, j, k))) => .inr (i, j, .inr (.inl k))
    | .inr (.inl (i, j, k)) => .inr (i, j, .inl k)
    | .inr (.inr (i, j, k)) => .inr (i, j, .inr (.inr k))
  exact Circuit.project e (by rintro _ ((i|i|i)|i|i) <;> rfl)

theorem scripts {u c : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    (ha : arity S w ≤ u) (hl : label S t w ∈ L)
    (hn : Circuit F S.format (nav S) (fun r => (perm S r, flags S r)) c) :
    Map F u L S.format (commands S w) (programs S t w) (spending S w c) := by
  have send := (Emit.circuit m z w n F).par (Outer.circuit F m z w n)
  exact (realize S t w hu ha hl hn).comp (Map.circuit hu ((divide S w).comp send))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Prepare
end

/-! # Computing all the terminal instructions from the common records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical
variable (i : Rates.Size)

def orderCost := 20 * i.S.format.width + Prepare.spending i.S i.w (linkCost i.S) + i.header

theorem generate (hm : 1 ≤ i.S.m) (hi : i.S.m ≤ i.W.w) {u : ℕ} {L : Set (Table i.F)}
    (hu : 3 ≤ u) (ha : arity i.S i.t i.w ≤ u) (hl : (↑(labels i.S i.t i.w) : Set _) ⊆ L) :
    Map i.F u L i.S.format (instruction i.S i.V i.t i.p i.w i.n)
      (orders i.S i.V i.t i.w) (orderCost i) := by
  have hs : Prepare.arity i.S i.w ≤ u := by unfold arity at ha; omega
  have hh : Header.arity i.S ≤ u := by unfold arity at ha; omega
  obtain ⟨c, hc, tag⟩ := i.W.tag i.S.m i.v hm hi (Nat.le_add_left ..)
  have e : Header.cost i.S i.V i.t i.v c ≤ i.header := by
    unfold Rates.Size.header Rates.Size.c Header.cost Redistribute.cost
    gcongr
  have h₁ := Prepare.scripts i.S i.t i.w hu hs (hl (by simp [labels])) (links_net i.S)
  have h₂ := (Header.realize (V:=i.V) (t:=i.t) hu hh (hl (by simp [labels])) tag
    (Nat.le_add_right ..)).mono e
  exact Map.pair hu h₁ h₂

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

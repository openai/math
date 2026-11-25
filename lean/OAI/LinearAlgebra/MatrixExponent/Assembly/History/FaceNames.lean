import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
import OAI.LinearAlgebra.MatrixExponent.Packing.Budget
import OAI.LinearAlgebra.MatrixExponent.Packing.RestoreCost
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Packing.FieldLift
import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Runs

/-! # Retaining the original ordering of exposed spans -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {x y : Wire}

def boundaryEnd (G : Diagram F x y) : slots x ⊕ slots y ↪ G.End where
  toFun := Sum.map Sum.inl Sum.inl
  inj' := by rintro (i|i) (j|j) h <;> cases h <;> rfl

omit [Field F] in
theorem station_boundary (G : Diagram F x y) (i : slots x ⊕ slots y) :
    G.station (boundaryEnd G i) = portEnd G i := by cases i <;> rfl

namespace Scheme.Presentation
variable {S : Scheme F} {r : S.format.obj} {G : Diagram F x y} (p : S.Presentation r G)

abbrev BorderSpan := {q : G.V × B S.e //
  0 < S.width r (p.vertex q.1, q.2) ∧ S.peer r (p.vertex q.1, q.2) = none}

def borderWidth (q : p.BorderSpan) := S.width r (p.vertex q.val.1, q.val.2)

abbrev BorderBit := Σ q : p.BorderSpan, Fin (p.borderWidth q)

def borderPin (b : p.BorderBit) : S.Pin r := ⟨(p.vertex b.1.val.1, b.1.val.2), b.2⟩

private theorem injective : Function.Injective p.borderPin := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  obtain ⟨hs, ht⟩ := Sigma.mk.inj he
  obtain ⟨hv, hi⟩ := Prod.mk.inj hs
  have h : i = j := Subtype.ext (Prod.ext (p.vertex.injective hv) hi)
  subst j
  exact Sigma.ext rfl ht

theorem no_peer (e : G.End) :
    S.peer r (p.toSeating.ends e).1 = none ↔ e ∈ Set.range (boundaryEnd G) := by
  rcases e with (i|j)|(i|j)
  · exact iff_of_true (p.input i) ⟨.inl i, rfl⟩
  · refine iff_of_false (by rw [(p.internal j).1]; simp) ?_
    rintro ⟨_|_, h⟩ <;> cases h
  · exact iff_of_true (p.output i) ⟨.inr i, rfl⟩
  · refine iff_of_false (by rw [(p.proper _ _ (p.internal j).1).1]; simp) ?_
    rintro ⟨_|_, h⟩ <;> cases h

private theorem side_bijection :
    ∃ e : p.BorderBit ≃ slots x ⊕ slots y, ∀ b,
      p.toSeating.ends (boundaryEnd G (e b)) = p.borderPin b := by
  have ex (b : p.BorderBit) : ∃ t, p.toSeating.ends (boundaryEnd G t) = p.borderPin b := by
    let i := p.toSeating.ends.symm (p.borderPin b)
    have hp : S.peer r (p.toSeating.ends i).1 = none := by
      rw [show p.toSeating.ends i = p.borderPin b from p.toSeating.ends.apply_symm_apply _]
      exact b.1.property.2
    obtain ⟨t, ht⟩ := (p.no_peer i).mp hp
    exact ⟨t, p.toSeating.ends.eq_symm_apply.mp ht⟩
  choose f hf using ex
  have bij : Function.Bijective f := by
    constructor
    · intro i j he
      apply p.injective
      rw [← hf, ← hf, he]
    · intro i
      have cover (a : S.Pin r) (ha : S.peer r a.1 = none) : ∃ b, p.borderPin b = a := by
        obtain ⟨⟨v, n⟩, j⟩ := a
        obtain ⟨w, rfl⟩ := p.cover ⟨(v, n), j⟩
        exact ⟨⟨⟨(w, n), j.pos, ha⟩, j⟩, rfl⟩
      obtain ⟨b, hb⟩ := cover _ ((p.no_peer _).mpr ⟨i, rfl⟩)
      exact ⟨b, (boundaryEnd G).injective (p.toSeating.ends.injective ((hf b).trans hb))⟩
  exact ⟨Equiv.ofBijective f bij, hf⟩

def exteriorBits : p.BorderBit ≃ slots x ⊕ slots y := p.side_bijection.choose

theorem border_pin (b : p.BorderBit) :
    p.toSeating.ends (boundaryEnd G (p.exteriorBits b)) = p.borderPin b :=
  p.side_bijection.choose_spec b

theorem border_station (b : p.BorderBit) : portEnd G (p.exteriorBits b) = b.1.val.1 := by
  have he (i : G.End) : p.vertex (G.station i) = (p.toSeating.ends i).1.1 := by
    obtain ⟨⟨v, j⟩, rfl⟩ := G.portEquiv.surjective i
    rw [G.station_port, p.toSeating.ends_at]
    rfl
  apply p.vertex.injective
  rw [← station_boundary, he, p.border_pin]
  rfl

end Scheme.Presentation
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Anchors for a local history

Slots of an old table, a matched gadget or an unmatched equality
constraint are identified before the contraction. This lets a
short description name slots by bundle and offset.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
open Packing Classical

variable {F V E : Type} [Field F] [Fintype V] [Fintype E] {a b : Wire}
  {N C : V → Finset V} {Δ D h k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l) {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (P : Gadget F) {G : Diagram F a b} {z : ℕ}
  (s : Bundles G src dst ix (P.b * z)) (hz : 0 < z) (i : g.Choice m P)

abbrev before := G.expanded (g.expansion m P s hz) i

abbrev cluster :=
  (before g m P s hz i).partition (Sum.elim (g.assign m P s i) (g.locate m (g.layout m P i)))

def old : G.End → (before g m P s hz i).End
  | .inl t => .inl (t.map id Sum.inl)
  | .inr t => .inr (t.map id (fun e => .inr (.inl e)))

def left (e : G.E) : (before g m P s hz i).End := .inr (.inr (.inl e))
def right (e : G.E) : (before g m P s hz i).End := .inl (.inr (.inr (.inl e)))

def supply (v : g.Parties m) (j : g.Supply m P i × Fin z) : (before g m P s hz i).End :=
  if (g.supplies m j.1).1 = v then .inl (.inr (.inr (.inr j))) else .inr (.inr (.inr (.inr j)))

variable (w : Bit (cluster g m P s hz i) → Bool)

abbrev read := w ∘ address (cluster g m P s hz i)

theorem old_factor (v : G.V) :
    factor (cluster g m P s hz i) (.inl v) w =
      Transcript.sample (G.table v) (read g m P s hz i w ∘ old g m P s hz i ∘ named G v) := by
  rw [factor, Diagram.weight_expanded]
  unfold Diagram.Expansion.entry Diagram.weight Transcript.sample
  apply congrArg₂ (G.table v).2.2 <;> apply congrArg <;> funext t
  · change Sum.elim _ _ (G.src ⟨v, t⟩) = read g m P s hz i w (old g m P s hz i (.inl (G.src ⟨v, t⟩)))
    cases G.src ⟨v, t⟩ <;> rfl
  · change Sum.elim _ _ (G.dst ⟨v, t⟩) = read g m P s hz i w (old g m P s hz i (.inr (G.dst ⟨v, t⟩)))
    cases G.dst ⟨v, t⟩ <;> rfl

theorem new_factor (v : g.Parties m) :
    factor (cluster g m P s hz i) (.inr v) w =
      (g.expansion m P s hz).entry i v (read g m P s hz i w ∘ left g m P s hz i)
        (read g m P s hz i w ∘ right g m P s hz i) (read g m P s hz i w ∘ supply g m P s hz i v) := by
  rw [factor, Diagram.weight_expanded]
  unfold Diagram.Expansion.entry
  apply congrArg ((g.expansion m P s hz).entry i v (read g m P s hz i w ∘ left g m P s hz i)
    (read g m P s hz i w ∘ right g m P s hz i))
  funext j
  unfold supply
  simp only [Function.comp_apply]
  split_ifs <;> rfl

def original (e : m.items) (q : Fin 2 × Fin (P.b * z)) :=
  s.bits.symm (m.pairEdge (e, q.1), q.2)

def inserted (e : m.items) (r : Σ j : Fin 8, Fin ((i e).2.1 j * z)) : g.Supply m P i × Fin z :=
  (.inl ⟨e, r.1, (finProdFinEquiv.symm r.2).1⟩, (finProdFinEquiv.symm r.2).2)

theorem paired_factor (e : m.items) (j : Fin 6) :
    factor (cluster g m P s hz i) (.inr (.inl ⟨e, j⟩)) w =
      (P.packet z hz).rule.entry (i e) j
        (read g m P s hz i w ∘ left g m P s hz i ∘ original g m P s e)
        (read g m P s hz i w ∘ right g m P s hz i ∘ original g m P s e)
        (read g m P s hz i w ∘ supply g m P s hz i (.inl ⟨e, j⟩) ∘ inserted g m P i e) := by
  rw [new_factor, g.expansion_pair]
  rfl

def carry (r : m.unpaired × Fin (P.b * z)) : g.Supply m P i × Fin z :=
  (.inr (r.1, (finProdFinEquiv.symm r.2).1), (finProdFinEquiv.symm r.2).2)

theorem unpaired_factor (v : V × Cell h) :
    factor (cluster g m P s hz i) (.inr (.inr v)) w =
      Spectral.Packet.checkAt F (fun r : m.unpaired × Fin (P.b * z) => (src r.1, ix r.1)) v
        (fun r => read g m P s hz i w (left g m P s hz i (s.bits.symm (r.1, r.2))))
        (read g m P s hz i w ∘ supply g m P s hz i (.inr v) ∘ carry g m P i) *
      Spectral.Packet.checkAt F (fun r : m.unpaired × Fin (P.b * z) => (dst r.1, ix r.1)) v
        (fun r => read g m P s hz i w (right g m P s hz i (s.bits.symm (r.1, r.2))))
        (read g m P s hz i w ∘ supply g m P s hz i (.inr v) ∘ carry g m P i) := by
  rw [new_factor, g.expansion_single]
  rfl

theorem unpaired_idle (v : V × Cell h) (hs : ∀ e : m.unpaired, (src e, ix e) ≠ v)
    (ht : ∀ e : m.unpaired, (dst e, ix e) ≠ v) :
    factor (cluster g m P s hz i) (.inr (.inr v)) w = 1 := by
  rw [unpaired_factor]
  simp [Spectral.Packet.checkAt, hs, ht]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
end

/-!
# Hidden spans of a wire-saving subround

The two halves of each old bundle are internal at their own station.
A supply bundle is internal only if its two parties have merged.
Both kinds retain their original offset ordering.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround

open Packing
open scoped Classical

variable {F V E : Type} [Field F] [Fintype V] [Fintype E] {a b : Wire}
  {N C : V → Finset V} {Δ D h k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l) {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (P : Gadget F) {G : Diagram F a b} {z : ℕ}
  (s : Bundles G src dst ix (P.b * z)) (hz : 0 < z) (i : g.Choice m P)

abbrev Segment := E ⊕ E ⊕ g.Supply m P i

def segmentWidth (z : ℕ) : Segment g m P i → ℕ
  | .inl _ | .inr (.inl _) => P.b * z
  | .inr (.inr _) => z

def ends : Segment g m P i → Site V h × Site V h
  | .inl e => let v := g.route m (g.layout m P i) (src e) (ix e); (v, v)
  | .inr (.inl e) => let v := g.route m (g.layout m P i) (dst e) (ix e); (v, v)
  | .inr (.inr e) => g.contact m (g.layout m P i) e

def segmentBits : (Σ j, Fin (segmentWidth g m P i z j)) ≃ (before g m P s hz i).E :=
  let e := (Equiv.sigmaEquivProd E (Fin (P.b * z))).trans s.bits.symm
  (Equiv.sumSigmaDistrib _).trans (e.sumCongr
    ((Equiv.sumSigmaDistrib _).trans (e.sumCongr (Equiv.sigmaEquivProd _ (Fin z)))))

theorem endpoints (j : Σ q, Fin (segmentWidth g m P i z q)) :
    let D := before g m P s hz i
    let H := cluster g m P s hz i
    let e := segmentBits g m P s hz i j
    (H.owner (D.source e), H.owner (D.target e)) = ends g m P i j.1 := by
  let col := g.layout m P i
  have old (e : E × Fin (P.b * z)) :
      g.assign m P s i (G.source (s.bits.symm e)) = g.route m col (src e.1) (ix e.1) ∧
      g.assign m P s i (G.target (s.bits.symm e)) = g.route m col (dst e.1) (ix e.1) := by
    simp only [Grouping.assign, s.left, s.right, Equiv.apply_symm_apply, col, and_self]
  rcases j with ⟨j|j|j, t⟩
  · let e : E × Fin (P.b * z) := (j, t)
    change (g.assign m P s i (G.source (s.bits.symm e)),
      g.locate m col (g.demand m (s.bits (s.bits.symm e))).1) = _
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (old e).1 (congrArg Prod.fst (g.locate_demand m col e))
  · let e : E × Fin (P.b * z) := (j, t)
    change (g.locate m col (g.demand m (s.bits (s.bits.symm e))).2,
      g.assign m P s i (G.target (s.bits.symm e))) = _
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (congrArg Prod.snd (g.locate_demand m col e)) (old e).2
  · exact g.locate_supply m col j

abbrev Hidden (v : Site V h) := {q : Segment g m P i // ends g m P i q = (v, v)}

def hiddenBits (v : Site V h) :
    (Σ j : Hidden g m P i v, Fin (segmentWidth g m P i z j.val)) ≃
      (cluster g m P s hz i).hidden v := by
  let D := before g m P s hz i
  let H := cluster g m P s hz i
  let E := segmentBits g m P s hz i
  let f (j : Σ j : Hidden g m P i v, Fin (segmentWidth g m P i z j.val)) := E ⟨j.1.val, j.2⟩
  have he (j : Σ j : Hidden g m P i v, Fin (segmentWidth g m P i z j.val)) :
      H.owner (D.source (f j)) = v ∧ H.owner (D.target (f j)) = v :=
    Prod.mk.inj ((endpoints g m P s hz i _).trans j.1.property)
  refine Equiv.ofBijective (fun j => ⟨⟨f j, (he j).1.trans (he j).2.symm⟩, (he j).1⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨q, hq⟩, t⟩ ⟨⟨r, hr⟩, u⟩ hh
    have eq := E.injective (congrArg (fun x => x.val.val) hh)
    cases eq
    rfl
  · rintro ⟨⟨j, hj⟩, hv⟩
    obtain ⟨⟨q, t⟩, rfl⟩ := E.surjective j
    have ht : ends g m P i q = (v, v) :=
      (endpoints g m P s hz i ⟨q, t⟩).symm.trans (Prod.ext hv (hj.symm.trans hv))
    exact ⟨⟨⟨q, ht⟩, t⟩, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
end

/-!
# Exposed spans of a contracted station

A surviving unit supplies one new span at each end. The old exterior
spans keep all their own offsets. These are exactly the arguments of
the new station, up to reordering.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround

open Packing
open scoped Classical

def endIndex {F : Type} {a b : Wire} (G : Diagram F a b) :
    (slots a ⊕ slots b) ⊕ (G.E × Bool) ≃ G.End where
  toFun
    | .inl p => boundaryEnd G p
    | .inr (e, t) => cond t (.inr (.inr e)) (.inl (.inr e))
  invFun
    | .inl (.inl p) => .inl (.inl p)
    | .inr (.inl p) => .inl (.inr p)
    | .inl (.inr e) => .inr (e, false)
    | .inr (.inr e) => .inr (e, true)
  left_inv := by rintro ((_|_)|⟨_, _|_⟩) <;> rfl
  right_inv := by rintro ((_|_)|(_|_)) <;> rfl

variable {F V E : Type} [Field F] [Fintype V] [Fintype E] {a b : Wire}
  {N C : V → Finset V} {Δ D h k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l) {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (P : Gadget F) {G : Diagram F a b} {z : ℕ}
  (s : Bundles G src dst ix (P.b * z)) (hz : 0 < z) (i : g.Choice m P)
  {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G)

abbrev Face := p.BorderSpan ⊕ (g.Survivors m P i × Bool)

def visibleWidth (z : ℕ) : Face g m P i p → ℕ := Sum.elim p.borderWidth (fun _ => z)

def whereAt : Face g m P i p → Site V h
  | .inl q => g.assign m P s i q.val.1
  | .inr (e, t) => cond t (g.ends' m P i e).2 (g.ends' m P i e).1

def faceBits : (Σ q, Fin (visibleWidth g m P i p z q)) ≃ (g.contract m P s hz i).End :=
  let swap : (g.Survivors m P i × Bool) × Fin z ≃ (g.Survivors m P i × Fin z) × Bool :=
    ⟨fun q => ((q.1.1, q.2), q.1.2), fun q => ((q.1.1, q.2), q.1.2), fun _ => rfl, fun _ => rfl⟩
  let cut := ((Equiv.sigmaEquivProd _ _).trans swap).trans
    ((g.remaining m P s hz i).prodCongr (Equiv.refl Bool))
  ((Equiv.sumSigmaDistrib _).trans (p.exteriorBits.sumCongr cut)).trans (endIndex _)

theorem face_location (q : Σ j, Fin (visibleWidth g m P i p z j)) :
    (g.contract m P s hz i).station (faceBits g m P s hz i p q) = whereAt g m P s i p q.1 := by
  rcases q with ⟨q|⟨e, t⟩, j⟩
  · let b : p.BorderBit := ⟨q, j⟩
    have he (b : slots a ⊕ slots _) :
        (g.contract m P s hz i).station (boundaryEnd _ b) = g.assign m P s i (portEnd G b) := by
      cases b <;> rfl
    exact (he (p.exteriorBits b)).trans (congrArg _ (p.border_station b))
  · have he := g.contact_contract m P s hz i (e, j)
    cases t
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

abbrev Visible (v : Site V h) := {q : Face g m P i p // whereAt g m P s i p q = v}

def visibleBits (v : Site V h) :
    (Σ q : Visible g m P s i p v, Fin (visibleWidth g m P i p z q.val)) ≃
      (g.contract m P s hz i).Port v := by
  let D := g.contract m P s hz i
  let e := faceBits g m P s hz i p
  let f (j : Σ q : Visible g m P s i p v, Fin (visibleWidth g m P i p z q.val)) :
      {q : D.End // D.station q = v} :=
    ⟨e ⟨j.1.val, j.2⟩, (face_location g m P s hz i p _).trans j.1.property⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).trans (D.incident v).symm
  · rintro ⟨⟨q, hq⟩, t⟩ ⟨⟨r, hr⟩, u⟩ hh
    have eq := e.injective (congrArg Subtype.val hh)
    cases eq
    rfl
  · rintro ⟨j, hj⟩
    obtain ⟨⟨q, t⟩, rfl⟩ := e.surjective j
    have hq := (face_location g m P s hz i p ⟨q, t⟩).symm.trans hj
    exact ⟨⟨⟨q, hq⟩, t⟩, rfl⟩

theorem visible_pin (v : Site V h) (j : Σ q : Visible g m P s i p v,
    Fin (visibleWidth g m P i p z q.val)) :
    named (g.contract m P s hz i) v (visibleBits g m P s hz i p v j) =
      faceBits g m P s hz i p ⟨j.1.val, j.2⟩ := by
  let D := g.contract m P s hz i
  change ((D.incident v) ((D.incident v).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
end

/-! # Positive occurrences contain a whole unit or a full tether span -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
open Finset
open scoped Classical

variable {T F : Type} {x y : Wire} {L : Fringe x y T} {h u : ℕ}
  (G : HostNet F L h u)

theorem parallel_le_tether (i : slots x ⊕ slots y) : G.parallelBits i ≤ G.tetherLoad (G.far i) := by
  let _ : DecidableEq (G.V × Cell h) := Classical.typeDecidableEq _
  apply (Nat.cast_le (α := ℝ)).mp
  rw [tetherLoad, port_load]
  change (G.parallelBits i : ℝ) ≤ push G.far (fun _ => 1) (G.far i)
  simp only [parallelBits, Fintype.card_subtype, push, sum_boole, Nat.cast_le]
  apply card_le_card
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact hj.2

theorem incident_floor [Fintype T] (p : G.V × Cell h) (i : G.E)
    (hi : (G.pair i).1 = p ∨ (G.pair i).2 = p) : (u : ℝ) ≤ G.load p.1 p.2 := by
  have hd : 1 ≤ degree G.pair p := by
    rw [degree_sum]
    apply le_trans _ (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i))
    rcases hi with hi|hi <;> simp [arityCost, hi]
  have hh : (u : ℝ) ≤ (degree G.pair p : ℝ) * u :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast hd)
  exact hh.trans ((le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load _ _))

theorem station_floor [Fintype T] (contacts : ∀ i, u ≤ G.tetherLoad (G.far i))
    (v : G.diagram.V) (hv : 0 < G.diagram.arity v) :
    (u : ℝ) ≤ G.load (G.units.place v).1 (G.units.place v).2 := by
  let p := G.units.place v
  have port (i : slots x ⊕ slots y) (hi : portEnd G.diagram i = v) :
      (u : ℝ) ≤ G.load p.1 p.2 := by
    have hs : G.far i = p := congrArg G.units.place hi
    have hh := contacts i
    rw [hs] at hh
    exact (Nat.cast_le.mpr hh).trans
      ((le_add_of_nonneg_right (by positivity)).trans (G.core_le_load _ _))
  rw [← G.diagram.degree] at hv
  obtain ⟨⟨q, hq⟩⟩ := Fintype.card_pos_iff.mp hv
  rcases q with (i|e)|(i|e)
  · exact port (.inl i) hq
  · exact G.incident_floor p _ (.inl ((G.units.left e).symm.trans (congrArg G.units.place hq)))
  · exact port (.inr i) hq
  · exact G.incident_floor p _ (.inr ((G.units.right e).symm.trans (congrArg G.units.place hq)))

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-!
# Counting the active atoms at a contracted station

A nonempty old station and an unmatched equality constraint each
consume at least one unit of the old load. Each role of a matched
gadget charges to a distinct wire incidence. Scalar stations may
instead be evaluated when their last port is removed.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
open Finset
open scoped Classical

private theorem sum_embedding {A B : Type} [Fintype A] [Fintype B]
    (e : A ↪ B) (f : B → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i, f (e i) ≤ ∑ i, f i := by
  rw [← sum_map univ e]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hf i)

variable {T F : Type} [Fintype T] {x y : Wire} {L : Fringe x y T} {h u : ℕ}
  (G : HostNet F L h u)
  {Δ D k : ℕ} {B : ℝ} (g : Grouping G.N G.C Δ D k B G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix)

abbrev Atom := G.diagram.V ⊕ g.Parties m

def live : G.Atom g m → Prop
  | .inl v => 0 < G.diagram.arity v
  | .inr (.inl _) => True
  | .inr (.inr p) => ∃ i : m.unpaired, (G.pair i.val).1 = p ∨ (G.pair i.val).2 = p

def receipt (col : Bool) : G.Atom g m → G.V × Cell h
  | .inl v => G.units.place v
  | .inr (.inl q) => g.rep m col q.1 q.2
  | .inr (.inr p) => p

def anchor (col : Bool) (i : G.Atom g m) :=
  let p := G.receipt g m col i
  g.route m col p.1 p.2

def roleCode (col : Bool) : Fin 6 → Fin 2 × Bool :=
  ![(0, false), (0, true), (1, false), (1, true),
    if col then (1, true) else (0, false), if col then (0, true) else (1, true)]

def via (col : Bool) (j : Fin 6) : m.items ↪ G.E where
  toFun i := m.pairEdge (i, (roleCode col j).1)
  inj' _ _ h := (Prod.mk.inj (m.pairEdge.injective h)).1

theorem role (col : Bool) (j : Fin 6) (i : m.items) :
    g.rep m col i j = cond (roleCode col j).2 (G.pair (G.via g m col j i)).2
      (G.pair (G.via g m col j i)).1 := by
  fin_cases j <;> cases col <;> rfl

def receipts (col : Bool) (z : Site G.V h) :=
  univ.filter fun i => G.live g m i ∧ G.anchor g m col i = z

theorem receipts_bound (contacts : ∀ i, u ≤ G.tetherLoad (G.far i))
    (one : Function.Injective G.units.place) (hB : 0 ≤ B) (col : Bool) (z : Site G.V h) :
    (G.receipts g m col z).card * (u : ℝ) ≤ 8 * (near G.C Δ z).card * ((2 : ℝ) ^ k * B) := by
  let f (t : G.V × Cell h) := g.route m col t.1 t.2
  let load t := if f t = z then G.load t.1 t.2 else 0
  let hit t := if f t = z then (u : ℝ) else 0
  let value (i : G.Atom g m) := if G.live g m i then hit (G.receipt g m col i) else 0
  have h₀ t : 0 ≤ load t := by unfold load; split_ifs <;> first | exact G.load_nonneg _ _ | rfl
  have h₁ t : 0 ≤ hit t := by unfold hit; split_ifs <;> positivity
  have hl t (ht : (u : ℝ) ≤ G.load t.1 t.2) : hit t ≤ load t := by
    unfold hit load; split_ifs <;> first | exact ht | rfl
  have old : ∑ v, value (.inl v) ≤ ∑ t, load t := by
    refine le_trans ?_ (sum_embedding ⟨G.units.place, one⟩ load h₀)
    apply sum_le_sum
    intro v _
    unfold value
    split_ifs with hv
    · exact hl _ (G.station_floor contacts v hv)
    · exact h₀ _
  have check : ∑ t, value (.inr (.inr t)) ≤ ∑ t, load t := by
    apply sum_le_sum
    intro t _
    unfold value
    split_ifs with ht
    · obtain ⟨e, he⟩ := ht
      exact hl _ (G.incident_floor _ _ he)
    · exact h₀ _
  let endpt (p : G.E × Bool) := cond p.2 (G.pair p.1).2 (G.pair p.1).1
  have all : ∑ i, hit (endpt i) ≤ ∑ t, load t := by
    have hb t : push endpt (fun _ => (u : ℝ)) t ≤ G.load t.1 t.2 := by
      rw [show push endpt _ t = degree G.pair t * (u : ℝ) from
        (degree_push (fun i s => endpt (i, s)) u t).symm]
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load _ _)
    unfold hit load
    rw [← test_push endpt (fun _ => (u : ℝ)) (fun t => f t = z)]
    exact sum_le_sum fun t _ => by split_ifs <;> first | exact hb t | rfl
  have gadget (j : Fin 6) : ∑ i, value (.inr (.inl ⟨i, j⟩)) ≤ ∑ t, load t := by
    let e := G.via g m col j
    let s := (roleCode col j).2
    have he := G.role g m col j
    let q : m.items ↪ G.E × Bool := ⟨fun i => (e i, s), fun _ _ eq => e.injective (Prod.mk.inj eq).1⟩
    refine le_trans ?_ ((sum_embedding q (fun i => hit (endpt i)) (fun i => h₁ _)).trans all)
    exact sum_le_sum fun i _ => by simp only [value, live, ite_true, receipt, he]; exact le_rfl
  have hsum : (∑ i, value i) ≤ 8 * (∑ t, load t) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma, sum_comm]
    have hh := sum_le_sum (s := univ) (fun j _ => gadget j)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hh
    linarith only [old, check, hh]
  have eq : (G.receipts g m col z).card * (u : ℝ) = ∑ i, value i := by
    simp only [receipts, ← nsmul_eq_mul, ← sum_const, sum_filter, ite_and]
    rfl
  rw [eq, mul_assoc]
  exact hsum.trans (mul_le_mul_of_nonneg_left (g.route_load m G.cs G.sub G.edge G.load_nonneg hB col z)
    (by norm_num))

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-! # Short names for wire ends across adjacent host positions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing
open scoped Classical

variable {F T : Type} {x y : Wire} {L : Fringe x y T} {h u : ℕ}

/-- The short names at a core occurrence need not be unique elsewhere. -/
structure Navigation (G : HostNet F L h u) (d w : ℕ) where
  one : Function.Injective G.units.place
  stub : G.E → Bool → B w
  separate : ∀ i j b, Scheme.side G i b = Scheme.side G j b → G.ix i = G.ix j →
    stub i b = stub j b → i = j
  slot : G.V → G.V → B d
  nav : G.V → B d → G.V
  back : ∀ i, nav (G.dst i) (slot (G.dst i) (G.src i)) = G.src i

namespace Scheme.Posting
variable [Field F] {S : Scheme F} {r : S.format.obj} {G : HostNet F L h u}
  (p : S.Posting r G) (hu : 0 < u)

include hu

theorem return_target (i : G.E) :
    (r (p.host (G.dst i))).1 (p.index (G.dst i) (G.src i)) = p.host (G.src i) := by
  let t : Fin u := ⟨0, hu⟩
  have he := (p.internal (G.units.bits.symm (i, t))).1
  change S.peer r (p.toSeating.ends (endBit G i false t)).1 =
    some (p.toSeating.ends (endBit G i true t)).1 at he
  rw [(p.ordered _ _ _).1, (p.ordered _ _ _).1] at he
  have ht := (p.proper _ _ he).1
  rw [peer, p.link] at ht
  exact congrArg (fun q : S.Span => q.1.1) (Option.some.inj ht)

theorem return_nav (i : G.E) : p.nav (G.dst i) (p.index (G.dst i) (G.src i)) = G.src i := by
  have hh : ∃ w, p.host w = (r (p.host (G.dst i))).1 (p.index (G.dst i) (G.src i)) :=
    ⟨G.src i, (p.return_target hu i).symm⟩
  rw [nav, dite_eq_left hh]
  exact p.host.injective (hh.choose_spec.trans (p.return_target hu i))

theorem stub_unique (i j : G.E) (b : Bool) (hs : side G i b = side G j b)
    (hb : G.ix i = G.ix j) (he : p.stub i b = p.stub j b) : i = j := by
  have eq : p.span i b = p.span j b := by simp only [span, spanAt, hs, hb, he]
  cases b
  · exact p.distinct hu eq
  · let t : Fin u := ⟨0, hu⟩
    have peer (i : G.E) : S.peer r (p.span i true) = some (p.span i false) := by
      have he := (p.internal (G.units.bits.symm (i, t))).1
      change S.peer r (p.toSeating.ends (endBit G i false t)).1 =
        some (p.toSeating.ends (endBit G i true t)).1 at he
      rw [(p.ordered _ _ _).1, (p.ordered _ _ _).1] at he
      exact (p.proper _ _ he).1
    exact p.distinct hu (Option.some.inj ((peer i).symm.trans ((congrArg _ eq).trans (peer j))))

def navigation (a : ℕ) (ha : a ≤ h) : Navigation (G.regroup a ha) S.d S.e where
  one v w eq := by
    have ht := (splitAddr G.V a ha).injective eq
    apply p.vertex.injective
    change G.diagram.V at v w
    rw [p.vertex_eq, p.vertex_eq, ht]
  stub := p.stub
  separate i j b hv hx he := by
    have ht : (side G i b, ancestor ha (G.ix i)) = (side G j b, ancestor ha (G.ix j)) := by
      cases b <;> exact hv
    exact p.stub_unique hu _ _ b (Prod.mk.inj ht).1
      ((splitCell a ha).injective (Prod.ext (Prod.mk.inj ht).2 hx)) he
  slot v w := p.index v.1 w.1
  nav := p.groupNav a
  back i := Prod.ext (p.return_nav hu i) rfl

end Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Local identifiers inside a contracted cell

An atom is specified by a reverse hop to the occurrence that paid for
it, its block, and either a station tag, a gadget role and stub, or
an equality tag. The same short names can be reused at other cells.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
open Coloring Packing HostNet
open scoped Classical

abbrev Role (w : ℕ) := Unit ⊕ (B w × Fin 6) ⊕ Unit
abbrev AtomKey (d w h : ℕ) := (Option (B d) × B h) × Role w

variable {T F : Type} [Fintype T] {x y : Wire} {L : Fringe x y T} {h u d w : ℕ}
  {G : HostNet F L h u} (p : Navigation G d w)
  {Δ D k : ℕ} {B' : ℝ} (g : Grouping G.N G.C Δ D k B' G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (col : Bool)

def reverse (v v' : G.V) : Option (B d) :=
  if v = v' then none else some (p.slot v v')

def recover (v : G.V) (i : Option (B d)) := i.elim v (p.nav v)

theorem recover_reverse (v : G.V) (b : Cell h) :
    let z := (g.route m col v b).1
    p.recover z (p.reverse z v) = v := by
  rcases g.route_cases m col v b with he | ⟨i, hi, _, hs, ht⟩
  · rw [he]
    change p.recover v (p.reverse v v) = v
    simp [reverse, recover]
  · have hh : G.src (m.mate i) = v := congrArg Prod.fst hs
    rw [ht, ← hh]
    change p.recover (G.dst (m.mate i)) (p.reverse (G.dst (m.mate i)) (G.src (m.mate i))) = _
    unfold reverse
    split_ifs with eq
    · exact eq
    · exact p.back _

def role : G.Atom g m → Role w
  | .inl _ => .inl ()
  | .inr (.inl i) => .inr (.inl (p.stub (G.via g m col i.2 i.1) (roleCode col i.2).2, i.2))
  | .inr (.inr _) => .inr (.inr ())

def atomKey (i : G.Atom g m) : AtomKey d w h :=
  let origin := G.receipt g m col i
  let toSite := G.anchor g m col i
  ((p.reverse toSite.1 origin.1, cellIndex h origin.2), p.role g m col i)

theorem atom_unique {i j : G.Atom g m} (ha : G.anchor g m col i = G.anchor g m col j)
    (hk : p.atomKey g m col i = p.atomKey g m col j) : i = j := by
  obtain ⟨hc, hr⟩ := Prod.mk.inj hk
  obtain ⟨hv, hb⟩ := Prod.mk.inj hc
  have hrec (i : G.Atom g m) : p.recover (G.anchor g m col i).1
      (p.reverse (G.anchor g m col i).1 (G.receipt g m col i).1) = (G.receipt g m col i).1 :=
    p.recover_reverse g m col _ _
  have hs : G.receipt g m col i = G.receipt g m col j := by
    refine Prod.ext ?_ ((cellIndex h).injective hb)
    rw [← hrec i, ← hrec j, hv, ha]
  rcases i with i|⟨i, a⟩|i <;> rcases j with j|⟨j, b⟩|j <;>
    simp only [role, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq] at hr
  · exact congrArg Sum.inl (p.one hs)
  · obtain ⟨ht, rfl⟩ := hr
    have hd (t : m.items) : g.rep m col t a =
        (Scheme.side G (G.via g m col a t) (roleCode col a).2, G.ix (G.via g m col a t)) := by
      rw [G.role]
      cases (roleCode col a).2 <;> rfl
    change g.rep m col i a = g.rep m col j a at hs
    rw [hd, hd] at hs
    have he := p.separate _ _ _ (Prod.mk.inj hs).1 (Prod.mk.inj hs).2 ht
    rw [(G.via g m col a).injective he]
  · exact congrArg (fun v => Sum.inr (Sum.inr v)) hs

def atomNames (z : Site G.V h) : ↥(G.receipts g m col z) ↪ AtomKey d w h where
  toFun i := p.atomKey g m col i.val
  inj' i j he := Subtype.ext (p.atom_unique g m col
    ((Finset.mem_filter.mp i.property).2.2.trans (Finset.mem_filter.mp j.property).2.2.symm) he)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
end

/-! # Short local names for incident and hidden spans -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
open Coloring Packing HostNet History.Subround Spectral.Tensor

abbrev StubKey (d w h : ℕ) := (AtomKey d w h × Bool) × B w
abbrev SupplyKey (d w h b : ℕ) :=
  Bool × ((AtomKey d w h × Fin 8 × Fin (4 * b)) ⊕ (StubKey d w h × Fin b))
abbrev SpanKey (d w h b : ℕ) := StubKey d w h ⊕ SupplyKey d w h b

variable {T F : Type} [Fintype T] {x y : Wire} {L : Fringe x y T} {h u d w : ℕ}
  {G : HostNet F L h u} (p : Navigation G d w)
  {Δ D k : ℕ} {B' : ℝ} (g : Grouping G.N G.C Δ D k B' G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (col : Bool)

def stubAtom (e : G.E) (b : Bool) : G.Atom g m := .inr (.inr (Scheme.side G e b, G.ix e))

def stubKey (e : G.E) (b : Bool) : StubKey d w h :=
  ((p.atomKey g m col (stubAtom g m e b), b), p.stub e b)

theorem stub_unique {e f : G.E} {a b : Bool}
    (hs : G.anchor g m col (stubAtom g m e a) = G.anchor g m col (stubAtom g m f b))
    (he : p.stubKey g m col e a = p.stubKey g m col f b) : (e, a) = (f, b) := by
  obtain ⟨he, ht⟩ := Prod.mk.inj he
  obtain ⟨he, rfl⟩ := Prod.mk.inj he
  have hv := p.atom_unique g m col hs he
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj hv))
  rw [p.separate e f _ h₁ h₂ ht]

variable [Field F] (P : Gadget F) (i : g.Choice m P)

def supplyAtom (e : g.Supply m P i) (b : Bool) : G.Atom g m :=
  .inr (cond b (g.supplies m e).2 (g.supplies m e).1)

theorem supply_anchor (e : g.Supply m P i) (b : Bool) :
    G.anchor g m col (supplyAtom g m P i e b) =
      cond b (g.contact m col e).2 (g.contact m col e).1 := by
  cases b <;> rcases e with ⟨t, j, k⟩ | ⟨z, k⟩ <;> rfl

private theorem profile_bound (e : m.items) (j : Fin 8) : g.profile m i e j ≤ 4 * P.b :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
    (P.cost _ (i e).2.property).le

def supplyKey (e : g.Supply m P i) (b : Bool) : SupplyKey d w h P.b :=
  (b, match e with
    | .inl ⟨t, j, k⟩ => .inl (p.atomKey g m col (supplyAtom g m P i (.inl ⟨t, j, k⟩) b),
        j, k.castLE (profile_bound g m P i t j))
    | .inr (e, k) => .inr (p.stubKey g m col e.val b, k))

theorem supply_unique {e f : g.Supply m P i} {a b : Bool}
    (hs : G.anchor g m col (supplyAtom g m P i e a) =
      G.anchor g m col (supplyAtom g m P i f b))
    (he : p.supplyKey g m col P i e a = p.supplyKey g m col P i f b) : (e, a) = (f, b) := by
  obtain ⟨rfl, he⟩ := Prod.mk.inj he
  rcases e with ⟨r, j, k⟩ | ⟨r, k⟩ <;> rcases f with ⟨t, j', k'⟩ | ⟨t, k'⟩
  · obtain ⟨ha, hj⟩ := Prod.mk.inj (Sum.inl.inj he)
    have ht := p.atom_unique g m col hs ha
    have hrt : r = t := by
      cases a <;> exact congrArg Sigma.fst (Sum.inl.inj (Sum.inr.inj ht))
    subst t
    obtain ⟨rfl, hk⟩ := Prod.mk.inj hj
    have hkk : k = k' := Fin.ext (congrArg (fun j : Fin (4 * P.b) => j.val) hk)
    subst k'
    rfl
  · cases he
  · cases he
  · obtain ⟨ha, rfl⟩ := Prod.mk.inj (Sum.inr.inj he)
    have hh : G.anchor g m col (stubAtom g m r.val a) =
        G.anchor g m col (stubAtom g m t.val a) := by cases a <;> exact hs
    have hrt : r = t := Subtype.ext (Prod.mk.inj (p.stub_unique g m col hh ha)).1
    subst t
    rfl

def hiddenKey : Segment g m P i → SpanKey d w h P.b
  | .inl e => .inl (p.stubKey g m (g.layout m P i) e false)
  | .inr (.inl e) => .inl (p.stubKey g m (g.layout m P i) e true)
  | .inr (.inr e) => .inr (p.supplyKey g m (g.layout m P i) P i e false)

def hiddenNames (v : Site G.V h) : Hidden g m P i v ↪ SpanKey d w h P.b where
  toFun e := p.hiddenKey g m P i e.val
  inj' := by
    rintro ⟨e, he⟩ ⟨f, hf⟩ hk
    have hs := congrArg Prod.fst (he.trans hf.symm)
    apply Subtype.ext
    change e = f
    let col := g.layout m P i
    rcases e with e|e|e <;> rcases f with f|f|f
    · rw [(Prod.mk.inj (p.stub_unique g m col (e := e) (f := f) (a := false) (b := false) hs
        (Sum.inl.inj hk))).1]
    · have h := (Prod.mk.inj (p.stub_unique g m col (e := e) (f := f) (a := false) (b := true) hs
        (Sum.inl.inj hk))).2
      cases h
    · cases hk
    · have h := (Prod.mk.inj (p.stub_unique g m col (e := e) (f := f) (a := true) (b := false) hs
        (Sum.inl.inj hk))).2
      cases h
    · rw [(Prod.mk.inj (p.stub_unique g m col (e := e) (f := f) (a := true) (b := true) hs
        (Sum.inl.inj hk))).1]
    · cases hk
    · cases hk
    · cases hk
    · have hr : G.anchor g m col (supplyAtom g m P i e false) =
          G.anchor g m col (supplyAtom g m P i f false) := by
        rw [supply_anchor, supply_anchor]
        exact hs
      rw [(Prod.mk.inj (p.supply_unique g m col P i hr (Sum.inr.inj hk))).1]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
end

/-! # Naming and counting output spans in a local record -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing HostNet History.Subround
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z d : ℕ}
    (P : Gadget F) (G : HostNet F L h (P.b * z))
    {Δ D k : ℕ} {B' : ℝ} (g : Grouping G.N G.C Δ D k B' G.load)
    (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (i : g.Choice m P)
    {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G.diagram)
    (v : Site G.V h)

namespace Navigation

variable (q : Navigation G d S.e)

def faceKey : Face g m P i p → SpanKey d S.e h P.b
  | .inl e => .inl ((q.atomKey g m (g.layout m P i) (.inl e.val.1), false), e.val.2)
  | .inr (e, t) => .inr (q.supplyKey g m (g.layout m P i) P i e.val t)

def visibleNames : Visible g m P G.units i p v ↪ SpanKey d S.e h P.b where
  toFun e := faceKey P G g m i p q e.val
  inj' := by
    rintro ⟨e, he⟩ ⟨f, hf⟩ hkey
    apply Subtype.ext
    change e = f
    let col := g.layout m P i
    rcases e with e|⟨e, a⟩ <;> rcases f with f|⟨f, b⟩
    · obtain ⟨hk, hl⟩ := Prod.mk.inj (Sum.inl.inj hkey)
      have ha : G.anchor g m col (.inl e.val.1) = G.anchor g m col (.inl f.val.1) := he.trans hf.symm
      have h := q.atom_unique g m col ha (Prod.mk.inj hk).1
      exact congrArg Sum.inl (Subtype.ext (Prod.ext (Sum.inl.inj h) hl))
    · cases hkey
    · cases hkey
    · have ha : G.anchor g m col (supplyAtom g m P i e.val a) =
          G.anchor g m col (supplyAtom g m P i f.val b) := by
        rw [supply_anchor, supply_anchor]
        exact he.trans hf.symm
      obtain ⟨hh, rfl⟩ := Prod.mk.inj (q.supply_unique g m col P i ha (Sum.inr.inj hkey))
      rw [Subtype.ext hh]

end Navigation

namespace History.Subround

theorem visible_bound (hz : 0 < z) (hB : 0 ≤ B') (hw : ∀ q, z ≤ p.borderWidth q) :
    Fintype.card (Visible g m P G.units i p v) * (z : ℝ) ≤ 9 * (near G.C Δ v).card * ((2 : ℝ) ^ k * B') := by
  let A := Visible g m P G.units i p v
  let C := g.contract m P G.units hz i
  have hlen (q : A) : z ≤ visibleWidth g m P i p z q.val := by
    rcases q with ⟨q|q, _⟩
    · exact hw q
    · exact le_rfl
  have he : Fintype.card A * z ≤ C.arity v := by
    have eq := Fintype.card_congr (visibleBits g m P G.units hz i p v)
    simp only [Fintype.card_sigma, Fintype.card_fin, Diagram.Port, Fintype.card_sum, card_slots] at eq
    have := Finset.sum_le_sum (s := Finset.univ) (fun q _ => hlen q)
    rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at this
    exact this.trans_eq eq
  have hi (t : G.V × Cell h) : (P.b * z : ℕ) * (degree G.pair t : ℝ) ≤ G.load t.1 t.2 := by
    rw [mul_comm]
    exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load _ _)
  have ho (t : G.V × Cell h) : (exterior G.diagram G.units.place t : ℝ) ≤ G.load t.1 t.2 :=
    (le_add_of_nonneg_right (by positivity)).trans (G.core_le_load _ _)
  refine le_trans ?_ (g.load_contract m P G.units hz G.cs G.sub G.edge G.load_nonneg hB hi ho i v)
  rw [← Nat.cast_mul]
  exact Nat.cast_le.mpr he

end History.Subround
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

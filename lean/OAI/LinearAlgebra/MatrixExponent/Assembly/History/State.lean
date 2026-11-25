import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reads
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Radius
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Checks

/-! # Recognizing exterior spans by their local pattern -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
open Coloring Packing
open scoped Classical

variable {F T : Type} [Field F] {x y : Wire} {L : Fringe x y T}
  {h u : ℕ} {S : Scheme F} {r : S.format.obj}
  {G : HostNet F L h u} (p : S.Posting r G) (a : ℕ) (ha : a ≤ h)

local notation "H" => G.regroup a ha

def patternAt (v : G.V × Cell a) (b : B (h - a)) : Pattern F S.d S.k S.e :=
  S.decode ((r (p.host v.1)).2 (p.block ((splitCell a ha).symm (v.2, (cellIndex _).symm b))))

private def addressAt (v : G.V × Cell a) (b : B (h - a)) : S.Vtx :=
  (p.host v.1, p.block ((splitCell a ha).symm (v.2, (cellIndex _).symm b)), 0)

private theorem addressAt_eq (v : G.V × Cell a) (b : B (h - a)) (w : G.diagram.V) :
    p.vertex w = p.addressAt a ha v b ↔ (H).units.place w = (v, (cellIndex _).symm b) := by
  rw [p.vertex_eq]
  change _ ↔ splitAddr G.V a ha (G.units.place w) = (v, (cellIndex _).symm b)
  rw [← Equiv.eq_symm_apply]
  simp only [addressAt, Prod.mk.injEq, p.host.injective.eq_iff, p.block.injective.eq_iff, and_true]
  rw [Prod.ext_iff]
  rfl

theorem occupied_iff (v : G.V × Cell a) (b : B (h - a)) :
    (∃ j, 0 < (p.patternAt a ha v b).width 0 j) ↔
      ∃ w : G.diagram.V, 0 < G.diagram.arity w ∧ (H).units.place w = (v, (cellIndex _).symm b) := by
  let q := p.addressAt a ha v b
  have size w : 0 < G.diagram.arity w ↔ Nonempty (S.LocalPin r (p.vertex w)) := by
    rw [← Fintype.card_pos_iff, ← Fintype.card_congr (p.pin w)]
    simp only [Diagram.Port, Fintype.card_sum, card_slots, Diagram.arity]
  change (∃ j, 0 < S.width r (q, j)) ↔ _
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨w, hw⟩ := p.cover ⟨(q, j), ⟨0, hj⟩⟩
    change p.vertex w = q at hw
    refine ⟨w, (size w).mpr ?_, (p.addressAt_eq _ _ _ _ _).mp hw⟩
    rw [hw]
    exact ⟨⟨j, ⟨0, hj⟩⟩⟩
  · rintro ⟨w, hw, ht⟩
    have h := (size w).mp hw
    rw [(p.addressAt_eq _ _ _ _ _).mpr ht] at h
    obtain ⟨⟨j, i⟩⟩ := h
    exact ⟨j, i.pos⟩

theorem border_iff (v : G.V × Cell a) (b : B (h - a)) (j : B S.e) :
    let t := (cellIndex _).symm b
    let M := p.patternAt a ha v b
    0 < M.width 0 j ∧ M.peer 0 j = none ↔
      ∃ e : p.toPresentation.BorderSpan, (H).units.place e.val.1 = (v, t) ∧ e.val.2 = j := by
  intro t M
  let y : S.Vtx := (p.host v.1, p.block ((splitCell a ha).symm (v.2, t)), 0)
  have hv (w : G.diagram.V) : p.vertex w = y ↔ (H).units.place w = (v, t) :=
    p.addressAt_eq a ha v b w
  have peer : M.peer 0 j = none ↔ S.peer r (y, j) = none := by
    simp [M, patternAt, t, Scheme.peer, Scheme.pattern, y]
  rw [peer]
  change 0 < S.width r (y, j) ∧ _ ↔ _
  constructor
  · rintro ⟨hw, hp⟩
    obtain ⟨w, he⟩ := p.cover ⟨(y, j), ⟨0, hw⟩⟩
    change p.vertex w = y at he
    exact ⟨⟨(w, j), by rw [he]; exact ⟨hw, hp⟩⟩, (hv w).mp he, rfl⟩
  · rintro ⟨⟨⟨w, s⟩, hs⟩, hw, rfl⟩
    rwa [← (hv w).mpr hw]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
end

/-!
# Identifying the active atoms of a contraction locally

Search only the two-hop neighborhood of the receiving position.
Checkers are counted once by their stamp even if many untouched rows
name the same occurrence.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting

open Coloring Packing Navigation.Emission Finset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T}
  {u h : ℕ} {S : Scheme F} {r : S.format.obj}
  {G : HostNet F L h u} (p : S.Posting r G) (hu : 0 < u)
  (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load)
  (m : Matchings a ha g) (ctl : p.Controls hu a ha g m) (col : Bool)
  (v : Site (G.V × Cell a) (h - a))

local notation "H" => G.regroup a ha
local notation "q" => p.navigation hu a ha
local notation "c" => p.chart hu a ha g m ctl
local notation "nav" => p.groupNav a
local notation "data" => p.records a ha g m.color
local notation "recv" => p.recv a ha
local notation "key" => Navigation.AtomKey S.d S.e (h - a)
local notation "row" => (G.V × Cell a) × B (h - a + S.e)

private theorem checker_at (e : (H).E) (s : Bool) :
    let j := (c).row e
    let ends := Match.localEnds nav data col j.1 j.2
    Match.readPath nav j.1 (cond s ends.2 ends.1) =
      (c).site (g.route m col (Scheme.side H e s) ((H).ix e)) := by
  have he := (c).endpoints col e
  cases s
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

private theorem checker_key (e : (H).E) (s : Bool) :
    let j := (c).row e
    (q).atomKey g m col (Navigation.stubAtom g m e s) =
      checker (tipAt nav data recv col j.1 j.2 s).1 :=
  congrArg (fun t : Tip S.d S.e (h - a) => checker (w := S.e) t.1) (p.tip_eq hu a ha g m ctl col e s)

def Reported (j : key) : Prop :=
  (∃ w ∈ (q).neighborhood v.1, ∃ b,
    (∃ i, 0 < (p.patternAt a ha w b).width 0 i) ∧
    Match.follow nav w (Match.action col (data w) b) = (c).site v ∧
    station (stampAt nav data recv col w b) = j) ∨
  (∃ t : row, t.1 ∈ (q).neighborhood v.1 ∧ ∃ i,
    (Match.rows (data t.1)).control.1 t.2 = true ∧
    Match.readPath nav t.1 (Match.localParties nav data col t.1 t.2 i) = (c).site v ∧
    party col (partyTips nav data recv col t.1 t.2) i = j) ∨
  (∃ t : row, t.1 ∈ (q).neighborhood v.1 ∧ ∃ s : Bool,
    Match.untouched data t = true ∧
    (let ends := Match.localEnds nav data col t.1 t.2
     Match.readPath nav t.1 (cond s ends.2 ends.1) = (c).site v) ∧
    checker (tipAt nav data recv col t.1 t.2 s).1 = j)

theorem atom_image (j : key) :
    j ∈ univ.map ((q).atomNames g m col v) ↔ p.Reported hu a ha g m ctl col v j := by
  have mark (w : (H).V) (b : Cell (h - a)) := p.stamp_eq hu a ha g m ctl col w b
  have role (t : m.items) (i : Fin 6) :
      (q).atomKey g m col (.inr (.inl ⟨t, i⟩)) =
      party col (partyTips nav data recv col ((c).marked t).1 ((c).marked t).2) i :=
    ((q).atom_party g m col t i).trans
      (congrArg (fun y => party col y i) (p.tips_eq hu a ha g m ctl col t))
  constructor
  · intro he
    obtain ⟨⟨t, hv⟩, _, hj⟩ := mem_map.mp he
    simp only [HostNet.receipts, mem_filter, mem_univ, true_and] at hv
    obtain ⟨ht, hw⟩ := hv
    change (q).atomKey g m col t = j at hj
    rcases t with t|⟨t, i⟩|t
    · let y := (H).units.place t
      change g.route m col y.1 y.2 = v at hw
      refine .inl ⟨y.1, hw ▸ (q).window_move g m col y.1 y.2, cellIndex _ y.2, ?_, ?_, ?_⟩
      · exact (p.occupied_iff a ha _ _).mpr ⟨t, ht, by rw [Equiv.symm_apply_apply]; rfl⟩
      · exact ((c).moved col _ _).trans (congrArg (c).site hw)
      · exact (congrArg station (mark _ _)).symm.trans hj
    · change g.party m col t i = v at hw
      exact .inr (.inl ⟨(c).marked t, hw ▸ (q).window_party g m col t i, i,
        ((c).marks _).mpr ⟨t, rfl⟩, ((c).gadget col t i).trans (congrArg _ hw),
        (role _ _).symm.trans hj⟩)
    · obtain ⟨e, he⟩ := ht
      obtain ⟨s, rfl⟩ : ∃ s, (Scheme.side H e.val s, (H).ix e.val) = t := by
        rcases he with he|he
        · exact ⟨false, he⟩
        · exact ⟨true, he⟩
      change g.route m col (Scheme.side H e.val s) ((H).ix e.val) = v at hw
      exact .inr (.inr ⟨(c).row e.val, hw ▸ (q).window_end g m col e.val s, s,
        ((c).untouched_iff _).mpr ⟨e, rfl⟩,
        (p.checker_at hu a ha g m ctl col e.val s).trans (congrArg _ hw),
        (p.checker_key hu a ha g m ctl col e.val s).symm.trans hj⟩)
  · have put (i : (H).Atom g m) (hi : (H).live g m i)
        (hv : (H).anchor g m col i = v) (hk : (q).atomKey g m col i = j) :
        j ∈ univ.map ((q).atomNames g m col v) :=
      mem_map.mpr ⟨⟨i, by simp only [HostNet.receipts, mem_filter, mem_univ, true_and]; exact ⟨hi, hv⟩⟩, mem_univ _, hk⟩
    rintro (⟨w, _, b, ht, hs, hk⟩|⟨t, _, i, ht, hs, hk⟩|⟨t, _, i, ht, hs, hk⟩)
    · obtain ⟨b, rfl⟩ := (cellIndex _).surjective b
      obtain ⟨u, hu', he⟩ := (p.occupied_iff _ _ _ _).mp ht
      rw [Equiv.symm_apply_apply] at he
      refine put (.inl u) hu' ?_ ?_
      · change g.route m col ((H).units.place u).1 ((H).units.place u).2 = v
        rw [he]
        exact (c).site.injective (((c).moved col w b).symm.trans hs)
      · exact ((q).atom_station g m col u).trans ((congrArg
          (fun t => station ((q).stamp g m col t)) he).trans ((congrArg station (mark w b)).trans hk))
    · obtain ⟨t, rfl⟩ := ((c).marks _).mp ht
      exact put (.inr (.inl ⟨t, i⟩)) trivial
        ((c).site.injective (((c).gadget col t i).symm.trans hs)) ((role _ _).trans hk)
    · obtain ⟨e, rfl⟩ := ((c).untouched_iff _).mp ht
      refine put (Navigation.stubAtom (G := H) g m e.val i) ?_
        ((c).site.injective ((p.checker_at hu a ha g m ctl col e.val i).symm.trans hs))
        ((p.checker_key hu a ha g m ctl col e.val i).trans hk)
      refine ⟨e, ?_⟩
      cases i
      · exact .inl rfl
      · exact .inr rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
end

/-! # Compact keys of incident spans before local numbering -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
open Coloring Packing History.Subround
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z d : ℕ}
  (P : Gadget F) {G : HostNet F L h (P.b * z)} {S : Scheme F} {r : S.format.obj}
  (q : Navigation G d S.e)
  {Δ D k : ℕ} {B' : ℝ} (g : Grouping G.N G.C Δ D k B' G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (i : g.Choice m P)
  (p : S.Presentation r G.diagram) (v : Site G.V h)

def portKey : PortMap.Port g m P G.units i p v → Bool × SpanKey d S.e h P.b
  | .inl u => (false, q.faceKey P G g m i p u.val)
  | .inr u => (true, q.hiddenKey g m P i u.val)

local notation "col" => g.layout m P i

theorem portKey_exterior (e : p.BorderSpan) (he : g.assign m P G.units i e.val.1 = v) :
    q.portKey P g m i p v (PortMap.exterior g m P G.units i p v e he) =
      (false, Emission.exterior (q.stamp g m col (G.units.place e.val.1)) e.val.2) := rfl

theorem portKey_demand (e : G.E) (t : Bool)
    (he : g.route m col (cond t (G.dst e) (G.src e)) (G.ix e) = v) :
    q.portKey P g m i p v (PortMap.demand g m P G.units i p v e t he) =
      (true, Emission.demand (q.tip g m col e t) t) := by cases t <;> rfl

theorem portKey_supply (e : g.Supply m P i) (t : Bool)
    (he : PortMap.supplySite g m P i e t = v) :
    q.portKey P g m i p v (PortMap.supply g m P G.units i p v e t he) =
      Emission.pointer col (q.eventTips g m col P i e) (eventKind g m P i e)
        (decide ((g.contact m col e).1 = (g.contact m col e).2)) t := by
  by_cases h : (g.contact m col e).1 = (g.contact m col e).2
  · rw [PortMap.supply, dite_eq_left h, decide_eq_true h]
    exact q.hidden_new g m P i e t
  · rw [PortMap.supply, dite_eq_right h, decide_eq_false h]
    exact q.visible_new P G g m i p ⟨e, h⟩ t

end OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
end

/-! # Recovering all hidden and visible keys from active records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation.Emission
open Coloring

variable {V : Type} {d h w ℓ b : ℕ} (nav : V → B d → V)
  (data : V → (Match.Input d h w w ℓ).obj) (col : Bool)

def oldAt (j : V × B (h + w)) (s : Bool) : V × B ℓ :=
  let ends := Match.localEnds nav data col j.1 j.2
  Match.readPath nav j.1 (cond s ends.2 ends.1)

def newAt (j : Match.Candidate V (h + w) b) (s : Bool) : V × B ℓ :=
  let ends := Match.paths nav data col j
  Match.readPath nav j.1.1 (cond s ends.2 ends.1)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation.Emission

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
open Coloring Packing Navigation.Emission Finset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T}
  {h z : ℕ} {P : Gadget F} {S : Scheme F} {r : S.format.obj}
  {G : HostNet F L h (P.b * z)} (p : S.Posting r G)
  (hu : 0 < P.b * z) (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load)
  (m : Matchings a ha g) (ctl : p.Controls hu a ha g m) (i : g.Choice m P)

local notation "H" => G.regroup a ha
local notation "q" => p.navigation hu a ha
local notation "c" => p.chart hu a ha g m ctl
local notation "col" => g.layout m P i
local notation "data" => p.records a ha g m.color

local notation "nav" => p.groupNav a
local notation "candidate" => Match.Candidate (G.V × Cell a) (h - a + S.e) P.b

theorem oldAt_eq (t : (H).E) (s : Bool) :
    oldAt nav data col ((c).row t) s =
      (c).site (g.route m col (Scheme.side H t s) ((H).ix t)) := by
  have he := (c).endpoints col t
  cases s
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem newAt_eq (t : g.Supply m P i) (s : Bool) :
    newAt nav data col ((c).event P i t) s =
      (c).site (cond s (g.contact m col t).2 (g.contact m col t).1) := by
  have he := (c).read_event P i col t
  cases s
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem old_key (t : (H).E) (s : Bool) :
    let j := (c).row t
    (q).hiddenKey g m P i (cond s (.inr (.inl t)) (.inl t)) =
      demand (tipAt nav data (p.recv a ha) col j.1 j.2 s) s :=
  ((q).hidden_old g m P i t s).trans
    (congrArg (fun x => demand x s) (p.tip_eq hu a ha g m ctl col t s))

theorem supply_key (t : g.Supply m P i) (s : Bool) :
    let j := (c).event P i t
    (q).supplyKey g m col P i t s =
      supply col (supplyTips nav data (p.recv a ha) col j) j.2 s :=
  ((q).supply_eq g m col P i t s).trans (congrArg₂ (fun x y => supply col x y s)
    (p.eventTips_eq hu a ha g m ctl col P i t) (p.eventKind_eq hu a ha g m ctl P i t))

variable (shape : (G.V × Cell a) × B (h - a + S.e) → Fin 8 → ℕ)
  (code : ∀ t, shape ((p.chart hu a ha g m ctl).marked t) = g.profile m i t)
  (v : Site (G.V × Cell a) (h - a)) (j : Navigation.SpanKey S.d S.e (h - a) P.b)

private theorem in_window (t : g.Supply m P i) (s : Bool)
    (he : cond s (g.contact m col t).2 (g.contact m col t).1 = v) :
    ((c).event P i t).1.1 ∈ (q).neighborhood v.1 := by
  have hs := (q).window_supply g m col P i t s
  subst v
  rcases t with ⟨t, j, l⟩ | ⟨t, l⟩ <;> exact hs

include code in
theorem hidden_image :
    j ∈ univ.map ((q).hiddenNames g m P i v) ↔
      (∃ (t : (G.V × Cell a) × B (h - a + S.e)) (s : Bool),
        t.1 ∈ (q).neighborhood v.1 ∧ (Match.rows (data t.1)).active t.2 = true ∧ oldAt nav data col t s = (c).site v ∧
        demand (tipAt nav data (p.recv a ha) col t.1 t.2 s) s = j) ∨
      (∃ t : candidate, t.1.1 ∈ (q).neighborhood v.1 ∧ Match.enabled data shape t = true ∧
        newAt nav data col t false = (c).site v ∧ newAt nav data col t true = (c).site v ∧
        .inr (supply col (supplyTips nav data (p.recv a ha) col t) t.2 false) = j) := by
  have old := p.oldAt_eq hu a ha g m ctl i
  have new := p.newAt_eq hu a ha g m ctl i
  have first := p.old_key hu a ha g m ctl i
  have second := p.supply_key hu a ha g m ctl i
  have win (t : (H).E) (s : Bool) (he : g.route m col (Scheme.side H t s) ((H).ix t) = v) :
      ((c).row t).1 ∈ (q).neighborhood v.1 := by
    rw [← he]
    exact (q).window_end g m col t s
  constructor
  · intro hj
    obtain ⟨⟨t|t|t, ht⟩, _, he⟩ := mem_map.mp hj
    · exact .inl ⟨(c).row t, false, win t false (congrArg Prod.fst ht), ((c).active _).mpr ⟨t, rfl⟩,
        (old t false).trans (congrArg (c).site (congrArg Prod.fst ht)), (first t false).symm.trans he⟩
    · exact .inl ⟨(c).row t, true, win t true (congrArg Prod.fst ht), ((c).active _).mpr ⟨t, rfl⟩,
        (old t true).trans (congrArg (c).site (congrArg Prod.fst ht)), (first t true).symm.trans he⟩
    · exact .inr ⟨(c).event P i t, p.in_window hu a ha g m ctl i v t false (congrArg Prod.fst ht),
        ((c).enabled_iff P i shape code _).mpr ⟨t, rfl⟩,
        (new t false).trans (congrArg (c).site (congrArg Prod.fst ht)),
        (new t true).trans (congrArg (c).site (congrArg Prod.snd ht)),
        (congrArg Sum.inr (second t false).symm).trans he⟩
  · rintro (⟨j, s, _, hj, hv, he⟩|⟨j, _, hj, hv, hw, he⟩)
    · obtain ⟨t, rfl⟩ := ((c).active j).mp hj
      have hm := (c).site.injective ((old t s).symm.trans hv)
      have hloc : History.Subround.ends g m P i (cond s (.inr (.inl t)) (.inl t)) = (v, v) := by
        cases s <;> exact Prod.ext hm hm
      exact mem_map.mpr ⟨⟨_, hloc⟩, mem_univ _, (first t s).trans he⟩
    · obtain ⟨t, rfl⟩ := ((c).enabled_iff P i shape code j).mp hj
      have hloc : g.contact m col t = (v, v) := Prod.ext
        ((c).site.injective ((new t false).symm.trans hv))
        ((c).site.injective ((new t true).symm.trans hw))
      exact mem_map.mpr ⟨⟨.inr (.inr t), hloc⟩, mem_univ _, (congrArg Sum.inr (second t false)).trans he⟩

include code in
theorem visible_image :
    j ∈ univ.map ((q).visibleNames P H g m i p.toPresentation v) ↔
      (∃ (w : G.V × Cell a) (b : B (h - a)) (s : B S.e), w ∈ (q).neighborhood v.1 ∧
        (0 < (p.patternAt a ha w b).width 0 s ∧ (p.patternAt a ha w b).peer 0 s = none) ∧
        Match.follow nav w (Match.action col (data w) b) = (c).site v ∧
        exterior (stampAt nav data (p.recv a ha) col w b) s = j) ∨
      (∃ (t : candidate) (s : Bool), t.1.1 ∈ (q).neighborhood v.1 ∧
        Match.enabled data shape t = true ∧ newAt nav data col t s = (c).site v ∧
        newAt nav data col t false ≠ newAt nav data col t true ∧
        .inr (supply col (supplyTips nav data (p.recv a ha) col t) t.2 s) = j) := by
  have new := p.newAt_eq hu a ha g m ctl i
  have key := p.supply_key hu a ha g m ctl i
  have border (t : p.toPresentation.BorderSpan) := (q).visible_old P H g m i p.toPresentation t
  have loc (w : G.V × Cell a) (b : Cell (h - a)) :
      Match.follow nav w (Match.action col (data w) (cellIndex _ b)) = (c).site (g.route m col w b) :=
    (c).moved col w b
  constructor
  · intro hj
    obtain ⟨⟨t|⟨t, s⟩, ht⟩, _, he⟩ := mem_map.mp hj
    · let w := (H).units.place t.val.1
      change g.route m col w.1 w.2 = v at ht
      have win := (q).window_move g m col w.1 w.2
      refine .inl ⟨w.1, cellIndex _ w.2, t.val.2, ?_, ?_, (loc _ _).trans (congrArg (c).site ht), ?_⟩
      · rw [← ht]
        exact win
      · apply (p.border_iff a ha _ _ _).mpr
        exact ⟨t, by rw [Equiv.symm_apply_apply]; rfl, rfl⟩
      · exact (congrArg (fun z => exterior z t.val.2)
          (p.stamp_eq hu a ha g m ctl col w.1 w.2).symm).trans ((border t).symm.trans he)
    · refine .inr ⟨(c).event P i t.val, s, p.in_window hu a ha g m ctl i v t.val s ht,
        ((c).enabled_iff P i shape code _).mpr ⟨t.val, rfl⟩, (new t.val s).trans (congrArg (c).site ht),
        ?_, (congrArg Sum.inr (key t.val s).symm).trans he⟩
      exact fun e => t.property ((c).site.injective ((new t.val false).symm.trans (e.trans (new t.val true))))
  · rintro (⟨w, b, s, _, hb, hv, he⟩|⟨t, s, _, ht, hv, hw, he⟩)
    · obtain ⟨b, rfl⟩ := (cellIndex (h - a)).surjective b
      obtain ⟨j, hj, rfl⟩ := (p.border_iff a ha w _ s).mp hb
      rw [Equiv.symm_apply_apply] at hj
      have hroute := (c).site.injective ((loc w b).symm.trans hv)
      have hwhere : History.Subround.whereAt g m P (H).units i p.toPresentation (.inl j) = v := by
        change g.route m col ((H).units.place j.val.1).1 ((H).units.place j.val.1).2 = v
        rw [hj]
        exact hroute
      refine mem_map.mpr ⟨⟨.inl j, hwhere⟩, mem_univ _, (border j).trans ?_⟩
      rw [hj]
      exact (congrArg (fun z => exterior z j.val.2) (p.stamp_eq hu a ha g m ctl col w b)).trans he
    · obtain ⟨t, rfl⟩ := ((c).enabled_iff P i shape code t).mp ht
      have hne : (g.contact m col t).1 ≠ (g.contact m col t).2 := fun e =>
        hw ((new t false).trans ((congrArg (c).site e).trans (new t true).symm))
      have hwhere := (c).site.injective ((new t s).symm.trans hv)
      exact mem_map.mpr ⟨⟨.inr (⟨t, hne⟩, s), hwhere⟩, mem_univ _, (congrArg Sum.inr (key t s)).trans he⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
end

/-! # Comparing destination names in two local coordinate systems -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window
open Coloring Match Navigation.Emission
open scoped Classical

variable {V W X : Type} {d h e ℓ n : ℕ} {α : Env V X d h e ℓ} {β : Env W X d h e ℓ}

def Env.issuers (α : Env V X d h e ℓ) :=
  Finset.univ.image fun i : Option (B d) × Option (B d) =>
    let v := i.1.elim α.root (α.nav α.root)
    i.2.elim v (α.nav v)

theorem Related.issuers {v : V} (hv : v ∈ α.issuers) :
    ∃ w ∈ β.issuers, Related α β 2 v w := by
  obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)), ?_⟩
  have r : Related α β 0 α.root β.root := related_root
  cases i <;> cases j
  · exact r.widen (by decide)
  · exact (r.next _).widen (by decide)
  · exact (r.next _).widen (by decide)
  · exact (r.next _).next _

def Names (α : Env V X d h e ℓ) (β : Env W X d h e ℓ) (x : V × B ℓ) (y : W × B ℓ) :=
  Related α β 4 x.1 y.1 ∧ x.2 = y.2

theorem names_root (i : B ℓ) : Names α β (α.root, i) (β.root, i) :=
  ⟨related_root.widen (by decide), rfl⟩

variable (a : Agree α β 4) {v : V} {w : W} (r : Related α β 2 v w)

include a in
theorem Agree.identical {x x' : V × B ℓ} {y y' : W × B ℓ}
    (h₁ : Names α β x y) (h₂ : Names α β x' y') :
    x = x' ↔ y = y' := by
  rw [Prod.ext_iff, Prod.ext_iff, a.equal h₁.1 h₂.1, h₁.2, h₂.2]

include a r

theorem Agree.motion (c : Bool) (b : B h) :
    Names α β (follow α.nav v (action c (α.data v) b)) (follow β.nav w (action c (β.data w) b)) := by
  rw [(a.records r (by decide)).1]
  exact ⟨(r.follow _).widen (by decide), rfl⟩

omit a in
private theorem related_path (p : (Match.Path d ℓ).obj) :
    Names α β (readPath α.nav v p) (readPath β.nav w p) :=
  ⟨r.path p, rfl⟩

theorem Agree.gadget (c : Bool) (i : B (h + e)) (j : Fin 6) :
    Names α β (readPath α.nav v (localParties α.nav α.data c v i j))
      (readPath β.nav w (localParties β.nav β.data c w i j)) := by
  rw [a.parties r (by decide)]
  exact related_path r _

theorem Agree.oldAt (c : Bool) (i : B (h + e)) (s : Bool) :
    Names α β (oldAt α.nav α.data c (v, i) s) (oldAt β.nav β.data c (w, i) s) := by
  unfold Navigation.Emission.oldAt
  rw [a.ends r (by decide)]
  exact related_path r _

theorem Agree.newAt (c : Bool) (i : B (h + e)) {b : ℕ} (j : Kind b) (s : Bool) :
    Names α β (newAt α.nav α.data c ((v, i), j) s) (newAt β.nav β.data c ((w, i), j) s) := by
  unfold Navigation.Emission.newAt
  rw [a.paths r (by decide)]
  exact related_path r _

theorem Agree.untouched (i : B (h + e)) :
    Match.untouched α.data (v, i) = Match.untouched β.data (w, i) := by
  simp only [Match.untouched, (a.records r (by decide)).1]

theorem Agree.enabled (f : X → B (h + e) → Fin 8 → ℕ) (i : B (h + e)) {b : ℕ} (j : Kind b) :
    Match.enabled α.data (fun t => f (α.extra t.1) t.2) ((v, i), j) =
      Match.enabled β.data (fun t => f (β.extra t.1) t.2) ((w, i), j) := by
  rcases j with ⟨j, k⟩|k
  · simp only [Match.enabled, (a.records r (by decide)).1, (a.records r (by decide)).2.2]
  · exact a.untouched r i

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window
end

/-!
# Receipt lists depend only on the rooted window

The candidate issuer is at distance at most two; reading either of
its endpoints needs at most two more hops. Raw names are compared
locally, without storing absolute host addresses.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window
open Coloring Navigation Navigation.Emission Match
open scoped Classical

variable {V W X F : Type} {d h e ℓ k b : ℕ} {α : Env V X d h e ℓ} {β : Env W X d h e ℓ}

private theorem issuer_exists {f : V → Prop} {g : W → Prop}
    (hh : ∀ v w, Related α β 2 v w → (f v ↔ g w)) :
    (∃ v ∈ α.issuers, f v) ↔ ∃ w ∈ β.issuers, g w := by
  constructor
  · rintro ⟨v, hv, hf⟩
    obtain ⟨w, hw, r⟩ := Related.issuers (β := β) hv
    exact ⟨w, hw, (hh v w r).mp hf⟩
  · rintro ⟨w, hw, hg⟩
    obtain ⟨v, hv, p, hp, e, f⟩ := Related.issuers (β := α) hw
    exact ⟨v, hv, (hh v w ⟨p, hp, f, e⟩).mpr hg⟩

private theorem row_exists {A : Type} {f : V × A → Prop} {g : W × A → Prop}
    (hh : ∀ v w, Related α β 2 v w → ∀ i, f (v, i) ↔ g (w, i)) :
    (∃ v, v.1 ∈ α.issuers ∧ f v) ↔ ∃ w, w.1 ∈ β.issuers ∧ g w := by
  simp only [Prod.exists, exists_and_left]
  exact issuer_exists fun v w r => exists_congr (hh v w r)

private theorem event_exists {A Z : Type} {f : (V × A) × Z → Prop} {g : (W × A) × Z → Prop}
    (hh : ∀ v w, Related α β 2 v w → ∀ i j, f ((v, i), j) ↔ g ((w, i), j)) :
    (∃ v, v.1.1 ∈ α.issuers ∧ f v) ↔ ∃ w, w.1.1 ∈ β.issuers ∧ g w := by
  simp only [Prod.exists, exists_and_left]
  exact issuer_exists fun v w r => exists_congr fun i => exists_congr (hh v w r i)

variable (pattern : X → B h → Pattern F d k e) (shape : X → B (h + e) → Fin 8 → ℕ)

namespace Env
variable (α : Env V X d h e ℓ) (col : Bool) (u : B ℓ)

def atoms (j : AtomKey d e h) : Prop :=
  (∃ w ∈ α.issuers, ∃ i,
    (∃ k, 0 < (pattern (α.extra w) i).width 0 k) ∧
    follow α.nav w (action col (α.data w) i) = (α.root, u) ∧
    station (α.stamp col w i) = j) ∨
  (∃ t : V × B (h + e), t.1 ∈ α.issuers ∧ ∃ i,
    (rows (α.data t.1)).control.1 t.2 = true ∧
    readPath α.nav t.1 (localParties α.nav α.data col t.1 t.2 i) = (α.root, u) ∧
    party col (α.tips col t.1 t.2) i = j) ∨
  (∃ t : V × B (h + e), t.1 ∈ α.issuers ∧ ∃ s : Bool, untouched α.data t = true ∧
    oldAt α.nav α.data col t s = (α.root, u) ∧ checker (α.tip col t.1 t.2 s).1 = j)

def hidden (j : SpanKey d e h b) : Prop :=
  (∃ (t : V × B (h + e)) (s : Bool), t.1 ∈ α.issuers ∧ (rows (α.data t.1)).active t.2 = true ∧
    oldAt α.nav α.data col t s = (α.root, u) ∧ demand (α.tip col t.1 t.2 s) s = j) ∨
  (∃ t : Candidate V (h + e) b, t.1.1 ∈ α.issuers ∧
    enabled α.data (fun t => shape (α.extra t.1) t.2) t = true ∧
    newAt α.nav α.data col t false = (α.root, u) ∧ newAt α.nav α.data col t true = (α.root, u) ∧
    .inr (supply col (α.supplies col t) t.2 false) = j)

def visible (j : SpanKey d e h b) : Prop :=
  (∃ (w : V) (i : B h) (t : B e), w ∈ α.issuers ∧
    (0 < (pattern (α.extra w) i).width 0 t ∧ (pattern (α.extra w) i).peer 0 t = none) ∧
    follow α.nav w (action col (α.data w) i) = (α.root, u) ∧
    exterior (α.stamp col w i) t = j) ∨
  (∃ (t : Candidate V (h + e) b) (s : Bool), t.1.1 ∈ α.issuers ∧
    enabled α.data (fun t => shape (α.extra t.1) t.2) t = true ∧
    newAt α.nav α.data col t s = (α.root, u) ∧
    newAt α.nav α.data col t false ≠ newAt α.nav α.data col t true ∧
    .inr (supply col (α.supplies col t) t.2 s) = j)
end Env

variable (a : Agree α β 4) (col : Bool) (u : B ℓ)
include a

theorem Agree.atoms (j : AtomKey d e h) :
    α.atoms pattern col u j ↔ β.atoms pattern col u j := by
  unfold Env.atoms
  refine or_congr ?_ (or_congr ?_ ?_)
  · refine issuer_exists fun v w r => exists_congr fun i => ?_
    rw [a.identical (a.motion r col i) (names_root u), a.stamp r (by decide),
      (a.records r (by decide)).2.2]
  · refine row_exists fun v w r i => exists_congr fun t => ?_
    rw [a.identical (a.gadget r col i t) (names_root u), a.tips r (by decide),
      (a.records r (by decide)).1]
  · refine row_exists fun v w r i => exists_congr fun t => ?_
    rw [a.identical (a.oldAt r col i t) (names_root u), a.tip r (by decide), a.untouched r]

theorem Agree.hidden (j : SpanKey d e h b) :
    α.hidden shape col u j ↔ β.hidden shape col u j := by
  unfold Env.hidden
  refine or_congr ?_ ?_
  · simp only [exists_and_left]
    refine row_exists fun v w r i => and_congr (by rw [(a.records r (by decide)).1])
      (exists_congr fun t => ?_)
    rw [a.identical (a.oldAt r col i t) (names_root u), a.tip r (by decide)]
  · refine event_exists fun v w r i t => ?_
    rw [a.identical (a.newAt r col i t false) (names_root u),
      a.identical (a.newAt r col i t true) (names_root u), a.enabled r, a.supplies r (by decide)]

theorem Agree.visible (j : SpanKey d e h b) :
    α.visible pattern shape col u j ↔ β.visible pattern shape col u j := by
  unfold Env.visible
  refine or_congr ?_ ?_
  · simp only [exists_and_left]
    refine issuer_exists fun v w r => exists_congr fun i => exists_congr fun t => ?_
    rw [a.identical (a.motion r col i) (names_root u), a.stamp r (by decide),
      (a.records r (by decide)).2.2]
  · simp only [exists_and_left]
    refine event_exists fun v w r i t => and_congr (by rw [a.enabled r]) (exists_congr fun s => ?_)
    simp only [ne_eq]
    rw [a.identical (a.newAt r col i t s) (names_root u),
      not_congr (a.identical (a.newAt r col i t false) (a.newAt r col i t true)),
      a.supplies r (by decide)]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window
end

/-! # Recovering the three compact-name dictionaries from a local window -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing Finset
open scoped Classical

namespace Window

abbrev Lists (d w h b : ℕ) := Finset (Navigation.AtomKey d w h) ×
  Finset (Navigation.SpanKey d w h b) × Finset (Navigation.SpanKey d w h b)

variable {V W X F : Type} {d h e ℓ k b : ℕ}
  (pattern : X → B h → Pattern F d k e) (shape : X → B (h + e) → Fin 8 → ℕ)

def Env.lists (α : Env V X d h e ℓ) (col : Bool) (key : B ℓ) : Lists d e h b :=
  (univ.filter (α.atoms pattern col key), univ.filter (α.hidden shape col key),
    univ.filter (α.visible pattern shape col key))

theorem Agree.lists {α : Env V X d h e ℓ} {β : Env W X d h e ℓ} (ha : Agree α β 4)
    (col : Bool) (key : B ℓ) :
    α.lists (b := b) pattern shape col key = β.lists pattern shape col key := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i
    simp only [Env.lists, mem_filter, mem_univ, true_and]
    exact ha.atoms pattern _ _ _
  · ext i
    simp only [Env.lists, mem_filter, mem_univ, true_and]
    exact ha.hidden shape _ _ _
  · ext i
    simp only [Env.lists, mem_filter, mem_univ, true_and]
    exact ha.visible pattern shape _ _ _

end Window

namespace Scheme.Posting

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T}
  {h z : ℕ} {P : Gadget F} {S : Scheme F} {r : S.format.obj}
  {G : HostNet F L h (P.b * z)} (p : S.Posting r G)
  (hu : 0 < P.b * z) (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load)
  (m : Matchings a ha g) (ctl : p.Controls hu a ha g m) (i : g.Choice m P)

local notation "H" => G.regroup a ha
local notation "q" => p.navigation hu a ha
local notation "c" => p.chart hu a ha g m ctl
local notation "col" => g.layout m P i

abbrev Detail (S : Scheme F) (J : Type) (n : ℕ) :=
  (B n → B S.ℓ) × (B (n + S.e) → J)

variable {J : Type} (selector : (G.V × Cell a) × B (h - a + S.e) → J)
  (profile : J → Fin 8 → ℕ) (v : Site (G.V × Cell a) (h - a))

def environment : Window.Env (G.V × Cell a) (Detail S J (h - a)) S.d (h - a) S.e (h - a + 1) where
  root := v.1
  nav := p.groupNav a
  data := p.records a ha g m.color
  recv := p.recv a ha
  extra w := (fun b => (r (p.host w.1)).2 (p.block ((splitCell a ha).symm (w.2, (cellIndex _).symm b))),
    fun j => selector (w, j))

def dictionaries : Window.Lists S.d S.e (h - a) P.b :=
  (univ.map ((q).atomNames g m col v), univ.map ((q).hiddenNames g m P i v),
    univ.map ((q).visibleNames P H g m i p.toPresentation v))

theorem dictionaries_eq (code : ∀ t, profile (selector ((c).marked t)) = g.profile m i t) :
    p.dictionaries hu a ha g m i v =
      (p.environment a ha g m selector v).lists
        (fun t b => S.decode (t.1 b)) (fun t j => profile (t.2 j)) col (intervalCode _ v.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext j
    simp only [dictionaries, Window.Env.lists, mem_filter, mem_univ, true_and]
    exact p.atom_image hu a ha g m ctl col v j
  · ext j
    simp only [dictionaries, Window.Env.lists, mem_filter, mem_univ, true_and]
    exact p.hidden_image hu a ha g m ctl i (profile ∘ selector) code v j
  · ext j
    simp only [dictionaries, Window.Env.lists, mem_filter, mem_univ, true_and]
    exact p.visible_image hu a ha g m ctl i (profile ∘ selector) code v j

end Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Comparing two contracted occurrences

Each occurrence may come from a different original diagram and group.
Only the common pattern menu, gadget and scales are shared.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F]

abbrev ChoiceTag (P : Gadget F) := Option (Fin P.copies × ↥P.shapes)

def profileOf (P : Gadget F) : ChoiceTag P → Fin 8 → ℕ :=
  fun q => q.elim (fun _ => 0) (fun i => i.2.val)

structure State (S : Scheme F) (P : Gadget F) (a h z Δ D k : ℕ) (B' : ℝ) where
  T : Type
  [finite : Fintype T]
  x : Wire
  y : Wire
  L : Fringe x y T
  G : HostNet F L h (P.b * z)
  r : S.format.obj
  p : S.Posting r G
  ha : a ≤ h
  hz : 0 < z
  g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load
  m : Scheme.Posting.Matchings a ha g
  ctl : p.Controls (Nat.mul_pos P.pos hz) a ha g m
  i : g.Choice m P
  selector : (G.V × Cell a) × B (h - a + S.e) → ChoiceTag P
  selected : ∀ t, selector ((p.chart (Nat.mul_pos P.pos hz) a ha g m ctl).marked t) = some (i t)
  v : Site (G.V × Cell a) (h - a)

attribute [instance] State.finite

theorem Window.Agree.restrict {V W X : Type} {d h e ℓ m n : ℕ}
    {α : Window.Env V X d h e ℓ} {β : Window.Env W X d h e ℓ} (h : Window.Agree α β n)
    (hm : m ≤ n) : Window.Agree α β m :=
  ⟨fun _ _ hp hq => h.same _ _ (hp.trans hm) (hq.trans hm),
   fun _ hp => h.data _ (hp.trans hm), fun _ hp => h.recv _ (hp.trans hm),
   fun _ hp => h.extra _ (hp.trans hm)⟩

namespace State
variable {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
    (u v : State S P a h z Δ D k B')

include u in
theorem hu : 0 < P.b * z := Nat.mul_pos P.pos u.hz

abbrev H := u.G.regroup a u.ha
abbrev q := u.p.navigation u.hu a u.ha
abbrev c := u.p.chart u.hu a u.ha u.g u.m u.ctl
abbrev col := u.g.layout u.m P u.i
abbrev env := u.p.environment a u.ha u.g u.m u.selector u.v
abbrev lists := u.p.dictionaries u.hu a u.ha u.g u.m u.i u.v

theorem code (t : u.m.items) : profileOf P (u.selector (u.c.marked t)) = u.g.profile u.m u.i t := by
  rw [show u.selector (u.c.marked t) = some (u.i t) from u.selected t]
  rfl

structure Same (n : ℕ) : Prop where
  agree : Window.Agree u.env v.env n
  layout : u.col = v.col
  key : intervalCode _ u.v.2 = intervalCode _ v.v.2

variable {u v} {n : ℕ}

theorem Same.symm (h : u.Same v n) : v.Same u n := ⟨h.agree.symm, h.layout.symm, h.key.symm⟩

theorem Same.lists (e : u.Same v n) (hn : 4 ≤ n) : u.lists = v.lists := by
  have hu := u.p.dictionaries_eq u.hu a u.ha u.g u.m u.ctl u.i u.selector (profileOf P) u.v u.code
  have hv := v.p.dictionaries_eq v.hu a v.ha v.g v.m v.ctl v.i v.selector (profileOf P) v.v v.code
  refine hu.trans (Eq.trans ?_ hv.symm)
  rw [show u.g.layout u.m P u.i = v.g.layout v.m P v.i from e.layout, e.key]
  exact (e.agree.restrict hn).lists _ _ _ _

end State
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

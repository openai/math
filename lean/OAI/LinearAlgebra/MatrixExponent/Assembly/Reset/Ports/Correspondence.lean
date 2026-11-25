import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Raw.Local
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Repost
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Move
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Routes

/-! # Transporting the equality checks of exceptional paths -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Spectral.Packet
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U V : Setup S h u a Δ D Y w B') (R : Rotor F Y w) (fit : U.Fits R c)
local notation "L" => terminalWidth Δ Y
local notation "m" => Detour.steps L

theorem old_start (e : U.G.E) :
    U.oldPlace R fit e false = (U.Z.group (U.G.ix e), U.stop R e 0) := by
  unfold stop
  rw [Detour.Switch.path_zero]
  rfl

theorem old_end (e : U.G.E) :
    U.oldPlace R fit e true = (U.Z.group (U.G.ix e), U.stop R e m) := by
  unfold stop
  rw [Detour.Switch.path_last]
  rfl

variable {U V R fit} {fit' : V.Fits R c} {σ : Cell a} {v : U.G.V} {z : V.G.V}
  {loc : Coord R h a Δ} {x : U.Value R} {y : V.Value R}
  (al : Alignment R fit fit' σ v z loc x y) {e : U.Z.Exceptional} {f : V.Z.Exceptional}

include al in
theorem Alignment.joins (i : Fin (m + 1))
    (he : (U.Z.group (U.G.ix e.val), U.stop R e.val i.val) = (σ, v, loc))
    (hf : (V.Z.group (V.G.ix f.val), V.stop R f.val i.val) = (σ, z, loc))
    (hn : ∀ b, endName U.post e.val b = endName V.post f.val b) :
    U.joins R x i e ↔ V.joins R y i f := by
  have wire (j : Fin m) (b : Bool) (hj : step j.val b = i.val) :
      x (.inr (.inr (j, e))) = y (.inr (.inr (j, f))) := by
    apply al.wire _ _ b
    · rw [detour_place, hj]; exact he
    · rw [detour_place, hj]; exact hf
    · simp only [rawKey, hn]
  unfold Setup.joins Rule.through
  apply Iff.of_eq
  apply congrArg₂ Eq
  · induction i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      exact al.old _ _ false ((U.old_start R fit e.val).trans he) ((V.old_start R fit' f.val).trans hf) (hn false)
    | succ j =>
      simp only [Fin.cons_succ]
      exact wire j true rfl
  · induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact al.old _ _ true ((U.old_end R fit e.val).trans he) ((V.old_end R fit' f.val).trans hf) (hn true)
    | cast j =>
      simp only [Fin.snoc_castSucc]
      exact wire j false rfl

variable {Q : Relation U V} {k n : ℕ} (p : Region U V σ Q n) (hk : k + (h - a) + 3 ≤ n) (hr : Q k v z)
include al p hk hr

private theorem pull_detours (hy : V.detours R σ z loc y) : U.detours R σ v loc x := by
  intro i e he
  let t := Detour.Switch.side L i.val
  have hv : Scheme.side U.G e.val t = v := (U.stop_side R e.val i).symm.trans (Prod.mk.inj (Prod.mk.inj he).2).1
  obtain ⟨g, hg, r⟩ := p.unit_pair (k := k) (by omega) e.val t z (Prod.mk.inj he).1 (hv ▸ hr)
  let f : V.Z.Exceptional := ⟨g, mt r.good.mpr e.property⟩
  have hf : (V.Z.group (V.G.ix f.val), V.stop R f.val i.val) = (σ, z, loc) :=
    Prod.ext (r.group' p) (Prod.ext ((V.stop_side R g i).trans hg)
      ((r.stop p (by omega) R i).symm.trans (Prod.mk.inj (Prod.mk.inj he).2).2))
  exact (al.joins i he hf r.name).mpr (hy i f hf)

theorem Alignment.detours : U.detours R σ v loc x ↔ V.detours R σ z loc y :=
  ⟨pull_detours al.symm p.symm hk hr, pull_detours al p hk hr⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Corresponding ports of two programmed rotor copies -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Spectral.Packet
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U V : Setup S h u a Δ D Y w B') (R : Rotor F Y w) (fit : U.Fits R c)
  {σ : Cell a} {v : U.G.V} {z : V.G.V} {loc : Coord R h a Δ}
  {q : Schedule.Address h} {t : R.Hardware}

theorem old_selected (e : U.End v q) (hs : selected R σ loc q t)
    (he : R.root false (U.delivery.inputAt (v, q) e) = t) :
    U.oldPlace R fit e.val.1.val e.val.2 = (σ, v, loc) := by
  rw [old_place, e.property, U.end_root]
  exact Prod.ext ((U.end_group v q e).trans hs.1) (Prod.ext rfl (he ▸ hs.2))

theorem direct_selected (e : U.End v q) (hs : selected R σ loc q t)
    (he : R.root true (U.delivery.outputAt (v, q) e) = t) :
    U.rawPlace R fit (.inl (.inr e.val.1)) e.val.2 = (σ, v, loc) := by
  have aux {x : Site U.G.V h} (p : GoodEnd U.Z.leaf (demands U.G).point U.Z.good x) :
      U.delivery.outputAt x p = (U.delivery.plug p.val.1 p.val.2).2 := by
    obtain ⟨⟨j, b⟩, rfl⟩ := p
    rfl
  rw [direct_place, e.property, U.end_root, ← aux e, he]
  exact Prod.ext ((U.end_group v q e).trans hs.1) (Prod.ext rfl hs.2)

theorem inside_selected (e : U.delivery.LocalWires R (v, q)) (b : Bool) (hs : selected R σ loc q t)
    (he : cond b (U.localSupply R (v, q) e).2 (U.localSupply R (v, q) e).1 = t) :
    U.rawPlace R fit (.inl (.inl ⟨(v, q), e⟩)) b = (σ, v, loc) := by
  rw [local_place]
  unfold localSupply at he
  rw [he]
  exact Prod.ext hs.1 (Prod.ext rfl hs.2)

variable {U V R}

structure Program (v : U.G.V) (z : V.G.V) (q : Schedule.Address h)
    (e : U.End v q ≃ V.End z q) : Prop where
  side : ∀ i, i.val.2 = (e i).val.2
  name : ∀ i, endName U.post i.val.1.val i.val.2 = endName V.post (e i).val.1.val (e i).val.2
  input : ∀ i, U.delivery.inputAt (v, q) i = V.delivery.inputAt (z, q) (e i)
  output : ∀ i, U.delivery.outputAt (v, q) i = V.delivery.outputAt (z, q) (e i)
  layers : U.delivery.layers (v, q) = V.delivery.layers (z, q)
  lane : ∀ i, ((U.delivery.lane (v, q) i).1.cast layers, (U.delivery.lane (v, q) i).2) =
    V.delivery.lane (z, q) (e i)
  config : ∀ j, U.delivery.config (v, q) j = V.delivery.config (z, q) (j.cast layers)

theorem Agree.program (p : Agree U V σ v z) (hq : Site.group a (v, q) = σ) :
    ∃ e, Program (U := U) (V := V) v z q e := by
  obtain ⟨m, e, hm⟩ := p.matching hq
  have name (i : U.End v q) :
      endName U.post i.val.1.val i.val.2 = endName V.post (e i).val.1.val (e i).val.2 := (hm.contact i).symm
  have he (i : U.End v q) : i.val.2 = (e i).val.2 ∧
      Related U V v z i.val.2 i.val.1.val (e i).val.1.val := by
    obtain ⟨j, hj, hr⟩ := p.end_map hq i
    have eq : j = e i := endName_inj V.post V.hu V.Z (z, q) (by
      change endName V.post j.val.1.val j.val.2 = _
      rw [← hj, ← hr.name]
      exact name i)
    subst j
    exact ⟨hj, hr⟩
  refine ⟨e, fun i => (he i).1, name, fun i => p.input hq (he i).2.ix, fun i => (hm.output i).symm, p.layers hq, ?_,
    fun j => p.config hq _ _ rfl⟩
  intro i
  obtain ⟨hl, ht⟩ := Prod.mk.inj (p.lane hq (he i).1 (he i).2)
  exact Prod.ext (Fin.ext hl) ht

theorem Program.wire {e : U.End v q ≃ V.End z q} (p : Program v z q e) (R : Rotor F Y w)
    (i : U.delivery.LocalWires R (v, q)) :
    U.localKey R (v, q) i = V.localKey R (z, q) (R.supplyMap e p.layers i) ∧
    U.localSupply R (v, q) i = V.localSupply R (z, q) (R.supplyMap e p.layers i) := by
  have hl (i : U.End v q) := (Prod.mk.inj (p.lane i)).2
  rcases i with ⟨j, b⟩|⟨j, b⟩|⟨j, b⟩
  · simp only [Rotor.supplyMap, localKey, p.name, localSupply, Rotor.supply, Sum.elim_inl,
      Rotor.pathEdge, p.input, hl, and_self]
  · exact ⟨rfl, rfl⟩
  · simp only [Rotor.supplyMap, localKey, p.name, localSupply, Rotor.supply, Sum.elim_inr,
      Rotor.pathEdge, p.output, hl, and_self]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Corresponding stations implement the same reset packet -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Finset
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup S h u a Δ D Y w B'} {R : Rotor F Y w}
  {fit : U.Fits R c} {fit' : V.Fits R c} {σ : Cell a} {v : U.G.V} {z : V.G.V}
  {loc : Coord R h a Δ} {x : U.Value R} {y : V.Value R}
  (al : Alignment R fit fit' σ v z loc x y)

private theorem pair_read {T : Type} (f : T × Bool → Bool) (i : T) (b : Bool) :
    (if b then f (i, true) else f (i, false)) = f (i, b) := by cases b <;> rfl

variable (U R) (q : Schedule.Address h)

private def rotorIn (v : U.G.V) (x : U.Value R) (i : U.End v q) :=
  if i.val.2 then x (.inl (i.val.1.val, true)) else x (.inl (i.val.1.val, false))

private def rotorOut (v : U.G.V) (x : U.Value R) (i : U.End v q) :=
  x (.inr (.inl (.inr i.val.1)))

private def rotorRead (v : U.G.V) (x : U.Value R) (i : U.delivery.LocalWires R (v, q)) :=
  x (.inr (.inl (.inl ⟨(v, q), i⟩)))

-- Use the same enumeration of incident ends as the abstract delivery.
local instance {V : Type} {h : ℕ} : DecidableEq (Site V h) := Classical.decEq _

local instance {A : Type} [Fintype A] {n : ℕ} : Fintype (R.Supply A n) := inferInstance

private theorem rotor_eval (v : U.G.V) (x : U.Value R) (t : R.Hardware) :
    U.rotorWeight R x ((v, q), t) =
    (R.deployRule (U.delivery.inputAt (v, q)) (U.delivery.outputAt (v, q))
      (U.delivery.config (v, q)) (U.delivery.lane (v, q)) (U.delivery.input (v, q)) (U.delivery.routes (v, q))).entry () t
      (U.rotorIn R q v x) (U.rotorOut R q v x) (U.rotorRead R q v x) := by
  unfold rotorWeight rotorIn rotorOut rotorRead
  rw [Delivery.deploy_entry]

variable {U R q} {t : R.Hardware} {e : U.End v q ≃ V.End z q}
  (prog : Program v z q e) (hs : selected R σ loc q t)

include al prog hs in
private theorem input_eq (i : U.End v q) (hi : R.root false (U.delivery.inputAt (v, q) i) = t) :
    U.rotorIn R q v x i = V.rotorIn R q z y (e i) := by
  unfold rotorIn
  have h := U.old_selected R fit i hs hi
  have h' := V.old_selected R fit' (e i) hs ((congrArg (R.root false) (prog.input i)).symm.trans hi)
  have hn := prog.name i
  rw [← prog.side i] at h' hn
  have eq := al.old _ _ _ h h' hn
  have a := pair_read (x ∘ Sum.inl) i.val.1.val i.val.2
  have b := pair_read (y ∘ Sum.inl) (e i).val.1.val (e i).val.2
  rw [prog.side i] at eq
  rw [prog.side i] at a
  simp only [prog.side i]
  exact a.trans (eq.trans b.symm)

include al prog hs in
private theorem output_eq (i : U.End v q) (hi : R.root true (U.delivery.outputAt (v, q) i) = t) :
    U.rotorOut R q v x i = V.rotorOut R q z y (e i) := by
  have h := U.direct_selected R fit i hs hi
  have h' := V.direct_selected R fit' (e i) hs ((congrArg (R.root true) (prog.output i)).symm.trans hi)
  have hn := prog.name i
  rw [← prog.side i] at h' hn
  exact al.wire _ _ _ h h' (congrArg RawId.direct hn)

include al prog hs in
private theorem inside_eq (i : U.delivery.LocalWires R (v, q))
    (hi : (U.localSupply R (v, q) i).1 = t ∨ (U.localSupply R (v, q) i).2 = t) :
    U.rotorRead R q v x i = V.rotorRead R q z y (R.supplyMap e prog.layers i) := by
  obtain ⟨hkey, heq⟩ := prog.wire R i
  have hs' : ∃ b : Bool, cond b (U.localSupply R (v, q) i).2 (U.localSupply R (v, q) i).1 = t :=
    hi.elim (fun h => ⟨false, h⟩) (fun h => ⟨true, h⟩)
  obtain ⟨b, hb⟩ := hs'
  exact al.wire _ _ _ (U.inside_selected R fit i b hs hb)
    (V.inside_selected R fit' (R.supplyMap e prog.layers i) b hs (heq ▸ hb)) hkey

include al in
theorem Alignment.rotor (p : Agree U V σ v z) {q : Schedule.Address h} {t : R.Hardware}
    (hs : selected R σ loc q t) :
    U.rotorWeight R x ((v, q), t) = V.rotorWeight R y ((z, q), t) := by
  obtain ⟨e, prog⟩ := p.program (q := q) hs.1
  rw [rotor_eval, rotor_eval]
  exact R.deploy_map _ _ _ _ _ _ _ _ _ _ _ _ e prog.layers prog.input prog.output
    prog.lane prog.config t _ _ _ _ _ _
    (input_eq al prog hs) (output_eq al prog hs) (inside_eq al prog hs)

include al in
theorem Alignment.main (p : Agree U V σ v z) :
    U.mainValue R σ v loc x = V.mainValue R σ z loc y := by
  unfold mainValue
  refine prod_congr rfl fun q _ => prod_congr rfl fun t _ => ?_
  split
  · exact al.rotor p ‹_›
  · rfl

include al in
theorem Alignment.value {Q : Relation U V} {k n : ℕ} (p : Region U V σ Q n)
    (hk : k + (h - a) + 3 ≤ n) (hr : Q k v z) :
    U.valueAt R fit σ v loc x = V.valueAt R fit' σ z loc y := by
  simp only [value_eq, al.main (p.toSurvey.agree (by omega) hr), al.detours p hk hr]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Correspondence of both endpoints of each reset supply wire -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c c' : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup S h u a Δ D Y w B'}
  (R : Rotor F Y w) (fit : U.Fits R c) (fit' : V.Fits R c')
  (Q : Relation U V) (σ : Cell a) (k : ℕ)

inductive RawMode : U.Raw R → V.Raw R → Prop
  | inside (x : Schedule.Address h) (v z)
      (e : U.delivery.LocalWires R (v, x)) (f : V.delivery.LocalWires R (z, x)) :
      RawMode (.inl (.inl ⟨(v, x), e⟩)) (.inl (.inl ⟨(z, x), f⟩))
  | direct (e : {i // U.Z.good i}) (f : {j // V.Z.good j}) (r : UnitPair Q σ k e.val f.val) :
      RawMode (.inl (.inr e)) (.inl (.inr f))
  | detour (j : Fin (Detour.steps (terminalWidth Δ Y))) (e : U.Z.Exceptional) (f : V.Z.Exceptional)
      (r : UnitPair Q σ k e.val f.val) : RawMode (.inr (j, e)) (.inr (j, f))

structure RawPair (e : U.Raw R) (f : V.Raw R) : Prop where
  mode : RawMode R Q σ k e f
  key : ∀ t, U.rawKey R e t = V.rawKey R f t
  group : ∀ t, (U.rawPlace R fit e t).1 = σ
  group' : ∀ t, (V.rawPlace R fit' f t).1 = σ
  host : ∀ t, Q k (U.rawPlace R fit e t).2.1 (V.rawPlace R fit' f t).2.1
  coord : ∀ t, (U.rawPlace R fit e t).2.2 = (V.rawPlace R fit' f t).2.2

variable {Q σ k} {n : ℕ} (p : Region U V σ Q n)

include p in
theorem RawPair.direct (hk : k + (h - a) + 2 ≤ n)
    (e : {i // U.Z.good i}) (f : {j // V.Z.good j}) (r : UnitPair Q σ k e.val f.val) :
    RawPair R fit fit' Q σ k (.inl (.inr e)) (.inl (.inr f)) := by
  refine ⟨.direct _ _ r, fun t => congrArg RawId.direct (r.name t), ?_, ?_, ?_, ?_⟩
  · intro t; rw [direct_place]; exact r.group
  · intro t; rw [direct_place]; exact r.group' p
  · intro t; rw [direct_place, direct_place]; exact r.hosts t
  · intro t
    rw [direct_place, direct_place]
    exact congrArg Sum.inl (Prod.ext (r.drop p hk t)
      (congrArg (R.root true) (r.plug p hk e.property f.property t)))

include p in
theorem RawPair.detour (hk : k + (h - a) + 2 ≤ n)
    (j : Fin (Detour.steps (terminalWidth Δ Y))) (e : U.Z.Exceptional) (f : V.Z.Exceptional)
    (r : UnitPair Q σ k e.val f.val) :
    RawPair R fit fit' Q σ k (.inr (j, e)) (.inr (j, f)) := by
  refine ⟨.detour _ _ _ r, fun t => congrArg (RawId.detour j.val) (r.name _), ?_, ?_, ?_, ?_⟩
  · intro t; rw [detour_place]; exact r.group
  · intro t; rw [detour_place]; exact r.group' p
  · intro t; simp only [detour_place, stop_side]; exact r.hosts _
  · intro t; rw [detour_place, detour_place]; exact r.stop p hk R _

include p in
/-- A hit at one endpoint identifies a supply at both endpoints.
The peer can use one extra step in the neighborhood relation. -/
theorem Region.raw (hk : k + (h - a) + 3 ≤ n) (e : U.Raw R) (t : Bool) (z : V.G.V)
    (hg : (U.rawPlace R fit e t).1 = σ) (hv : Q k (U.rawPlace R fit e t).2.1 z) :
    ∃ f, (V.rawPlace R fit' f t).2.1 = z ∧ RawPair R fit fit' Q σ (k + 1) e f := by
  rcases e with (⟨⟨v, x⟩, b⟩|j)|⟨i, j⟩
  · simp only [local_place] at hg hv
    obtain ⟨d, hd, hl⟩ := (p.toSurvey.agree (by omega) hv).local_wire hg R b
    refine ⟨.inl (.inl ⟨(z, x), d⟩), by rw [local_place], .inside .., fun _ => hd, ?_, ?_, ?_, ?_⟩
    · intro t; rw [local_place]; exact hg
    · intro t; rw [local_place]; exact hg
    · intro t; rw [local_place, local_place]; exact p.widen (by omega) hv
    · intro t
      simp only [local_place]
      unfold localSupply at hl
      rw [hl]
      rfl
  · simp only [direct_place] at hg hv
    obtain ⟨f, hf, hr⟩ := p.unit_pair (by omega) j.val t z hg hv
    let g := Subtype.mk f (hr.good.mp j.2)
    exact ⟨.inl (.inr g), by rw [direct_place]; exact hf,
      RawPair.direct R fit fit' p (by omega) j g hr⟩
  · simp only [detour_place, stop_side] at hg hv
    obtain ⟨f, hf, hr⟩ := p.unit_pair (by omega) j.val _ z hg hv
    let g : V.Z.Exceptional := ⟨f, mt hr.good.mpr j.2⟩
    exact ⟨.inr (i, g), by simp only [detour_place, stop_side]; exact hf,
      RawPair.detour R fit fit' p (by omega) i j g hr⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Visible and hidden span names at a reset station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)
  (fit : U.Fits R c)

abbrev At := Cell a × (U.result R fit).vertex
abbrev station (σ : Cell a) (v : U.G.V) (loc : Coord R h a Δ) :=
  (U.place R fit).symm (σ, v, loc)

inductive PortId (R : Rotor F Y w) (h : ℕ) where
  | border (b : Cell h) (j : ℕ)
  | demand (t : Bool) (name : ℕ)
  | line (visible t : Bool) (id : RawId R h)

variable (v : U.At R fit)
local notation "Dlv" => U.result R fit

def portKey : Reset.Port U.post Dlv v → PortId R h
  | .inl ⟨.inl q, _⟩ => .border (U.G.units.place q.val.1).2 q.val.2.val
  | .inl ⟨.inr (e, t), _⟩ => .line true t (U.rawKey R e.val t)
  | .inr ⟨.inl e, _⟩ => .demand false (endName U.post e false)
  | .inr ⟨.inr (.inl e), _⟩ => .demand true (endName U.post e true)
  | .inr ⟨.inr (.inr e), _⟩ => .line false false (U.rawKey R e false)

theorem exterior_key (j : U.post.toPresentation.BorderSpan) (hj) :
    U.portKey R fit v (exterior U.post Dlv v j hj) =
      .border (U.G.units.place j.val.1).2 j.val.2.val := rfl

theorem demand_key (e : U.G.E) (t : Bool) (he) :
    U.portKey R fit v (demand U.post Dlv v e t he) = .demand t (endName U.post e t) := by
  cases t <;> rfl

theorem supply_key (e : U.Raw R) (t : Bool) (he) :
    U.portKey R fit v (supply U.post Dlv v e t he) =
      if ((Dlv).supply e).1 = ((Dlv).supply e).2 then .line false false (U.rawKey R e false)
      else .line true t (U.rawKey R e t) := by
  unfold supply
  split <;> rfl

theorem supply_place (e : U.Raw R) (t : Bool) :
    U.place R fit (supplySite Dlv e t) = U.rawPlace R fit e t := rfl

theorem demand_place (e : U.G.E) (t : Bool) :
    U.place R fit (demandSite Dlv e t) = U.oldPlace R fit e t := by rw [oldPlace, point_eq]

theorem owner_place (p : U.G.V × Cell h) :
    U.place R fit ((Dlv).owner p) = (U.Z.group p.2, p.1,
      .inl (((U.Z.leaf p).drop a).2, R.root false (U.delivery.terminal p))) := rfl

private theorem unique_border {j k : U.post.toPresentation.BorderSpan}
    (he : (Dlv).owner (U.G.units.place j.val.1) = (Dlv).owner (U.G.units.place k.val.1))
    (hb : (U.G.units.place j.val.1).2 = (U.G.units.place k.val.1).2) (hs : j.val.2.val = k.val.2.val) :
    j = k := by
  have hp := congrArg (U.place R fit) he
  rw [owner_place, owner_place] at hp
  have hplace : U.G.units.place j.val.1 = U.G.units.place k.val.1 :=
    Prod.ext (congrArg (fun p => p.2.1) hp) hb
  apply Subtype.ext
  refine Prod.ext ?_ (Fin.ext hs)
  apply U.post.vertex.injective
  rw [U.post.vertex_eq, U.post.vertex_eq, hplace]

private theorem unique_demand {e f : U.G.E} (t : Bool)
    (he : demandSite Dlv e t = demandSite Dlv f t) (hh : endName U.post e t = endName U.post f t) : e = f := by
  apply U.end_inj_at _ hh
  have hp := congrArg (U.place R fit) he
  simp only [demand_place, old_place] at hp
  exact congrArg (fun p => p.2.1) hp

theorem portKey_injective : Function.Injective (U.portKey R fit v) := by
  rintro (⟨j|⟨e, t⟩, he⟩ | ⟨e|e|e, he⟩) (⟨k|⟨f, b⟩, hf⟩ | ⟨f|f|f, hf⟩) hh <;>
    simp [portKey] at hh
  · have : j = k := unique_border U R fit (he.trans hf.symm) hh.1 hh.2
    subst k; rfl
  · obtain ⟨rfl, hk⟩ := hh
    have hp : U.rawPlace R fit e.val t = U.rawPlace R fit f.val t :=
      congrArg (U.place R fit) (he.trans hf.symm)
    have : e = f := Subtype.ext (U.raw_inj R fit (congrArg (fun p => p.2.1) hp) hk)
    subst f; rfl
  · have : e = f := unique_demand U R fit false (congrArg Prod.fst (he.trans hf.symm)) hh
    subst f; rfl
  · have : e = f := unique_demand U R fit true (congrArg Prod.fst (he.trans hf.symm)) hh
    subst f; rfl
  · have hp : U.rawPlace R fit e false = U.rawPlace R fit f false :=
      congrArg (fun p => U.place R fit p.1) (he.trans hf.symm)
    have : e = f := U.raw_inj R fit (congrArg (fun p => p.2.1) hp) hh
    subst f; rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Resident wires and their peer endpoints -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup S h u a Δ D Y w B'} {R : Rotor F Y w}
  {fit : U.Fits R c} {fit' : V.Fits R c} {σ : Cell a} {v : U.G.V} {z : V.G.V}
  {loc : Coord R h a Δ} {Q : Relation U V} {k n : ℕ} {t : Bool}

theorem RawPair.loop {e : U.Raw R} {f : V.Raw R} (r : RawPair R fit fit' Q σ k e f)
    (p : Region U V σ Q n) (hk : k ≤ n) :
    ((U.result R fit).supply e).1 = ((U.result R fit).supply e).2 ↔
      ((V.result R fit').supply f).1 = ((V.result R fit').supply f).2 := by
  have eqn : U.rawPlace R fit e false = U.rawPlace R fit e true ↔
      V.rawPlace R fit' f false = V.rawPlace R fit' f true := by
    have ha := p.same (p.widen hk (r.host false)) (p.widen hk (r.host true))
    simp only [Prod.ext_iff, r.group, r.group', r.coord, ha]
  simpa only [rawPlace, Bool.cond_false, Bool.cond_true, Equiv.apply_eq_iff_eq] using eqn

theorem old_at {e : U.G.E} : demandSite (U.result R fit) e t = U.station R fit σ v loc ↔
    U.oldPlace R fit e t = (σ, v, loc) := by
  rw [station, Equiv.eq_symm_apply, demand_place]

theorem raw_at {e : U.Raw R} : supplySite (U.result R fit) e t = U.station R fit σ v loc ↔
    U.rawPlace R fit e t = (σ, v, loc) := (U.place R fit).eq_symm_apply

variable (p : Region U V σ Q n) (hk : k + (h - a) + 3 ≤ n) (hr : Q k v z)
include p hk hr

theorem Region.old_here {e : U.G.E} (he : U.oldPlace R fit e t = (σ, v, loc)) :
    ∃ f, V.oldPlace R fit' f t = (σ, z, loc) ∧ UnitPair Q σ (k + 1) e f := by
  simp only [old_place, Prod.mk.injEq] at he
  obtain ⟨f, hf, r⟩ := p.unit_pair (by omega) e t z he.1 (he.2.1 ▸ hr)
  refine ⟨f, ?_, r⟩
  simp only [old_place, Prod.mk.injEq]
  refine ⟨r.group' p, hf, ?_⟩
  rw [← he.2.2]
  exact congrArg Sum.inl (Prod.ext (r.drop p (by omega) t).symm
    (congrArg (R.root false) (r.terminal p (by omega) t).symm))

theorem Region.raw_here {e : U.Raw R} (he : U.rawPlace R fit e t = (σ, v, loc)) :
    ∃ f, V.rawPlace R fit' f t = (σ, z, loc) ∧ RawPair R fit fit' Q σ (k + 1) e f := by
  obtain ⟨f, hf, r⟩ := p.raw R fit fit' hk e t z (by rw [he]) (by rwa [he])
  exact ⟨f, Prod.ext (r.group' t) (Prod.ext hf ((r.coord t).symm.trans (by rw [he]))), r⟩

theorem Region.raw_pair {e : U.Raw R} {f : V.Raw R}
    (he : U.rawPlace R fit e t = (σ, v, loc)) (hf : V.rawPlace R fit' f t = (σ, z, loc))
    (hn : U.rawKey R e t = V.rawKey R f t) : RawPair R fit fit' Q σ (k + 1) e f := by
  obtain ⟨j, hj, r⟩ := p.raw_here (fit' := fit') hk hr he
  have : j = f := V.raw_inj R fit' (by rw [hj, hf]) ((r.key t).symm.trans hn)
  rwa [this] at r

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # The scheduled reset has a short local factorization -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Spectral.Packet Classical

namespace Delivery
variable {P U X W F : Type} [Fintype P] [Field F] [Fintype X] [Fintype U]
  {leaf : P → X} {point : U → Bool → P} {good : U → Prop}
  {edge : U → W} {outLeaf : W → Bool → X} {cap : W → ℝ} {Y w : ℕ}
  {out : ∀ x, Port outLeaf cap Y x ↪ Fin Y} {l : P → ℝ} {u : ℝ}
  (d : Delivery leaf point good edge outLeaf cap Y w out l u) (R : Rotor F Y w)

theorem deploy_simple : (d.deployRule R).Simple := by
  unfold deployRule
  apply Rule.Simple.join_outputs
  apply Rule.Simple.select
  apply Rule.Simple.place
  apply Rule.Simple.parallel
  intro x
  exact R.deploy_simple _ _ _ _ _ _

end Delivery

namespace Schedule
variable {V A U F : Type} [Fintype V] [Fintype U] [Field F] {h a k Y w L : ℕ}
  {T : Demands V A U h} {N : V → Finset V} {d : V → V → ℕ}
  {l : V → Cell h → ℝ} {u g ε : ℝ}
  (Z : Schedule T N d a k l u g ε) {o : Z.Plugs Y}
  (D : Z.Dispatch o w) (R : Rotor F Y w)
  (sw : Detour.Switch (Site V (h - a) × Fin Y) L)
  (ok : ∀ i : U, Z.terminal D (T.point i true) ∈ sw.near (Z.terminal D (T.point i false)))

theorem rule_simple : (Z.rule D R sw ok).Simple := by
  unfold rule
  apply Rule.Simple.partition
  · apply Rule.Simple.congr
    · exact (D.deploy_simple R).place _
    · rfl
  · apply Rule.Simple.place
    unfold Detour.Switch.rule
    apply Rule.Simple.congr
    · exact Rule.path_simple _ _
    · rfl

end Schedule
end OAI.LinearAlgebra.MatrixExponent.Packing

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)

theorem result_simple (fits : U.Fits R c) : (U.result R fits).rule.Simple :=
  U.Z.rule_simple U.delivery R _ _

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Serializing the outgoing spans and local tensor after a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Allocation

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} {p : S.Posting r G}
  {B' W : ℝ} {Hcap D : ℕ}
  {q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D}
  {m d h' e ℓ cap : ℕ} {len : B ℓ → ℕ} {decode : B cap → (B e → ℕ → Bool) → F}

local notation "U" => scheme m d h' e ℓ cap len decode
local notation "Host" => endHost (q := q)
local notation "R" => Post.record d e ℓ (Format.addr cap)

variable (A : Allocation p q (scheme m d h' e ℓ cap len decode)) (size : Face p q → B ℓ)
  (payload : Cell a × q.vertex → B cap) (nav : B m → B d → B m)

def header : Face p q → (Post.field d e ℓ).obj
  | .inl j => (size (.inl j), S.direction r (p.vertex j.val.1, j.val.2), false, 0, 0)
  | .inr (b, t) => (size (.inr (b, t)), t, true, A.index (Host b t) (Host b (!t)), A.unitSeat b (!t))

def fields (v : Cell a × q.vertex) : B e → (Post.field d e ℓ).obj :=
  Function.extend (A.seat v) (fun j => A.header size j.val) (fun _ => Post.unused)

def localRecord (v : Cell a × q.vertex) : (R).obj :=
  (true, A.fields size v, payload v)

def records (x : B m) (y : B h') : (R).obj :=
  Function.extend A.vertex (A.localRecord size payload) (fun _ => Post.vacant) (x, y, 0)

def output : (U).format.obj := fun v => (nav v, (R).serial ∘ A.records size payload v)

local notation "out" => A.output size payload nav

theorem read_output (v : (U).Vtx) :
    (U).pattern out v = pattern len decode (A.records size payload v.1 v.2.1) :=
  congrArg (pattern len decode) ((R).serial.symm_apply_apply _)

theorem record_at (v : Cell a × q.vertex) :
    A.records size payload (A.vertex v).1 (A.vertex v).2.1 = A.localRecord size payload v :=
  A.vertex.injective.extend_apply _ _ v

theorem record_vacant (v : (U).Vtx) (hv : v ∉ Set.range A.vertex) :
    A.records size payload v.1 v.2.1 = Post.vacant := by
  have he : (v.1, v.2.1, (0 : B 0)) = v := Prod.ext rfl (Prod.ext rfl (Fin.eq_zero _).symm)
  unfold records
  rw [he]
  exact Function.extend_apply' _ _ _ hv

theorem stored (v : Cell a × q.vertex) :
    Dense.used (Post.order d e ℓ cap ((out (A.host v.2)).2 (A.block v.1))).val ≤
      Dense.used (payload v).val + (Post.headerFmt d e ℓ).width := by
  change Dense.used (Post.order d e ℓ cap
    ((R).serial (A.records size payload (A.vertex v).1 (A.vertex v).2.1))).val ≤ _
  rw [record_at]
  exact Post.order_length (A.localRecord size payload v)

theorem used (j : Face p q) :
    (A.records size payload (A.span j).1.1 (A.span j).1.2.1).2.1 (A.span j).2 = A.header size j := by
  let v := whereAt p q j
  change (A.records size payload (A.vertex v).1 (A.vertex v).2.1).2.1 (A.slot j) = _
  rw [record_at]
  let t : Visible p q v := ⟨j, rfl⟩
  change A.fields size v (A.seat v t) = A.header size t.val
  rw [fields, (A.seat v).injective.extend_apply]

theorem idle (t : (U).Span) (ht : t ∉ Set.range A.span) :
    (A.records size payload t.1.1 t.1.2.1).2.1 t.2 = Post.unused := by
  rcases t with ⟨v, j⟩
  by_cases hv : v ∈ Set.range A.vertex
  · obtain ⟨w, rfl⟩ := hv
    rw [record_at]
    have hn : j ∉ Set.range (A.seat w) := by
      rintro ⟨t, rfl⟩
      exact ht ⟨t.val, Prod.ext (congrArg A.vertex t.property) (A.slot_eq w t)⟩
    change A.fields size w j = _
    rw [fields, Function.extend_apply' _ _ _ hn]
  · rw [record_vacant _ _ _ _ hv]
    rfl

theorem exposed_direction (j : p.toPresentation.BorderSpan) :
    (U).direction out (A.span (.inl j)) = S.direction r (p.vertex j.val.1, j.val.2) := by
  rw [Scheme.direction, read_output]
  simp only [pattern, used, header]

variable (h₀ : len 0 = 0) (hlen : ∀ j, len (size j) = visibleWidth p q j)

include h₀ hlen in
theorem lengths : A.Lengths out where
  used j := by
    rw [Scheme.width, read_output]
    change len ((A.records _ _ _ _).2.1 _).1 = _
    rw [A.used]
    rcases j with j|⟨b, t⟩ <;> exact hlen _
  idle t ht := by
    rw [Scheme.width, read_output]
    change len ((A.records _ _ _ _).2.1 _).1 = _
    rw [A.idle _ _ _ ht]
    exact h₀

local notation "l" => A.lengths size payload nav h₀ hlen

theorem agrees
    (hop : ∀ (b : q.Survivors) t,
      nav (A.host (Host b t)) (A.index (Host b t) (Host b (!t))) = A.host (Host b (!t)))
    (H : ∀ v (x : B e → ℕ → Bool), decode (payload v) x =
      Transcript.sample ((q.contract G.units).table v)
        (fun j => let y := (visibleBits p q v).symm j; x (A.seat v y.1) y.2.val)) :
    A.Agrees l where
  sample v t := by
    rw [table_eq len decode out _ _ (A.read_output size payload nav _), record_at]
    change decode (payload v) _ = _
    rw [H]
    apply congrArg
    funext i
    obtain ⟨⟨j, b⟩, rfl⟩ := (visibleBits p q v).surjective i
    dsimp only [Function.comp_apply]
    rw [Equiv.symm_apply_apply, A.pin_at]
    have ht : b.val < (U).width out (A.vertex v, A.seat v j) := by
      rw [A.length_at l]
      exact b.isLt
    exact dite_eq_left ht
  vacant v hv t := by
    rw [table_eq len decode out _ _ (A.read_output size payload nav _), record_vacant _ _ _ _ hv]
    rfl
  outside j := by
    rw [Scheme.peer, read_output]
    simp only [pattern, used, header, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  idle t ht := by
    rw [Scheme.peer, read_output]
    simp only [pattern, A.idle _ _ t ht, Post.unused, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  dir b t := by
    rw [Scheme.direction, read_output]
    simp only [pattern, used, header]
  link b t := by
    dsimp only
    rw [read_output]
    simp only [pattern, used, header, ↓reduceIte]
  nav b t := hop b t

theorem boundary (H : A.Agrees l) (t : slots x ⊕ slots y) :
    let b := p.toSeating.ends (boundaryEnd _ t)
    let b' := (A.presentation l H).toSeating.ends (boundaryEnd _ t)
    (U).width out b'.1 = S.width r b.1 ∧ (U).direction out b'.1 = S.direction r b.1 ∧
      b'.2.val = b.2.val := by
  obtain ⟨j, rfl⟩ := p.toPresentation.exteriorBits.surjective t
  dsimp only [presentation]
  rw [p.toPresentation.border_pin, A.exposed_pin]
  exact ⟨(l).used (.inl j.1), A.exposed_direction size payload nav j.1, rfl⟩

theorem floor (H : A.Agrees l) {w : ℕ} (hw : ∀ b, w ≤ p.toPresentation.borderWidth b) :
    ∀ b, w ≤ (A.presentation l H).borderWidth b := by
  let p' := A.presentation l H
  intro b
  let j : p'.BorderBit := ⟨b, ⟨0, b.property.1⟩⟩
  obtain ⟨t, ht⟩ := p.toPresentation.exteriorBits.surjective (p'.exteriorBits j)
  have h := (A.boundary size payload nav h₀ hlen H (p'.exteriorBits j)).1
  rw [p'.border_pin, ← ht, p.toPresentation.border_pin] at h
  exact (hw _).trans_eq h.symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Allocation
end

/-! # Posting a reset network from descriptions of the local tensors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Book

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} {p : S.Posting r G}
  {B' W' : ℝ} {Hcap D : ℕ}
  {q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W' Hcap D}
  {m d h' e cap : ℕ} (b : Book S u e cap)
  (A : Allocation p q (b.scheme m d h')) (nav : B m → B d → B m)

abbrev data (v : Cell a × q.vertex) := b.payload p q v (A.seat v)

abbrev output := A.output (b.size p q) (b.data A) nav

local notation "Host" => Allocation.endHost (q := q)

/-- A recipe witnesses the length bound. Only its decoded function
determines the emitted label. -/
structure Ready : Prop where
  sizes : ∀ j, b.len (b.put (p.toPresentation.borderWidth j)) = p.toPresentation.borderWidth j
  hop : ∀ (t : q.Survivors) i,
    nav (A.host (Host t i)) (A.index (Host t i) (Host t (!i))) = A.host (Host t (!i))
  describe : ∀ v, ∃ c : Recipe S e,
    run b.ord u c = localEval p q v (A.seat v) ∧ Dense.cost c.2 = inherited p q v b.ord
  budget : ∀ v, overhead S e + inherited p q v b.ord ≤ cap

namespace Ready

variable {b A nav} (H : b.Ready A nav)
local notation "out" => b.output A nav
local notation "U" => b.scheme m d h'

include H in
theorem length (j : Face p q) : b.len (b.size p q j) = visibleWidth p q j := by
  cases j with
  | inl j => exact H.sizes j
  | inr _ => exact b.unit

include H in
theorem lengths : A.Lengths out := A.lengths (b.size p q) (b.data A) nav b.zero H.length

include H in
theorem data_spec (v : Cell a × q.vertex) :
    decoder b.ord u cap (b.data A v) = localEval p q v (A.seat v) ∧
      Dense.used (b.data A v).val ≤ overhead S e + inherited p q v b.ord := by
  obtain ⟨c, hc, hl⟩ := H.describe v
  rw [← hl]
  exact canonical_spec c hc (by rw [hl]; exact H.budget v)

theorem agrees : A.Agrees H.lengths :=
  A.agrees (b.size p q) (b.data A) nav b.zero H.length H.hop (fun v t => congrFun (H.data_spec v).1 t)

def posting : (U).Posting out (G.afterReset q) := A.posting H.lengths H.agrees

theorem boundary (t : slots x ⊕ slots y) :
    let i := p.toSeating.ends (boundaryEnd _ t)
    let j := H.posting.toSeating.ends (boundaryEnd _ t)
    (U).width out j.1 = S.width r i.1 ∧ (U).direction out j.1 = S.direction r i.1 ∧
      j.2.val = i.2.val :=
  A.boundary (b.size p q) (b.data A) nav b.zero H.length H.agrees t

theorem floor {w : ℕ} (hw : ∀ j, w ≤ p.toPresentation.borderWidth j) :
    ∀ j, w ≤ H.posting.toPresentation.borderWidth j :=
  A.floor (b.size p q) (b.data A) nav b.zero H.length H.agrees hw

theorem palette (W : Finset ℕ) (hw : ∀ j, p.toPresentation.borderWidth j ∈ W) :
    ∀ j, H.posting.toPresentation.borderWidth j ∈ W := by
  let p' := H.posting.toPresentation
  intro j
  let x : p'.BorderBit := ⟨j, ⟨0, j.property.1⟩⟩
  obtain ⟨t, ht⟩ := p.toPresentation.exteriorBits.surjective (p'.exteriorBits x)
  have hh := (H.boundary (p'.exteriorBits x)).1
  rw [p'.border_pin, ← ht, p.toPresentation.border_pin] at hh
  exact Eq.mp (congrArg (· ∈ W) hh.symm) (hw t.1)

include H in
theorem stored (v : Cell a × q.vertex) :
    Dense.used (Post.order d e b.d cap ((out (A.host v.2)).2 (A.block v.1))).val ≤
      (Post.headerFmt d e b.d).width + overhead S e + inherited p q v b.ord := by
  refine (A.stored (b.size p q) (b.data A) nav v).trans ?_
  have := (H.data_spec v).2
  omega

end Ready
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Book
end

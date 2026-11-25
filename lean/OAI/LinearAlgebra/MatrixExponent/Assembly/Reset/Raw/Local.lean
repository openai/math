import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Routes
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Prefix
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Repost
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Move

/-! # Consistency of the reserved slot of a matched good unit -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  {U V : Setup S h u a Δ D Y w B'} {σ : Cell a} {v : U.G.V} {z : V.G.V}
  {t : Bool} {e : U.G.E} {f : V.G.E}

private theorem addr_aux {i j : ℕ} (hi : i ≤ h) (hj : j ≤ h) (p q : Cell h) (he : i = j) (hp : p = q) :
    (⟨i, ancestor hi p⟩ : Chart.Address) = ⟨j, ancestor hj q⟩ := by cases he; cases hp; rfl

theorem Agree.address (c : Agree U V σ v z) (r : Related U V v z t e f)
    (he : Scheme.side U.G e t = v) (hf : Scheme.side V.G f t = z) :
    Chart.address (U.Z.link e) = Chart.address (V.Z.link f) := by
  have hd := (c.contact r he hf).1.depth
  have hm : U.Z.π (U.G.ix e) = V.Z.π (V.G.ix f) := by rw [c.mix, r.ix]
  exact addr_aux _ _ _ _ hd hm

private theorem drop_addr {k l : ℕ} (b : ℕ) (hg : l = k - b) (x : Cell k) :
    (⟨l, fun i => suffix b x (Fin.cast hg i)⟩ : Chart.Address) = ⟨k - b, suffix b x⟩ := by
  subst l; rfl

theorem Agree.drop_address (c : Agree U V σ v z) (r : Related U V v z t e f)
    (he : Scheme.side U.G e t = v) (hf : Scheme.side V.G f t = z) :
    Chart.address (dropContact a (U.Z.link e)) = Chart.address (dropContact a (V.Z.link f)) := by
  let d (p : Chart.Address) : Chart.Address := ⟨p.1 - a, suffix a p.2⟩
  calc
    _ = d (Chart.address (U.Z.link e)) := drop_addr a _ _
    _ = d (Chart.address (V.Z.link f)) := congrArg d (c.address r he hf)
    _ = _ := (drop_addr a _ _).symm

abbrev Fiber (U : Setup S h u a Δ D Y w B') (e : U.G.E) :=
  Dispatch.LinkFiber U.Z.good U.Z.link (U.Z.link e)

private theorem Agree.link_maps (c : Agree U V σ v z) (r : Related U V v z t e f)
    (he : Scheme.side U.G e t = v) (hf : Scheme.side V.G f t = z)
    (hg : U.Z.good e) (hs : U.Z.group (U.G.ix e) = σ) (p : U.Fiber e) :
    ∃ q : V.Fiber f, linkName U.post p.val.val = linkName V.post q.val.val := by
  obtain ⟨⟨b, hb⟩, hl⟩ := p
  change U.Z.link b = U.Z.link e at hl
  have hc : U.contact b = U.contact e := congrArg Sigma.fst hl
  have hroot : Scheme.side U.G b t = v := by rw [← U.ends, hc, U.ends, he]
  have hleaf : U.Z.leaf ((demands U.G).point b t) = U.Z.leaf ((demands U.G).point e t) := by
    rw [U.Z.routes b hb, U.Z.routes e hg, hl]
  have hgroup : U.Z.group (U.G.ix b) = σ := by
    exact ((U.Z.group_end b t).symm.trans ((congrArg (Site.group a) hleaf).trans
      (U.Z.group_end e t))).trans hs
  obtain ⟨j, hj, hroot', r'⟩ := c.fwd b t hb hgroup hroot
  have heq : V.Z.link j = V.Z.link f := by
    apply Chart.address_inj
    · change V.contact j = V.contact f
      apply unique_contact ((V.ends j t).trans hroot') ((V.ends f t).trans hf)
      rw [V.ends, V.ends, ← r'.label, ← r.label, ← U.ends, ← U.ends, hc]
    · rw [← c.address r' hroot hroot', ← c.address r he hf, hl]
  exact ⟨⟨⟨j, hj⟩, heq⟩, r'.name false⟩

variable [NeZero Y] [NeZero w]

theorem Agree.slot (c : Agree U V σ v z) (r : Related U V v z t e f)
    (he : Scheme.side U.G e t = v) (hf : Scheme.side V.G f t = z)
    (hg : U.Z.good e) (hg' : V.Z.good f) (hs : U.Z.group (U.G.ix e) = σ) :
    (U.delivery.slot ⟨e, hg⟩).val = (V.delivery.slot ⟨f, hg'⟩).val := by
  have hs' : V.Z.group (V.G.ix f) = σ := by rw [← r.ix, ← c.group, hs]
  let i : U.Fiber e := ⟨⟨e, hg⟩, rfl⟩
  let j : V.Fiber f := ⟨⟨f, hg'⟩, rfl⟩
  have h₁ := linkName_inj U.post U.hu U.Z (U.Z.link e)
  have h₂ := linkName_inj V.post V.hu V.Z (V.Z.link f)
  obtain ⟨p, hp⟩ := Dispatch.equivalent _ _ h₁ h₂ (c.link_maps r he hf hg hs)
    (c.symm.link_maps r.symm hf he hg' hs')
  have hij : p i = j := h₂ ((hp i).trans (r.name false))
  have heq := U.local_delivery.slot_congr V.local_delivery p hp (c.contact r he hf).2 i
  rw [hij] at heq
  exact heq

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # A reset label consists of span headers and one encoded contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Coloring
variable {F : Type} [Field F] {m d h e ℓ cap : ℕ}

/-- Outside the stated span length the decoder sees zeros. -/
def totalize (w : B e → ℕ) (x : Positions w → Bool) (s : B e) (i : ℕ) :=
  if H : i < w s then x ⟨s, ⟨i, H⟩⟩ else false

def pattern (len : B ℓ → ℕ) (decode : B cap → (B e → ℕ → Bool) → F)
    (r : (Post.record d e ℓ (.addr cap)).obj) : Pattern F d 0 e where
  width _ t := len (r.2.1 t).1
  direction _ t := (r.2.1 t).2.1
  peer _ t := if (r.2.1 t).2.2.1 then some ((r.2.1 t).2.2.2.1, 0, (r.2.1 t).2.2.2.2) else none
  value _ x := if r.1 then decode r.2.2
    (totalize (fun t => len (r.2.1 t).1) (fun i => x i.1 i.2)) else 1

abbrev scheme (m d h e ℓ cap : ℕ) (len : B ℓ → ℕ) (decode : B cap → (B e → ℕ → Bool) → F) : Scheme F :=
  ⟨m, d, h, 0, e, Post.width d e ℓ cap, pattern len decode ∘ (Post.record d e ℓ (.addr cap)).serial.symm⟩

variable (len : B ℓ → ℕ) (decode : B cap → (B e → ℕ → Bool) → F)
local notation "U" => scheme m d h e ℓ cap len decode

theorem table_eq (out : (U).format.obj) (v : (U).Vtx) (r : (Post.record d e ℓ (.addr cap)).obj)
    (hr : (U).pattern out v = pattern len decode r) (x : (U).LocalPin out v → Bool) :
    (U).table out v x = if r.1 then
      decode r.2.2 (totalize (fun t => (U).width out (v, t)) x) else 1 := by
  have eq (P : Pattern F d 0 e) (he : P = pattern len decode r) (j : B 0)
      (z : Positions (P.width j) → Bool) :
      P.value j (fun s i => z ⟨s, i⟩) =
        if r.1 then decode r.2.2 (totalize (P.width j) z) else 1 := by
    subst P
    rfl
  exact eq _ hr _ x

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Dictionaries shared by all occurrences in one reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
open Coloring Packing
open scoped Classical

variable {F : Type} (S : Scheme F) (u e cap : ℕ)

structure Book (S : Scheme F) (u e cap : ℕ) where
  ord : B S.ℓ ≃ B S.ℓ
  d : ℕ
  len : B d → ℕ
  put : ℕ → B d
  zero : len 0 = 0
  unit : len (put u) = u

namespace Book

abbrev lenBits (W : Finset ℕ) := Nat.clog 2 (W.card + 3)

private theorem dictionary (W : Finset ℕ) :
    ∃ f : (ℕ → B (lenBits W)) × (B (lenBits W) → ℕ), f.2 0 = 0 ∧
      f.2 (f.1 u) = u ∧ ∀ j ∈ W, f.2 (f.1 j) = j := by
  let U := insert 0 (insert u W)
  have hc : U.card ≤ W.card + 3 :=
    ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _))).trans
      (Nat.le_succ _)
  obtain ⟨i⟩ : Nonempty (↥U ↪ B (lenBits W)) := Function.Embedding.nonempty_of_card_le (by
    simp only [Fintype.card_coe, Fintype.card_fin]
    exact hc.trans (Nat.le_pow_clog (by decide) _))
  let a : ↥U := ⟨0, by simp [U]⟩
  let k := i.trans (Equiv.swap (i a) 0).toEmbedding
  let len := Function.extend k Subtype.val (fun _ => 0)
  let put (j : ℕ) := if h : j ∈ U then k ⟨j, h⟩ else 0
  have hl (j : ℕ) (h : j ∈ U) : len (put j) = j := by
    simp only [put, dite_eq_left h, len, k.injective.extend_apply]
  have hz : len 0 = 0 := by
    rw [← show k a = 0 from Equiv.swap_apply_left _ _]
    exact k.injective.extend_apply _ _ a
  exact ⟨(put, len), hz, hl _ (by simp [U]), fun j hj => hl j (by simp [U, hj])⟩

variable (ord : B S.ℓ ≃ B S.ℓ) (W : Finset ℕ)

def make : Book S u e cap where
  ord := ord
  d := lenBits W
  len := (dictionary u W).choose.2
  put := (dictionary u W).choose.1
  zero := (dictionary u W).choose_spec.1
  unit := (dictionary u W).choose_spec.2.1

theorem represent {j : ℕ} (hj : j ∈ W) :
    let b := make S u e cap ord W
    b.len (b.put j) = j :=
  (dictionary u W).choose_spec.2.2 _ hj

variable {S u e cap} [Field F] [Fintype F] (b : Book S u e cap)

abbrev scheme (m' d' h' : ℕ) :=
  Reset.scheme m' d' h' e b.d cap b.len (decoder b.ord u cap)

variable {T : Type} [Fintype T] {x y : Wire} {L : Fringe x y T} {h a : ℕ}
  {G : HostNet F L h u} {r : S.format.obj} (p : S.Posting r G)
  {B' W' : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W' Hcap D)

def size : Face p q → B b.d := b.put ∘ visibleWidth p q

def payload (v : Cell a × q.vertex) (seat : Visible p q v ↪ B e) : B cap :=
  canonical b.ord u cap (localEval p q v seat)

end Book
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Matching reset deliveries on corresponding leaves -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  (U : Setup S h u a Δ D Y w B') (v : U.G.V) (x : Schedule.Address h)

abbrev Occ := Dispatch.Base U.Z.leaf (v, x)
abbrev End := GoodEnd U.Z.leaf (demands U.G).point U.Z.good (v, x)

theorem end_root (q : U.End v x) : Scheme.side U.G q.val.1.val q.val.2 = v :=
  (point_side ..).symm.trans (congrArg (fun y : Site U.G.V h => y.1) q.2)

theorem end_group (q : U.End v x) :
    U.Z.group (U.G.ix q.val.1.val) = Site.group a (v, x) :=
  (U.Z.group_end ..).symm.trans (congrArg (Site.group a) q.2)

variable [NeZero Y] [NeZero w]

def data : Dispatch.Site (U.Occ v x) (U.End v x) Y :=
  Dispatch.site U.delivery (occName (G := U.G)) (endName U.post) (v, x)

private def port (q : U.End v x) :=
  dropSlot a U.Z.lo (v, x) (portOf _ _ _ _ _ _ Y U.delivery.agree U.delivery.slot q)

private theorem port_key (q : U.End v x) :
    U.chart.plugKey U.G.cs (relHi a U.Z.depth) U.Z.capacity _ (U.port v x q) =
      (q.val.2, U.chart.label v (Scheme.side U.G q.val.1.val (!q.val.2)),
       Chart.address (dropContact a (U.Z.link q.val.1.val)), (U.delivery.slot q.val.1).val) := by
  rw [← U.ends]
  rfl

variable {U v x} {V : Setup S h u a Δ D Y w B'} {σ : Cell a} {z : V.G.V}
  (c : Agree U V σ v z) (hx : Site.group a (v, x) = σ)

include c hx in
theorem Agree.output {q : U.End v x} {q' : V.End z x}
    (ht : q.val.2 = q'.val.2) (r : Related U V v z q.val.2 q.val.1.val q'.val.1.val) :
    (U.data v x).output q = (V.data z x).output q' := by
  have he := U.end_root v x q
  have hf := V.end_root z x q'
  rw [← ht] at hf
  have haddr := c.drop_address r he hf
  have hslot := c.slot r he hf q.val.1.property q'.val.1.property ((U.end_group v x q).trans hx)
  have hp : U.chart.plugKey U.G.cs (relHi a U.Z.depth) U.Z.capacity _ (U.port v x q) =
      V.chart.plugKey V.G.cs (relHi a V.Z.depth) V.Z.capacity _ (V.port z x q') := by
    rw [port_key, port_key, ← ht, r.label, haddr, hslot]
  exact U.chart.plugs_eq U.G.cs (relHi a U.Z.depth) U.Z.capacity
    V.chart V.G.cs (relHi a V.Z.depth) V.Z.capacity c.relative c.symm.relative
    U.bound V.bound (Site.drop a (v, x)).2 (U.port v x q) (V.port z x q') hp

include c hx in
private theorem Agree.occ_map (p : U.Occ v x) :
    ∃ p' : V.Occ z x, (U.data v x).occurrence p = (V.data z x).occurrence p' ∧
      (U.data v x).load p = (V.data z x).load p' := by
  obtain ⟨⟨t, j⟩, he⟩ := p
  have ht : t = v := congrArg (fun p : Site U.G.V h => p.1) he
  subst t
  have hj : U.Z.group j = σ := (U.Z.leaf_group (v, j)).symm.trans
    ((congrArg (Site.group a) he).trans hx)
  have hy := (c.leaf j hj).symm.trans (congrArg Prod.snd he)
  exact ⟨⟨(z, j), Prod.ext rfl hy⟩, rfl, congrArg (· / B') (c.load j hj)⟩

include c hx in
omit [NeZero Y] [NeZero w] in
theorem Agree.end_map (p : U.End v x) :
    ∃ q : V.End z x, p.val.2 = q.val.2 ∧ Related U V v z p.val.2 p.val.1.val q.val.1.val := by
  have hv := U.end_root v x p
  have hs := (U.end_group v x p).trans hx
  obtain ⟨f, hf, hz, hr⟩ := c.fwd _ _ p.val.1.property hs hv
  have he : (demands U.G).point p.val.1.val p.val.2 = (v, U.G.ix p.val.1.val) :=
    Prod.ext ((point_side ..).trans hv) rfl
  have he' : (demands V.G).point f p.val.2 = (z, U.G.ix p.val.1.val) :=
    Prod.ext ((point_side ..).trans hz) hr.ix.symm
  have hleaf : V.Z.leaf ((demands V.G).point f p.val.2) = (z, x) := by
    rw [he']
    apply Prod.ext
    · rfl
    rw [← c.leaf _ hs, ← he, p.2]
  exact ⟨⟨(⟨f, hf⟩, p.val.2), hleaf⟩, rfl, hr⟩

private def occKey (U : Setup S h u a Δ D Y w B') (v : U.G.V) (x : Schedule.Address h)
    (p : U.Occ v x) := ((U.data v x).occurrence p, (U.data v x).load p)

private def endKey (U : Setup S h u a Δ D Y w B') (v : U.G.V) (x : Schedule.Address h)
    (p : U.End v x) := ((U.data v x).contact p, (U.data v x).input p, (U.data v x).output p)

private theorem occ_inj : Function.Injective (U.occKey v x) :=
  fun _ _ h => occName_inj U.Z (v, x) (Prod.mk.inj h).1

private theorem end_inj : Function.Injective (U.endKey v x) :=
  fun _ _ h => endName_inj U.post U.hu U.Z (v, x) (Prod.mk.inj h).1

include c hx in
private theorem Agree.endKey_map (p : U.End v x) : ∃ q : V.End z x, U.endKey v x p = V.endKey z x q := by
  obtain ⟨q, ht, hr⟩ := c.end_map hx p
  refine ⟨q, Prod.ext ?_ (Prod.ext ?_ (c.output hx ht hr))⟩
  · change endName U.post _ _ = endName V.post _ _
    rw [← ht, hr.name]
  · exact congrArg (fun j : Cell h => (cellIndex h j).val) hr.ix

include c hx in
/-- Matching sibling blocks and incident units identify all local
inputs to the deterministic routing schedule. -/
theorem Agree.matching :
    ∃ e : U.Occ v x ≃ V.Occ z x, ∃ f : U.End v x ≃ V.End z x,
      Dispatch.Match (U.data v x) (V.data z x) e f := by
  have hx' : Site.group a (z, x) = σ := hx
  have ho := c.occ_map hx
  have ho' := c.symm.occ_map hx'
  obtain ⟨e, he⟩ := Dispatch.equivalent (U.occKey v x) (V.occKey z x) occ_inj occ_inj
    (by simpa only [occKey, Prod.mk.injEq] using ho) (by simpa only [occKey, Prod.mk.injEq] using ho')
  obtain ⟨f, hf⟩ := Dispatch.equivalent (U.endKey v x) (V.endKey z x) end_inj end_inj
    (c.endKey_map hx) (c.symm.endKey_map hx')
  simp only [occKey, endKey, Prod.mk.injEq] at he hf
  exact ⟨e, f, fun p => (he p).1, fun q => (hf q).1, fun p => (he p).2,
    fun q => (hf q).2.1, fun q => (hf q).2.2⟩

include c hx in
theorem Agree.route : Dispatch.schedule U.delivery (occName (G := U.G)) (endName U.post) (v, x) =
    Dispatch.schedule V.delivery (occName (G := V.G)) (endName V.post) (z, x) := by
  obtain ⟨e, f, he⟩ := c.matching hx
  exact Dispatch.schedule_eq he

include c hx in
theorem Agree.layers : U.delivery.layers (v, x) = V.delivery.layers (z, x) := by
  rw [U.local_delivery.layers_eq, V.local_delivery.layers_eq]
  exact congrArg Dispatch.Route.layers (c.route hx)

include c hx in
theorem Agree.config (i : Fin (U.delivery.layers (v, x))) (j : Fin (V.delivery.layers (z, x)))
    (hij : i.val = j.val) : U.delivery.config (v, x) i = V.delivery.config (z, x) j := by
  rw [U.local_delivery.config_eq, V.local_delivery.config_eq, hij]
  exact congrArg (fun r : Dispatch.Route Y w => r.config j.val) (c.route hx)

include c hx in
theorem Agree.lane {q : U.End v x} {q' : V.End z x} (ht : q.val.2 = q'.val.2)
    (r : Related U V v z q.val.2 q.val.1.val q'.val.1.val) :
    ((U.delivery.lane (v, x) q).1.val, (U.delivery.lane (v, x) q).2) =
      ((V.delivery.lane (z, x) q').1.val, (V.delivery.lane (z, x) q').2) := by
  rw [U.local_delivery.lane_eq, V.local_delivery.lane_eq, ← ht, r.name]
  exact congrArg (fun k : Dispatch.Route Y w => k.lane (endName V.post q'.val.1.val q.val.2))
    (c.route hx)

include c in
theorem Agree.terminal (j : Cell h) (hj : U.Z.group j = σ) :
    U.delivery.terminal (v, j) = V.delivery.terminal (z, j) := by
  let x := (U.Z.leaf (v, j)).2
  let p : U.Occ v x := ⟨(v, j), rfl⟩
  let q : V.Occ z x := ⟨(z, j), Prod.ext rfl (c.leaf j hj).symm⟩
  have hx : Site.group a (v, x) = σ := (U.Z.leaf_group (v, j)).trans hj
  change U.delivery.terminal p.val = V.delivery.terminal q.val
  rw [U.local_delivery.terminal_eq (v, x) p, V.local_delivery.terminal_eq (z, x) q]
  exact congrArg (fun k : Dispatch.Route Y w => k.terminal (cellIndex h j).val) (c.route hx)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Naming reset wires at each incident host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)
  (fit : U.Fits R c)

abbrev Raw := U.Z.Wires (L := terminalWidth Δ Y) U.delivery R
abbrev Coord (R : Rotor F Y w) (h a Δ : ℕ) := R.Host (Schedule.Address (h - a)) (terminalWidth Δ Y)

def place : Cell a × (U.result R fit).vertex ≃ Cell a × U.G.V × Coord R h a Δ :=
  (Equiv.refl _).prodCongr (Schedule.splitHost R a h _)

def rawPlace (e : U.Raw R) (t : Bool) :=
  U.place R fit (cond t ((U.result R fit).supply e).2 ((U.result R fit).supply e).1)

inductive RawId (R : Rotor F Y w) (h : ℕ) where
  | path (x : Schedule.Address h) (out : Bool) (step name : ℕ)
  | layer (x : Schedule.Address h) (j : ℕ) (e : R.E)
  | direct (name : ℕ)
  | detour (step name : ℕ)

def localKey (x : Site U.G.V h) : U.delivery.LocalWires R x → RawId R h
  | .inl (j, q) => .path x.2 false j.val (endName U.post q.val.1.val q.val.2)
  | .inr (.inl v) => .layer x.2 v.1.val v.2
  | .inr (.inr (j, q)) => .path x.2 true j.val (endName U.post q.val.1.val q.val.2)

def step (j : ℕ) (t : Bool) := if t then j + 1 else j

def rawKey (e : U.Raw R) (t : Bool) : RawId R h :=
  match e with
  | .inl (.inl ⟨x, b⟩) => U.localKey R x b
  | .inl (.inr q) => .direct (endName U.post q.val t)
  | .inr (j, q) => .detour j.val
      (endName U.post q.val (Detour.Switch.side (terminalWidth Δ Y) (step j.val t)))

theorem local_place (x : Site U.G.V h) (b : U.delivery.LocalWires R x) (t : Bool) :
    let p := R.supply (U.delivery.inputAt x) (U.delivery.outputAt x) (U.delivery.lane x) b
    U.rawPlace R fit (.inl (.inl ⟨x, b⟩)) t = (x.group a, x.1, .inl ((x.drop a).2, cond t p.2 p.1)) := by
  cases t <;> rfl

theorem direct_place (q : {e // U.Z.good e}) (t : Bool) :
    let x := U.Z.leaf ((demands U.G).point q.val t)
    U.rawPlace R fit (.inl (.inr q)) t = (U.Z.group (U.G.ix q.val), Scheme.side U.G q.val t,
      .inl ((x.drop a).2, R.root true (U.delivery.plug q t).2)) := by
  have he : Site.group a (U.Z.leaf ((demands U.G).point q.val t)) = U.Z.group (U.G.ix q.val) :=
    U.Z.group_end q.val t
  rw [← point_side, ← he]
  cases t <;> rfl

def switch : Detour.Switch (Site U.G.V (h - a) × Fin Y) (terminalWidth Δ Y) :=
  ⟨terminalNear U.G.C Δ Y, terminal_symm U.G.cs _ _, U.pins⟩

abbrev endTerm (e : U.G.E) (t : Bool) := U.Z.terminal U.delivery ((demands U.G).point e t)

theorem reaches (e : U.G.E) : U.endTerm e true ∈ U.switch.near (U.endTerm e false) :=
  Finset.mem_product.mpr ⟨U.Z.leaf_near U.G.cs U.G.sub (fun _ _ he => by simp [he])
    (U.G.edge e) (U.G.ix e), Finset.mem_univ _⟩

def stop (e : U.G.E) (j : ℕ) : U.G.V × Coord R h a Δ :=
  Schedule.splitHost R a h _ (R.hub (U.switch.path (U.reaches e) j))

theorem detour_place (j : Fin (Detour.steps (terminalWidth Δ Y))) (q : U.Z.Exceptional) (t : Bool) :
    U.rawPlace R fit (.inr (j, q)) t = (U.Z.group (U.G.ix q.val), U.stop R q.val (step j.val t)) := by
  cases t <;> rfl

theorem stop_side (e : U.G.E) (j : ℕ) :
    (U.stop R e j).1 = Scheme.side U.G e (Detour.Switch.side (terminalWidth Δ Y) j) := by
  have h (x : Detour.Hub (Site U.G.V (h - a) × Fin Y) (terminalWidth Δ Y)) :
      (Schedule.splitHost R a h _ (R.hub x)).1 = (Detour.owner x).1.1 := by cases x <;> rfl
  unfold stop
  rw [h, U.switch.path_owner]
  cases Detour.Switch.side (terminalWidth Δ Y) j <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Uniqueness of raw supply names at a fixed host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)

theorem end_inj_at {e f : U.G.E} {t : Bool} (hz : Scheme.side U.G e t = Scheme.side U.G f t)
    (hk : endName U.post e t = endName U.post f t) : e = f := by
  obtain ⟨hi, hj⟩ := Prod.mk.inj (Encodable.encode_injective hk)
  exact U.post.stub_unique U.hu _ _ t hz ((cellIndex h).injective hi) (Prod.mk.inj hj).1

variable [NeZero Y] [NeZero w] (fit : U.Fits R c)

private def category : RawId R h → Option (Schedule.Address h) ⊕ Unit
  | .path x .. | .layer x .. => .inl (some x)
  | .direct _ => .inl none
  | .detour .. => .inr ()

private theorem local_category (x : Site U.G.V h) (b : U.delivery.LocalWires R x) :
    category R (U.localKey R x b) = .inl (some x.2) := by
  rcases b with b|b|b <;> rfl

theorem localKey_injective (x : Site U.G.V h) : Function.Injective (U.localKey R x) := by
  have he := endName_inj U.post U.hu U.Z x
  rintro (⟨j, e⟩|⟨j, e⟩|⟨j, e⟩) (⟨k, f⟩|⟨k, f⟩|⟨k, f⟩) hk <;>
    simp [localKey] at hk
  · rw [Fin.ext hk.1, he hk.2]
  · rw [hk.2, Fin.ext hk.1]
  · rw [Fin.ext hk.1, he hk.2]

/-- Together with the endpoint flag the local name distinguishes
all incident wires, including both ends of loops. -/
theorem raw_inj {e f : U.Raw R} {t : Bool}
    (hv : (U.rawPlace R fit e t).2.1 = (U.rawPlace R fit f t).2.1)
    (he : U.rawKey R e t = U.rawKey R f t) : e = f := by
  have hc := congrArg (category R) he
  rcases e with (⟨x, e⟩|e)|⟨i, e⟩ <;> rcases f with (⟨y, f⟩|f)|⟨j, f⟩ <;>
    simp only [rawKey, local_category] at hc <;> try {simp [category] at hc; done}
  · rw [local_place, local_place] at hv
    have hxy : x = y := Prod.ext hv (Option.some.inj (Sum.inl.inj hc))
    subst y
    rw [U.localKey_injective R x he]
  · rw [direct_place, direct_place] at hv
    have : e = f := Subtype.ext (U.end_inj_at hv (RawId.direct.inj he))
    rw [this]
  · obtain ⟨h, h'⟩ := RawId.detour.inj he
    have heq := Fin.ext h
    subst j
    simp only [detour_place, stop_side] at hv
    have : e = f := Subtype.ext (U.end_inj_at hv h')
    rw [this]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Matching an old unit and the terminals at both ends -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  {U V : Setup S h u a Δ D Y w B'} {Q : Relation U V} {σ : Cell a} {k n : ℕ}
  {e : U.G.E} {f : V.G.E}

structure UnitPair (Q : Relation U V) (σ : Cell a) (k : ℕ) (e : U.G.E) (f : V.G.E) : Prop where
  ix : U.G.ix e = V.G.ix f
  stub : ∀ b, U.post.stub e b = V.post.stub f b
  hosts : ∀ b, Q k (Scheme.side U.G e b) (Scheme.side V.G f b)
  group : U.Z.group (U.G.ix e) = σ
  good : U.Z.good e ↔ V.Z.good f

theorem Region.unit_pair (p : Region U V σ Q n) (hk : k + (h - a) + 2 ≤ n)
    (e : U.G.E) (b : Bool) (z : V.G.V) (hg : U.Z.group (U.G.ix e) = σ)
    (hr : Q k (Scheme.side U.G e b) z) :
    ∃ f, Scheme.side V.G f b = z ∧ UnitPair Q σ (k + 1) e f := by
  obtain ⟨f, hs, he, ho⟩ := p.fwd.hits _ _ _ hr (by omega) e b hg rfl
  have ht : Q k (Scheme.side U.G e b) (Scheme.side V.G f b) := hs ▸ hr
  refine ⟨f, hs, he.ix, he.stub, ?_, hg, p.toSurvey.good hk he.ix ht ho hg⟩
  intro t
  by_cases h : t = b
  · subst t; exact p.widen (by omega) ht
  · have h' : t = !b := by cases b <;> cases t <;> first | rfl | contradiction
    rwa [h']

theorem point_eq (U : Setup S h u a Δ D Y w B') (e : U.G.E) (t : Bool) :
    (demands U.G).point e t = (Scheme.side U.G e t, U.G.ix e) :=
  Prod.ext (point_side ..) rfl

namespace UnitPair
variable (r : UnitPair Q σ k e f) (p : Region U V σ Q n) (hk : k + (h - a) + 2 ≤ n)

include p r in
theorem group' : V.Z.group (V.G.ix f) = σ := by rw [← r.ix, ← p.fwd.group, r.group]

include r in
theorem name (b : Bool) : endName U.post e b = endName V.post f b := by
  rw [endName, endName, r.ix, r.stub]

include p hk r in
theorem related (b : Bool) :
    Related U V (Scheme.side U.G e b) (Scheme.side V.G f b) b e f :=
  ⟨r.ix, r.stub, p.labels (by omega) (r.hosts b) (p.widen (by omega) (r.hosts (!b)))⟩

include p hk r in
theorem leaf (b : Bool) :
    (U.Z.leaf ((demands U.G).point e b)).2 = (V.Z.leaf ((demands V.G).point f b)).2 := by
  rw [point_eq, point_eq, ← r.ix]
  exact p.toSurvey.leaf (by omega) (r.hosts b) r.group

variable [NeZero Y] [NeZero w]

include p hk r in
theorem terminal (b : Bool) :
    U.delivery.terminal ((demands U.G).point e b) =
      V.delivery.terminal ((demands V.G).point f b) := by
  rw [point_eq, point_eq, ← r.ix]
  exact (p.toSurvey.agree hk (r.hosts b)).terminal _ r.group

include p hk r in
theorem drop (b : Bool) : (U.endTerm e b).1.2 = (V.endTerm f b).1.2 :=
  congrArg (fun x => (Site.drop a ((), x)).2) (r.leaf p hk b)

end UnitPair

variable [NeZero Y] [NeZero w]

theorem endTerm_host (U : Setup S h u a Δ D Y w B') (e : U.G.E) (b : Bool) :
    (U.endTerm e b).1.1 = Scheme.side U.G e b := point_side e b

private theorem output_plug {x : Site U.G.V h}
    (t : GoodEnd U.Z.leaf (demands U.G).point U.Z.good x) :
    U.delivery.outputAt x t = (U.delivery.plug t.val.1 t.val.2).2 := by
  obtain ⟨⟨j, b⟩, rfl⟩ := t
  rfl

theorem UnitPair.plug (r : UnitPair Q σ k e f) (p : Region U V σ Q n) (hk : k + (h - a) + 2 ≤ n)
    (he : U.Z.good e) (hf : V.Z.good f) (b : Bool) :
    (U.delivery.plug ⟨e, he⟩ b).2 = (V.delivery.plug ⟨f, hf⟩ b).2 := by
  let v := Scheme.side U.G e b
  let z := Scheme.side V.G f b
  let x := (U.Z.leaf ((demands U.G).point e b)).2
  have h₁ : U.Z.leaf ((demands U.G).point e b) = (v, x) := Prod.ext (point_side ..) rfl
  have h₂ : V.Z.leaf ((demands V.G).point f b) = (z, x) :=
    Prod.ext (point_side ..) (r.leaf p hk b).symm
  let i : U.End v x := ⟨(⟨e, he⟩, b), h₁⟩
  let j : V.End z x := ⟨(⟨f, hf⟩, b), h₂⟩
  have hx : Site.group a (v, x) = σ := (U.end_group v x i).symm.trans r.group
  have hh := (p.toSurvey.agree hk (r.hosts b)).output hx (q := i) (q' := j) rfl (r.related p hk b)
  change U.delivery.outputAt _ i = V.delivery.outputAt _ j at hh
  rwa [output_plug, output_plug] at hh

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Correspondence of rotor paths and layers within one leaf -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup S h u a Δ D Y w B'} {σ : Cell a}
  {v : U.G.V} {z : V.G.V} {x : Schedule.Address h}

theorem Agree.input (c : Agree U V σ v z) (hx : Site.group a (v, x) = σ)
    {q : U.End v x} {q' : V.End z x} (hi : U.G.ix q.val.1.val = V.G.ix q'.val.1.val) :
    U.delivery.inputAt (v, x) q = V.delivery.inputAt (z, x) q' := by
  unfold Delivery.inputAt
  rw [point_eq, point_eq, U.end_root, V.end_root, ← hi]
  exact c.terminal _ ((U.end_group v x q).trans hx)

def localSupply (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w) (x : Site U.G.V h) :=
  R.supply (U.delivery.inputAt x) (U.delivery.outputAt x) (U.delivery.lane x)

theorem Agree.local_wire (c : Agree U V σ v z) (hx : Site.group a (v, x) = σ)
    (R : Rotor F Y w) (e : U.delivery.LocalWires R (v, x)) :
    ∃ f : V.delivery.LocalWires R (z, x),
      U.localKey R (v, x) e = V.localKey R (z, x) f ∧
      U.localSupply R (v, x) e = V.localSupply R (z, x) f := by
  have matchEnd (q : U.End v x) : ∃ q' : V.End z x,
      endName U.post q.val.1.val q.val.2 = endName V.post q'.val.1.val q'.val.2 ∧
      (U.delivery.lane (v, x) q).2 = (V.delivery.lane (z, x) q').2 ∧
      U.delivery.inputAt (v, x) q = V.delivery.inputAt (z, x) q' ∧
      U.delivery.outputAt (v, x) q = V.delivery.outputAt (z, x) q' := by
    obtain ⟨q', ht, hr⟩ := c.end_map hx q
    refine ⟨q', ?_, (Prod.mk.inj (c.lane hx ht hr)).2, c.input hx hr.ix, c.output hx ht hr⟩
    rw [← ht, hr.name]
  rcases e with ⟨i, q⟩ | ⟨i, q⟩ | ⟨i, q⟩
  · obtain ⟨p, hn, hl, hi, _⟩ := matchEnd q
    refine ⟨.inl (i, p), ?_, ?_⟩
    · simp only [localKey, hn]
    · simp only [localSupply, Rotor.supply, Sum.elim_inl, Rotor.pathEdge, hi, hl]
  · refine ⟨.inr (.inl ⟨i.cast (c.layers hx), q⟩), rfl, rfl⟩
  · obtain ⟨p, hn, hl, _, ho⟩ := matchEnd q
    refine ⟨.inr (.inr (i, p)), ?_, ?_⟩
    · simp only [localKey, hn]
    · simp only [localSupply, Rotor.supply, Sum.elim_inr, Rotor.pathEdge, ho, hl]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Matching pins and stops on the two arms of a detour -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  {U V : Setup S h u a Δ D Y w B'} {Q : Relation U V} {σ : Cell a} {k n : ℕ}
  {e : U.G.E} {f : V.G.E}

theorem Region.neighbors (p : Region U V σ Q n) (hk : k < n)
    {v : U.G.V} {z : V.G.V} (hr : Q k v z) : U.chart.Maps V.chart v z := by
  intro x hx
  obtain ⟨c, hc, _, hl, _⟩ := p.fwd.siblings _ _ _ hr hk ⟨(v, x), hx⟩ false rfl
  exact ⟨unitEnds c true, hc ▸ Chart.partner_mem V.G.cs c false, hl⟩

abbrev Terminal (U : Setup S h u a Δ D Y w B') := Site U.G.V (h - a) × Fin Y

def tipKey (x : U.Terminal) := (x.1.2, x.2)

theorem Region.pins_eq (p : Region U V σ Q n) (hk : k < n)
    {x y : U.Terminal} {x' y' : V.Terminal} (hxy : y ∈ terminalNear U.G.C Δ Y x)
    (hxy' : y' ∈ terminalNear V.G.C Δ Y x')
    (hx : Q k x.1.1 x'.1.1) (hy : Q n y.1.1 y'.1.1)
    (h₁ : tipKey x = tipKey x') (h₂ : tipKey y = tipKey y') :
    U.pins x ⟨y, hxy⟩ = V.pins x' ⟨y', hxy'⟩ := by
  rcases x with ⟨⟨v, a⟩, j⟩
  rcases x' with ⟨⟨v', b⟩, j'⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁
  exact U.chart.treePin_eq V.chart (p.neighbors hk hx) (p.symm.neighbors hk hx)
    U.hΔ U.deg V.deg _ _ _ _ (Prod.ext (p.labels hk hx hy) h₂)

variable [NeZero Y] [NeZero w] (r : UnitPair Q σ k e f) (p : Region U V σ Q n)
  (hk : k + (h - a) + 2 ≤ n)

include r p hk in
theorem UnitPair.tip (t : Bool) : tipKey (U.endTerm e t) = tipKey (V.endTerm f t) :=
  Prod.ext (r.drop p hk t) (r.terminal p hk t)

def pinAt (U : Setup S h u a Δ D Y w B') (e : U.G.E) (b : Bool) :=
  U.pins (U.endTerm e b) ⟨U.endTerm e (!b), by
    cases b
    · exact U.reaches e
    · exact U.switch.sym _ _ (U.reaches e)⟩

include r p hk in
theorem UnitPair.pin (b : Bool) : U.pinAt e b = V.pinAt f b := by
  unfold pinAt
  apply p.pins_eq (k := k) (by omega)
  · rw [endTerm_host, endTerm_host]; exact r.hosts b
  · rw [endTerm_host, endTerm_host]; exact p.widen (by omega) (r.hosts (!b))
  · exact r.tip p hk b
  · exact r.tip p hk (!b)

variable (R : Rotor F Y w)
local notation "L" => terminalWidth Δ Y
local notation "m" => Nat.clog 2 L

private def arm (x : Schedule.Address (h - a) × Fin Y) (pin : Fin L) (k : ℕ) : Coord R h a Δ :=
  if k ≤ m then .inr (x, Tree.climb pin k) else .inl (x.1, R.root false x.2)

private theorem stop_coord (U : Setup S h u a Δ D Y w B') (e : U.G.E) (j : ℕ) :
    (U.stop R e j).2 =
      if j ≤ m + 1 then arm R (tipKey (U.endTerm e false)) (U.pinAt e false) (m + 1 - j)
      else arm R (tipKey (U.endTerm e true)) (U.pinAt e true) (j - (m + 2)) := by
  have aux (x : U.Terminal) (i : Fin L) (t : ℕ) :
      (Schedule.splitHost R a h L (R.hub (if t ≤ m then .inr (x, Tree.climb i t) else .inl x))).2 =
        arm R (tipKey x) i t := by unfold arm; split <;> rfl
  unfold stop Detour.Switch.path
  split
  · exact aux _ _ _
  · exact aux _ _ _

include r p hk in
theorem UnitPair.stop (j : ℕ) : (U.stop R e j).2 = (V.stop R f j).2 := by
  simp only [stop_coord, r.tip p hk, r.pin p hk]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Comparing bit assignments at a reset station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U V : Setup S h u a Δ D Y w B') (R : Rotor F Y w)
  (fit : U.Fits R c) (fit' : V.Fits R c)

abbrev Value := (U.G.E × Bool) ⊕ U.Raw R → Bool

def oldPlace (e : U.G.E) (t : Bool) :=
  U.place R fit ((U.result R fit).owner ((demands U.G).point e t))

def valueAt (σ : Cell a) (v : U.G.V) (loc : Coord R h a Δ) (x : U.Value R) :=
  (U.result R fit).rule.entry () ((U.place R fit).symm (σ, v, loc))
    (fun i => x (.inl (i, false))) (fun i => x (.inl (i, true))) (x ∘ Sum.inr)

theorem old_place (e : U.G.E) (t : Bool) :
    let x := U.Z.leaf ((demands U.G).point e t)
    U.oldPlace R fit e t = (U.Z.group (U.G.ix e), Scheme.side U.G e t,
      .inl ((x.drop a).2, R.root false (U.delivery.terminal ((demands U.G).point e t)))) := by
  rw [← point_side]
  rfl

variable {U V}
structure Alignment (σ : Cell a) (v : U.G.V) (z : V.G.V) (loc : Coord R h a Δ)
    (x : U.Value R) (y : V.Value R) : Prop where
  old : ∀ i j t, U.oldPlace R fit i t = (σ, v, loc) → V.oldPlace R fit' j t = (σ, z, loc) →
    endName U.post i t = endName V.post j t → x (.inl (i, t)) = y (.inl (j, t))
  wire : ∀ i j t, U.rawPlace R fit i t = (σ, v, loc) → V.rawPlace R fit' j t = (σ, z, loc) →
    U.rawKey R i t = V.rawKey R j t → x (.inr i) = y (.inr j)

variable {R fit fit'} {σ : Cell a} {v : U.G.V} {z : V.G.V} {loc : Coord R h a Δ}
  {x : U.Value R} {y : V.Value R}

theorem Alignment.symm (e : Alignment R fit fit' σ v z loc x y) :
    Alignment R fit' fit σ z v loc y x :=
  ⟨fun i j t h h' he => (e.old j i t h' h he.symm).symm,
    fun i j t h h' he => (e.wire j i t h' h he.symm).symm⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# Separating the programmed rotor from the exceptional contacts

A site receives a product from the rotor stations mapped there.
For each exceptional path, consecutive bits must agree whenever
the path passes through this site.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule
open scoped Classical
open Finset

variable {F S E T : Type} [Field F] [Fintype S] [Fintype E] [Fintype T] {n : ℕ}

def through (x y : E → Bool) (z : Fin n × E → Bool) (i : Fin (n + 1)) (e : E) : Prop :=
  Fin.cons (α := fun _ => E → Bool) x (Function.curry z) i e =
    Fin.snoc (α := fun _ => E → Bool) (Function.curry z) y i e

theorem path_place (D : ℕ → E → S) (g : S → T) (v : T)
    (x y : E → Bool) (z : Fin n × E → Bool) :
    ((Rule.path F D n).place g).entry () v x y z =
      if ∀ (i : Fin (n + 1)) e, g (D i.val e) = v → through x y z i e then 1 else 0 := by
  change (∏ w ∈ univ.filter (fun w => g w = v), (Rule.path F D n).entry () w x y z) = _
  simp only [path_entry, prod_ite_zero, prod_const_one, mem_filter, mem_univ, true_and]
  congr! 1
  constructor
  · exact fun h i e he => h _ he i e rfl
  · rintro h w hw i e rfl; exact h i e hw

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Spectral.Packet Finset
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w) (fit : U.Fits R c)
  (σ : Cell a) (v : U.G.V) (loc : Coord R h a Δ) (x : U.Value R)

local notation "L" => terminalWidth Δ Y

def rotorWeight (t : Site U.G.V h × R.Hardware) :=
  (U.delivery.deployRule R).entry () t (fun e => x (.inl (e.val, false)))
    (fun e => x (.inl (e.val, true))) (fun i => x (.inr (.inl i)))

def joins (i : Fin (Detour.steps L + 1)) (e : U.Z.Exceptional) :=
  Rule.through (fun e => x (.inl (e.val, false))) (fun e => x (.inl (e.val, true)))
    (fun j => x (.inr (.inr j))) i e

def detours : Prop :=
  ∀ (i : Fin (Detour.steps L + 1)) (e : U.Z.Exceptional),
    (U.Z.group (U.G.ix e.val), U.stop R e.val i.val) = (σ, v, loc) → U.joins R x i e

def selected (q : Schedule.Address h) (t : R.Hardware) : Prop :=
  Site.group a ((), q) = σ ∧ Sum.inl ((Site.drop a ((), q)).2, t) = loc

def mainValue :=
  ∏ q : Schedule.Address h, ∏ t : R.Hardware,
    if selected R σ loc q t then U.rotorWeight R x ((v, q), t) else 1

private theorem main_eq :
    (∏ t ∈ univ.filter (fun t => Schedule.mainPlace R t = (U.place R fit).symm (σ, v, loc)),
      U.rotorWeight R x t) = U.mainValue R σ v loc x := by
  have he (z : U.G.V) (q : Schedule.Address h) (t : R.Hardware) :
      Schedule.mainPlace R ((z, q), t) = (U.place R fit).symm (σ, v, loc) ↔
        z = v ∧ selected R σ loc q t := by
    refine (U.place R fit).eq_symm_apply.trans ?_
    change (Site.group a ((), q), z, Sum.inl ((Site.drop a ((), q)).2, t)) = (σ, v, loc) ↔ _
    simp only [Prod.mk.injEq, selected, and_left_comm]
  rw [prod_filter, Fintype.prod_prod_type, Fintype.prod_prod_type]
  simp only [he, ite_and, prod_ite_irrel, prod_const_one, prod_ite_eq', mem_univ, ite_true, mainValue]

private def treeWalk (i : ℕ) (e : U.Z.Exceptional) :=
  (U.Z.group (U.G.ix e.val), U.switch.path (U.reaches e.val) i)

private theorem detour_eq :
    ((Rule.path F U.treeWalk (Detour.steps L)).place (Schedule.treePlace R)).entry ()
      ((U.place R fit).symm (σ, v, loc)) (fun e => x (.inl (e.val, false)))
      (fun e => x (.inl (e.val, true))) (fun j => x (.inr (.inr j))) =
      if U.detours R σ v loc x then 1 else 0 := by
  have he (i : ℕ) (e : U.Z.Exceptional) :
      Schedule.treePlace R (U.treeWalk i e) = (U.place R fit).symm (σ, v, loc) ↔
        (U.Z.group (U.G.ix e.val), U.stop R e.val i) = (σ, v, loc) :=
    (U.place R fit).eq_symm_apply
  refine (Rule.path_place U.treeWalk (Schedule.treePlace R) _ _ _ _).trans ?_
  congr! 1
  simp only [he, detours, joins]

theorem value_eq :
    U.valueAt R fit σ v loc x = U.mainValue R σ v loc x * if U.detours R σ v loc x then 1 else 0 := by
  rw [← U.main_eq R fit, ← U.detour_eq R fit]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

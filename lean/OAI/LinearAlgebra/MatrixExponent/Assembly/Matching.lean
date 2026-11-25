import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
import OAI.LinearAlgebra.MatrixExponent.Packing.Projection
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Packing.Suffix
import OAI.LinearAlgebra.MatrixExponent.Packing.FieldLift

/-!
# Local movement of thin occurrences

The column contraction moves a whole occurrence to its matched
destination if any of its outgoing rows is selected. Select one
such row from the padded array and recover the destination from
the thick mate. The row contraction leaves all occurrences in place.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match

open Coloring Packing

variable {d h e k ℓ : ℕ} (x : (Input d h e k ℓ).obj)

def motion (b : B h) : Bool × B (Labels h ℓ d).width :=
  let y := rows x
  let i := sampleRow y.control.1 b
  (y.control.1 i, y.dest (y.control.2 i))

theorem cheap_motion (F : Type) [Field F] (d h e k ℓ t : ℕ)
    (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t) (hw : k ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F (h + e) t (Input d h e k ℓ)
      (.vec h (.pair .bit (.addr (Labels h ℓ d).width))) motion 160 := by
  have hi := ht
  unfold Rows.overhead at hi
  let A := Format.addr (Labels h ℓ d).width
  have ha : (Format.pair .bit A).width ≤ t := by
    unfold A; rw [Format.width_pair, Format.width_bit, Format.width_addr]; omega
  have ctl := cheap_match F d h e k ℓ t ht hw hd
  have remote := (cheap_rows F d h e k ℓ t ht hw hd).snd.snd.snd.snd
  have get := Cheap.lookup F (h + e) t A (by omega) (by rw [Format.width_pair] at ha; omega)
  have addr := (remote.pair ctl.snd).comp get
  have sample := cheap_sample (h := h) (e := e) F (by omega) (.pair .bit A) ha
  exact ((ctl.fst.pair (ctl.fst.pair addr).zip).comp sample).mono (by decide)

private theorem mask_active {h k : ℕ} (x : Rows h k) {i : B h} (hi : x.control.1 i = true) :
    x.active i = true := by
  have := ((x.gather x.perm).mask_iff (x.perm.symm i)).mp hi
  simpa only [Rows.gather, Rows.active, Function.comp_apply, Equiv.apply_symm_apply] using this.1.1

namespace Stubs
variable {P V E : Type} {r : ℕ} {src dst : E → P} {ix : E → Cell r} {owner : P → V}
  (f : Stubs src dst ix owner d h e ℓ)
  (data : V → (Input d h e k ℓ).obj) (m : Matching src dst ix)
  (enc : f.Records data m.color)
  (ctl : Rows.Controls (fun p => rows (data (owner p))) f.pos m)

include enc ctl

/-- The read address is the neighbor slot and colony key of the
specific thick mate. Inactive rows need no dummy destination. -/
theorem motion_spec (p : P) (b : Cell r) (key : ((data (owner p)).2.1 (f.block b)).1 = f.tag p) :
    let y := motion (data (owner p)) (f.block b)
    y.1 = (m.plan p b).isSome ∧
      (y.1 = true → ∃ i, src i = p ∧ m.plan p b = some (dst i) ∧
        y.2 = (Labels h ℓ d).serial (0, f.tag (dst i), f.near i)) := by
  let X := rows (data (owner p))
  let i := sampleRow X.control.1 (f.block b)
  let y := motion (data (owner p)) (f.block b)
  have hr : (rowIndex h e i).1 = f.block b := sampleRow_block _ _
  have hc : X.src i = f.key p := by simp only [X, Rows.src, rows, hr, key, Stubs.key]
  have ok := f.represents data m.color enc p
  have spec (hi : y.1 = true) :
      ∃ j, src j = p ∧ m.plan p b = some (dst j) ∧
        y.2 = (Labels h ℓ d).serial (0, f.tag (dst j), f.near j) := by
    change X.control.1 i = true at hi
    obtain ⟨j, hj, hp⟩ := ok.onto i (mask_active X hi) hc
    have hb : ix j = b := by
      apply f.block.injective
      simpa [← hp, pos] using hr
    have hh : (m.plan (src j) (ix j)).isSome := by rw [ctl.mask, hj, hp]; exact hi
    let t := m.mate ⟨j, hh⟩
    obtain ⟨_, ht, hd⟩ := m.spec ⟨j, hh⟩
    have hs : src t = p := ht.trans hj
    have ha : f.pos t = X.control.2 i := by simpa only [hj, hp] using ctl.mate ⟨j, hh⟩
    refine ⟨t, hs, by simpa only [hj, hb] using hd, ?_⟩
    change X.dest (X.control.2 i) = _
    rw [← ha]
    simp only [X, Rows.dest, rows, pos, Equiv.apply_symm_apply, ← hs, enc.slot, enc.remote]
  refine ⟨Bool.eq_iff_iff.mpr ⟨?_, ?_⟩, spec⟩
  · intro hi
    obtain ⟨_, _, ht, _⟩ := spec hi
    simp [ht]
  · intro hp
    obtain ⟨j, hj, hb⟩ := m.used p b hp
    have hh : X.control.1 (f.pos j) = true := by
      have := ctl.mask j
      rw [hj, hb] at this
      exact this.symm.trans hp
    change X.control.1 i = true
    simpa [i, pos, hb] using sampleRow_marked _ hh

end Stubs
end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-!
# Short addresses for contracted sites

A moved station specifies a neighbor index and a colony label. From the
source of an original edge, both of its new endpoint addresses are at
most two local hops away. All six gadget parties use these same addresses.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring Packing
variable {d h e k ℓ : ℕ}

abbrev Move (d ℓ : ℕ) := Format.pair .bit (.pair (.addr ℓ) (.addr d))

/-- After the motion query, only the local label and one decision bit
are needed to determine the destination of the occurrence. -/
def step (col : Bool) (own : B ℓ) (q : Bool × B (Labels h ℓ d).width) : (Move d ℓ).obj :=
  if col && q.1 then (true, ((Labels h ℓ d).serial.symm q.2).2) else (false, own, 0)

def action (col : Bool) (x : (Input d h e k ℓ).obj) (b : B h) :=
  step (h := h) col (x.2.1 b).1 (motion x b)

variable {V : Type} (nav : V → B d → V)

def follow (v : V) (a : (Move d ℓ).obj) : V × B ℓ :=
  (if a.1 then nav v a.2.2 else v, a.2.1)

namespace Stubs
variable {P E : Type} {r : ℕ} {src dst : E → P} {ix : E → Cell r} {owner : P → V}
  (f : Stubs src dst ix owner d h e ℓ)
  (data : V → (Input d h e k ℓ).obj) (m : Matching src dst ix)
  (enc : f.Records data m.color)
  (ctl : Rows.Controls (fun p => rows (data (owner p))) f.pos m)
  (contacts : ∀ i, nav (owner (src i)) (f.near i) = owner (dst i))

include enc ctl contacts

theorem action_spec (p : P) (b : Cell r) (col : Bool)
    (own : ((data (owner p)).2.1 (f.block b)).1 = f.tag p) :
    let q := if col then (m.plan p b).getD p else p
    follow nav (owner p) (action col (data (owner p)) (f.block b)) = (owner q, f.tag q) := by
  obtain ⟨hm, he⟩ := f.motion_spec data m enc ctl p b own
  cases col
  · simp [action, step, follow, own]
  cases h : m.plan p b with
  | none => simp [action, step, follow, own, hm, h]
  | some q =>
    have ha : (motion (data (owner p)) (f.block b)).1 = true := by rw [hm, h]; rfl
    obtain ⟨i, hs, ht, hp⟩ := he ha
    have eq : dst i = q := Option.some.inj (ht.symm.trans h)
    have hv : nav (owner p) (f.near i) = owner q := by rw [← hs, contacts, eq]
    simp [action, step, follow, ha, hp, hv, eq]
end Stubs

/-- The first hop is optional. It precedes the movement of the endpoint. -/
abbrev Path (d ℓ : ℕ) := Format.pair (.pair .bit (.addr d)) (Move d ℓ)

def readPath (v : V) (q : (Path d ℓ).obj) :=
  follow nav (if q.1.1 then nav v q.1.2 else v) q.2

def ends (x : (Input d h e k ℓ).obj) (localMove : B h → (Move d ℓ).obj)
    (remote : B d → B h → (Move d ℓ).obj) (i : B (h + e)) : (Path d ℓ).obj × (Path d ℓ).obj :=
  let b := (rowIndex h e i).1
  let j := (rowIndex h e i).2
  let w := ((x.2.1 b).2 j).2.1
  (((false, 0), localMove b), ((true, w), remote w b))

def parties (col : Bool) {A : Type} (a b : A × A) : Fin 6 → A :=
  ![a.1, a.2, b.1, b.2, if col then b.2 else a.1, if col then a.2 else b.2]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-! # Computing the local movement record without long addresses -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring

variable (F : Type) [Field F] {d h e k ℓ t : ℕ}

private theorem unpack (A : Format) (ha : A.width ≤ t) :
    Cheap F 0 t (.addr A.width) A A.serial.symm 2 := by
  have aux (f : slots (word A.width) ≃ A.pins) :
      Cheap F 0 t (.addr A.width) A
        ((A.code.trans (f.symm.arrowCongr (.refl _))).trans (Format.addr _).code.symm).symm 2 := by
    have hw : A.width ≤ 2 ^ 0 * (100 + t) ^ 1 := by simp; omega
    have hd : (Format.addr A.width).width ≤ 2 ^ 0 * (100 + t) ^ 1 := by rwa [Format.width_addr]
    apply Cheap.project F hd hw f.symm
    intro x i
    rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
    rfl
  exact aux _

private abbrev Step (d h ℓ : ℕ) :=
  Format.pair .bit (.pair (.addr ℓ) (.pair .bit (.addr (Labels h ℓ d).width)))

private theorem cheap_step (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t) :
    Cheap F 0 t (Step d h ℓ) (Move d ℓ) (fun x => step x.1 x.2.1 x.2.2) 20 := by
  have hw : (Step d h ℓ).width ≤ 2 ^ 0 * (100 + t) ^ 1 := by
    simp only [Step, Format.width_pair, Format.width_addr, pow_zero, one_mul, pow_one]
    rw [Format.width_bit]
    rw [Rows.overhead, width_labels] at ht
    omega
  have hi := ht
  rw [Rows.overhead, width_labels] at hi
  have key := unpack F (Labels h ℓ d) (t := t) (by rw [width_labels]; omega)
  have gate : Cheap F 0 t (.pair .bit .bit) .bit (fun x => x.1 && x.2) 2 := by
    refine ⟨_, Coloring.small (A := .pair .bit .bit) (by simp) _, ?_⟩
    change 2 + 1 + 200 ≤ _
    ring_nf; omega
  have x := Cheap.id F hw
  have take := (x.fst.pair x.snd.snd.fst).comp gate
  have data := (x.snd.snd.snd.comp key).snd
  have zero := Cheap.const F hw (D := .addr d) (by simp; omega) (0 : B d)
  have own := ((data.fst.pair x.snd.fst).pair take).comp ((cheap_select F ℓ).widen (l := t) (by omega))
  have idx := ((data.snd.pair zero).pair take).comp ((cheap_select F d).widen (l := t) (by omega))
  convert (take.pair (own.pair idx)).mono (d := 20) (by decide) using 1
  funext x
  simp only [step, Function.comp_apply, id_eq]
  cases x.1 && x.2.2.1 <;> simp

theorem cheap_lift {n p t c : ℕ} {A D : Format} {f : A.obj → D.obj}
    (hf : Cheap F n t A D f c) (hn : n ≤ p) : Cheap F p t A D f c := by
  obtain ⟨m, hf, hb⟩ := hf
  exact ⟨m, hf, hb.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hn))⟩

private theorem zip {n c : ℕ} {A D E : Format}
    {f : A.obj → (B h → D.obj) × (B h → E.obj)}
    (hf : Cheap F n t A (.pair (.vec h D) (.vec h E)) f c) :
    Cheap F n t A (.vec h (.pair D E)) (fun x i => ((f x).1 i, (f x).2 i)) (c + 1) := by
  let x := Format.pair (.vec h D) (.vec h E)
  let y := Format.vec h (.pair D E)
  have hz : Circuit F x y (fun p i => (p.1 i, p.2 i)) (x.width + 2 * y.width) :=
    Circuit.project (Equiv.prodSumDistrib _ _ _) (by rintro p ⟨i, j | j⟩ <;> rfl)
  obtain ⟨m, hm, hb⟩ := hf
  refine ⟨_, hm.comp hz, ?_⟩
  have he : x.width = y.width := by simp [x, y, mul_add]
  have hg : 5 * (2 ^ n * (100 + t) ^ c) ≤ 2 ^ n * (100 + t) ^ (c + 1) := by
    rw [mul_comm 5, pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  change A.width + x.width + m ≤ _ at hb
  change A.width + y.width + (m + (x.width + 2 * y.width)) ≤ _
  omega

abbrev Directed (d h e k ℓ : ℕ) := Format.pair .bit (Input d h e k ℓ)

theorem cheap_action (d h e k ℓ t : ℕ)
    (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t) (hw : k ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F (h + e) t (Directed d h e k ℓ) (.vec h (Move d ℓ)) (fun x => action x.1 x.2) 180 := by
  have hi := ht
  rw [Rows.overhead, width_labels] at hi
  let A := Directed d h e k ℓ
  have ha : A.width ≤ 2 ^ (h + e) * (100 + t) ^ 31 := by
    obtain ⟨m, _, hm⟩ := cheap_rows F d h e k ℓ t ht hw hd
    rw [Format.width_pair, Format.width_bit, pow_succ (100 + t) 30, ← mul_assoc]
    have := lt_mul_of_one_lt_right (by positivity : 0 < 2 ^ (h + e) * (100 + t) ^ 30)
      (by omega : 1 < 100 + t)
    omega
  have small (U : Format) (hs : U.width ≤ t) :
      (Format.vec h U).width ≤ 2 ^ (h + e) * (100 + t) ^ 31 := by
    rw [Format.width_vec]
    apply Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega))
    exact (show U.width ≤ (100 + t) ^ 1 by simp; omega).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have col : Cheap F (h + e) t A (.vec h .bit) (fun x _ => x.1) 32 :=
    Cheap.project F ha (small .bit (by simp; omega)) (fun i => .inl i.2) (fun _ _ => rfl)
  have label : Cheap F (h + e) t A (.vec h (.addr ℓ)) (fun x i => (x.2.2.1 i).1) 32 :=
    Cheap.project F ha (small (.addr ℓ) (by simp; omega))
      (fun i => .inr (.inr (.inl (i.1, .inl i.2)))) (fun _ _ => rfl)
  have moved := (Cheap.id F ha).snd.comp (cheap_motion F d h e k ℓ t ht hw hd)
  have send := cheap_lift F (Cheap.map (A := Step d h ℓ) (D := Move d ℓ) (fun _ => _) (fun _ : B h => cheap_step F ht)) (Nat.le_add_right h e)
  have inp := zip F (col.pair (zip F (label.pair moved)))
  exact (inp.comp send).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-! # Recovering the physical replacement endpoints from local records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring Packing
variable {d h e k ℓ : ℕ} {V : Type}
  (nav : V → B d → V) (data : V → (Input d h e k ℓ).obj)

def localEnds (col : Bool) (v : V) :=
  ends (data v) (action col (data v)) (fun j => action col (data (nav v j)))

def localParties (col : Bool) (v : V) (i : B (h + e)) :=
  let f := localEnds nav data col v
  parties col (f ((rows (data v)).control.2 i)) (f i)

variable [Fintype V] {E : Type} {N C : V → Finset V} {Δ D u r : ℕ}
  {L : ℝ} {l : V → Cell r → ℝ} (g : Grouping N C Δ D u L l)
  {src dst : E → V} {ix : E → Cell r}

/-- The encoded site name stores a host position and a local interval key. -/
structure Chart (m : Matching (g.ends src ix) (g.ends dst ix) ix) where
  stubs : Stubs (g.ends src ix) (g.ends dst ix) ix (fun p => p.1) d h e ℓ
  records : stubs.Records data m.color
  controls : Rows.Controls (fun p => rows (data p.1)) stubs.pos m
  contacts : ∀ i, nav (src i) (stubs.near i) = dst i
  labels : ∀ v j, ((data v).2.1 (stubs.block j)).1 = stubs.tag (g.loc v j)
  site : Site V r ↪ V × B ℓ
  key : ∀ p, site (g.site p) = (p.1, stubs.tag p)

namespace Chart

variable {g nav data} {m : Matching (g.ends src ix) (g.ends dst ix) ix}
  (p : Chart nav data g m)

theorem moved (col : Bool) (v : V) (j : Cell r) :
    follow nav v (action col (data v) (p.stubs.block j)) = p.site (g.route m col v j) := by
  have h := p.stubs.action_spec nav data m p.records p.controls p.contacts (g.loc v j) j col
    (p.labels v j)
  cases col <;> exact h.trans (p.key _).symm

theorem endpoints (col : Bool) (i : E) :
    let f := readPath nav (src i)
    Prod.map f f (localEnds nav data col (src i) (p.stubs.pos i)) =
      (p.site (g.route m col (src i) (ix i)), p.site (g.route m col (dst i) (ix i))) := by
  have hs : (((data (src i)).2.1 (p.stubs.block (ix i))).2 (p.stubs.stub i)).2.1 =
      p.stubs.near i := p.records.slot i
  simp only [localEnds, ends, Stubs.pos, Equiv.apply_symm_apply, Prod.map, readPath,
    Bool.false_eq_true, ite_false, ite_true, hs, p.contacts]
  exact Prod.ext (p.moved col _ _) (p.moved col _ _)

theorem gadget (col : Bool) (i : m.items) (j : Fin 6) :
    readPath nav (src i.val) (localParties nav data col (src i.val) (p.stubs.pos i.val) j) =
      p.site (g.party m col i j) := by
  have ptr : (rows (data (src i.val))).control.2 (p.stubs.pos i.val) = p.stubs.pos (m.mate i) :=
    (p.controls.mate i).symm
  have origin : src (m.mate i) = src i.val := congrArg Sigma.fst (m.spec i).2.1
  let a := localEnds nav data col (src i.val) (p.stubs.pos (m.mate i))
  let b := localEnds nav data col (src i.val) (p.stubs.pos i.val)
  let f := readPath (ℓ := ℓ) nav (src i.val)
  have ha : Prod.map f f a =
      (p.site (g.party m col i 0), p.site (g.party m col i 1)) := by
    unfold f a
    rw [← origin]
    exact p.endpoints col _
  have hb : Prod.map f f b =
      (p.site (g.party m col i 2), p.site (g.party m col i 3)) := p.endpoints col _
  unfold localParties
  rw [ptr]
  change f (parties col a b j) = _
  have h₀ := congrArg Prod.fst ha
  have h₁ := congrArg Prod.snd ha
  have h₂ := congrArg Prod.fst hb
  have h₃ := congrArg Prod.snd hb
  fin_cases j
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃
  · cases col
    · exact h₀
    · exact h₃
  · cases col
    · exact h₃
    · exact h₁

end Chart
end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-! # Stub and colony numbering for grouped host positions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing
open scoped Classical

variable {V : Type} {h : ℕ}

def cellIndex (h : ℕ) : Cell h ≃ B h := Fintype.equivOfCardEq (by simp [Cell])

def intervalCode (h : ℕ) : (Σ d : Fin (h + 1), Cell d.val) ↪ B (h + 1) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    have ht := Site.card Unit h
    simpa only [Site, Fintype.card_prod, Fintype.card_unit, one_mul, mul_one, B,
      Fintype.card_fin, pow_succ'] using ht))

def siteCode (V : Type) (h : ℕ) : Site V h ↪ V × B (h + 1) :=
  (Function.Embedding.refl V).prodMap (intervalCode h)

namespace Scheme.Posting

variable {F T : Type} [Field F] {x y : Wire} {L : Fringe x y T} {u : ℕ}
  {S : Scheme F} {r : S.format.obj} {G : HostNet F L h u}
  (p : S.Posting r G) (hu : 0 < u)

/-- Follow a short neighbor index, defaulting to home for an empty seat. -/
def nav (v : G.V) (i : B S.d) : G.V :=
  if h : ∃ w, p.host w = (r (p.host v)).1 i then h.choose else v

include hu in
theorem nav_target (i : G.E) : p.nav (G.src i) (p.index (G.src i) (G.dst i)) = G.dst i := by
  have h : ∃ w, p.host w = (r (p.host (G.src i))).1 (p.index (G.src i) (G.dst i)) :=
    ⟨G.dst i, (p.target hu i).symm⟩
  rw [nav, dite_eq_left h]
  exact p.host.injective (h.choose_spec.trans (p.target hu i))

variable (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  {l : G.V × Cell a → Cell (h - a) → ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' l)

abbrev gSrc := g.ends (G.regroup a ha).src (G.regroup a ha).ix
abbrev gDst := g.ends (G.regroup a ha).dst (G.regroup a ha).ix

def groupNav (v : G.V × Cell a) (i : B S.d) := (p.nav v.1 i, v.2)

def stubs : Match.Stubs (gSrc a ha g) (gDst a ha g) (G.regroup a ha).ix
    (fun v => v.1) S.d (h - a) S.e (h - a + 1) where
  block := (cellIndex _).toEmbedding
  tag q := intervalCode _ (g.site q).2
  separate _ _ hv hi := g.site_injective (Prod.ext hv ((intervalCode _).injective hi))
  stub i := p.stub i false
  unique i j he hb hi := by
    have hs : (G.src i, ancestor ha (G.ix i)) = (G.src j, ancestor ha (G.ix j)) :=
      congrArg Sigma.fst he
    obtain ⟨hv, hx⟩ := Prod.mk.inj hs
    have hl : G.ix i = G.ix j := (splitCell a ha).injective (Prod.ext hx hb)
    apply p.distinct hu
    change ((p.host (G.src i), p.block (G.ix i), 0), p.stub i false) =
      ((p.host (G.src j), p.block (G.ix j), 0), p.stub j false)
    rw [hv, hl, hi]
  near i := p.index (G.src i) (G.dst i)
  neighbor i j he := by
    have hs : (G.src i, ancestor ha (G.ix i)) = (G.src j, ancestor ha (G.ix j)) :=
      congrArg Sigma.fst he
    obtain ⟨hv, hx⟩ := Prod.mk.inj hs
    change _ ↔ (G.dst i, ancestor ha (G.ix i)) = (G.dst j, ancestor ha (G.ix j))
    constructor
    · intro hi
      have ht : G.dst i = G.dst j := by rw [← p.nav_target hu i, hi, hv, p.nav_target hu j]
      exact Prod.ext ht hx
    · intro ht
      rw [hv, (Prod.mk.inj ht).1]

end Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Extracting the outgoing records from local station patterns -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring Packing
open scoped Classical

variable {F : Type} {d k e : ℕ}

def Pattern.outgoing (P : Pattern F d k e) (j : B e) : Bool × B d × B e :=
  let q := P.peer 0 j
  let active := decide (0 < P.width 0 j ∧ P.direction 0 j = false ∧ q.isSome)
  (active, (q.getD (0, 0, 0)).1, (q.getD (0, 0, 0)).2.2)

namespace Scheme.Posting

variable [Field F] {T : Type} {x y : Wire} {L : Fringe x y T} {u h : ℕ}
  {S : Scheme F} {r : S.format.obj} {G : HostNet F L h u}
  (p : S.Posting r G) (hu : 0 < u)

def localStub (v : G.V) (t : Cell h) :=
  (S.decode ((r (p.host v)).2 (p.block t))).outgoing

include hu in
theorem active (v : G.V) (t : Cell h) (i : B S.e) :
    (p.localStub v t i).1 = true ↔ ∃ q, G.src q = v ∧ G.ix q = t ∧ p.stub q false = i := by
  trans S.outgoing r ((p.host v, p.block t, 0), i)
  · simp [localStub, Pattern.outgoing, outgoing, width, direction, peer, pattern]
  rw [p.enumerates hu]
  simp [span, spanAt, side, p.host.injective.eq_iff, p.block.injective.eq_iff, and_assoc]

theorem local_slot (i : G.E) :
    (p.localStub (G.src i) (G.ix i) (p.stub i false)).2 =
      (p.index (G.src i) (G.dst i), p.stub i true) := by
  have ht := p.link i false
  change (S.decode ((r (p.host (G.src i))).2 (p.block (G.ix i)))).peer 0 (p.stub i false) =
    some (p.index (G.src i) (G.dst i), 0, p.stub i true) at ht
  simp [localStub, Pattern.outgoing, ht]

variable (a : ℕ) (ha : a ≤ h) {Δ D j : ℕ} {B' : ℝ}
  {l : G.V × Cell a → Cell (h - a) → ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D j B' l)

def label (v : G.V × Cell a) (i : Cell (h - a)) := intervalCode _ (g.here v i).2

def records (c : Color (h - a)) (v : G.V × Cell a) :
    (Match.Input S.d (h - a) S.e S.e (h - a + 1)).obj :=
  let old i := (cellIndex (h - a)).symm i
  (fun i => decide (thick c (old i)),
   fun i => (label a g v (old i), p.localStub v.1 ((splitCell a ha).symm (v.2, old i))),
   fun i t => label a g (p.groupNav a v t) (old i))

theorem record_label (c : Color (h - a)) (v : G.V × Cell a) (i : Cell (h - a)) :
    ((p.records a ha g c v).2.1 ((p.stubs hu a ha g).block i)).1 =
      (p.stubs hu a ha g).tag (g.loc v i) := by
  change label a g v ((cellIndex _).symm (cellIndex _ i)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem records_correct (c : Color (h - a)) :
    (p.stubs hu a ha g).Records (p.records a ha g c) c := by
  constructor
  · intro v i j
    change (p.localStub v.1 ((splitCell a ha).symm (v.2, (cellIndex _).symm i)) j).1 = true ↔
      ∃ q : G.E, (G.src q, ancestor ha (G.ix q)) = v ∧ cellIndex _ (suffix a (G.ix q)) = i ∧
        p.stub q false = j
    rw [p.active hu]
    apply exists_congr
    intro q
    rw [Equiv.eq_symm_apply, Prod.ext_iff]
    change (G.src q = v.1 ∧ (ancestor ha (G.ix q) = v.2 ∧
      suffix a (G.ix q) = (cellIndex _).symm i) ∧ _) ↔ _
    rw [Equiv.eq_symm_apply, Prod.ext_iff]
    tauto
  · intro i
    change G.E at i
    change decide (thick c ((cellIndex _).symm (cellIndex _ (suffix a (G.ix i))))) = true ↔ _
    rw [decide_eq_true_eq, Equiv.symm_apply_apply]
    rfl
  · intro i
    change G.E at i
    exact p.record_label hu a ha g c _ _
  · intro i
    change G.E at i
    let q := G.ix i
    change (p.localStub (G.src i) ((splitCell a ha).symm
      (ancestor ha q, (cellIndex _).symm (cellIndex _ (suffix a q)))) (p.stub i false)).2.1 = _
    rw [Equiv.symm_apply_apply, show (ancestor ha q, suffix a q) = splitCell a ha q from rfl,
      Equiv.symm_apply_apply]
    exact congrArg Prod.fst (p.local_slot i)
  · intro i
    change G.E at i
    change label a g (p.nav (G.src i) (p.index (G.src i) (G.dst i)), ancestor ha (G.ix i))
      ((cellIndex _).symm (cellIndex _ (suffix a (G.ix i)))) = _
    rw [Equiv.symm_apply_apply, p.nav_target hu]
    rfl

end Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Counting selector seats by the local mask bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match.Chart
open Coloring Packing
open scoped Classical

variable {d h e k ℓ : ℕ} {V E : Type} [Fintype V]
  {nav : V → B d → V} {data : V → (Input d h e k ℓ).obj}
  {N C : V → Finset V} {Δ D u r : ℕ}
  {L : ℝ} {l : V → Cell r → ℝ} {g : Grouping N C Δ D u L l}
  {src dst : E → V} {ix : E → Cell r}
  {m : Matching (g.ends src ix) (g.ends dst ix) ix}
  (p : Chart nav data g m)

def row : E ↪ V × B (h + e) where
  toFun i := (src i, p.stubs.pos i)
  inj' := by
    intro i j he
    obtain ⟨ha, hb⟩ := Prod.mk.inj he
    have he := (rowIndex h e).symm.injective hb
    have hi := p.stubs.block.injective (Prod.mk.inj he).1
    exact p.stubs.unique i j (by unfold Grouping.ends; rw [ha, hi]) hi (Prod.mk.inj he).2

def marked : m.items ↪ V × B (h + e) :=
  (Function.Embedding.subtype _).trans p.row

theorem active (j : V × B (h + e)) :
    (rows (data j.1)).active j.2 = true ↔ j ∈ Set.range p.row := by
  constructor
  · intro hj
    obtain ⟨i, hs, hb, he⟩ := (p.records.active _ _ _).mp hj
    exact ⟨i, Prod.ext hs ((rowIndex h e).symm_apply_eq.mpr (Prod.ext hb he))⟩
  · rintro ⟨i, rfl⟩
    exact (p.stubs.represents data _ p.records _).active i rfl

theorem marks (j : V × B (h + e)) :
    (rows (data j.1)).control.1 j.2 = true ↔ j ∈ Set.range p.marked := by
  constructor
  · intro hj
    let x := rows (data j.1)
    have hh := ((x.gather x.perm).mask_iff (x.perm.symm j.2)).mp hj
    have he : x.active j.2 = true := by
      simpa only [Rows.gather, Rows.active, Function.comp_apply, Equiv.apply_symm_apply] using hh.1.1
    obtain ⟨i, rfl⟩ := (p.active j).mp he
    exact ⟨⟨i, (p.controls.mask i).trans hj⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact (p.controls.mask i.val).symm.trans i.property

include p in
theorem mark_count [Fintype E] :
    (∑ v, (Finset.univ.filter fun i => (rows (data v)).control.1 i).card) = m.count := by
  let s := Finset.univ.filter fun j : V × B (h + e) => (rows (data j.1)).control.1 j.2
  have hs : s = Finset.univ.map p.marked := by
    ext j
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, p.marks, Finset.mem_map, Set.mem_range]
  have he : s.card = m.count := by rw [hs, Finset.card_map, Finset.card_univ, m.card_items]
  rw [← he]
  simp only [s, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Match.Chart
end

/-!
# Candidate wires for an entire subround

A fixed bank of slots accompanies each possible old row. The forward
and reciprocal mask bits distinguish the two members of a matched
pair from an untouched unit. Test for loops after reading the addresses.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring Packing Spectral.Tensor
open scoped Classical

abbrev Kind (b : ℕ) := (Fin 8 × Fin (4 * b)) ⊕ Fin b
abbrev Candidate (V : Type) (n b : ℕ) := (V × B n) × Kind b

variable {V : Type} {d h e k ℓ b : ℕ}
  (nav : V → B d → V) (data : V → (Input d h e k ℓ).obj)

def untouched (j : V × B (h + e)) :=
  let x := rows (data j.1)
  x.active j.2 && !(x.control.1 j.2) && !(x.control.1 (x.control.2 j.2))

def enabled (shape : V × B (h + e) → Fin 8 → ℕ) (q : Candidate V (h + e) b) : Bool :=
  match q.2 with
  | .inl (j, t) => (rows (data q.1.1)).control.1 q.1.2 && decide (t.val < shape q.1 j)
  | .inr _ => untouched data q.1

def paths (col : Bool) (q : Candidate V (h + e) b) : (Path d ℓ).obj × (Path d ℓ).obj :=
  let (v, i) := q.1
  match q.2 with
  | .inl (j, _) => Prod.map (localParties nav data col v i) (localParties nav data col v i) (sixPair j)
  | .inr _ => localEnds nav data col v i

namespace Chart
variable {nav data} {E F : Type} [Field F] [Fintype V] {N C : V → Finset V} {Δ D u r : ℕ}
  {L : ℝ} {l : V → Cell r → ℝ} {g : Grouping N C Δ D u L l}
  {src dst : E → V} {ix : E → Cell r}
  {m : Matching (g.ends src ix) (g.ends dst ix) ix}
  (p : Chart nav data g m)

private theorem paired (i : E) : i ∈ Set.range m.pairEdge ↔
    (m.plan (g.ends src ix i) (ix i)).isSome ∨ ∃ t, m.mate t = i := by
  constructor
  · rintro ⟨⟨t, j⟩, rfl⟩
    fin_cases j
    · exact .inr ⟨t, rfl⟩
    · exact .inl t.property
  · rintro (hi | ⟨t, rfl⟩)
    · exact ⟨(⟨i, hi⟩, 1), rfl⟩
    · exact ⟨(t, 0), rfl⟩

theorem untouched_iff (j : V × B (h + e)) :
    untouched data j = true ↔ ∃ i : m.unpaired, p.row i.val = j := by
  have onRow (i : E) : untouched data (p.row i) = true ↔ i ∉ Set.range m.pairEdge := by
    have ha := (p.active (p.row i)).mpr ⟨i, rfl⟩
    have hm := p.controls.mask i
    have ht := p.controls.used_iff (p.stubs.represents data _ p.records) i
    change (m.plan _ _).isSome = (rows (data (p.row i).1)).control.1 (p.row i).2 at hm
    change (rows (data (p.row i).1)).control.1
      ((rows (data (p.row i).1)).control.2 (p.row i).2) = true ↔ _ at ht
    simp only [untouched, Bool.and_eq_true, Bool.not_eq_true', ha, true_and, ← hm,
      paired, not_or, ← ht, Bool.not_eq_true]
  constructor
  · intro hj
    have ha := hj
    simp only [untouched, Bool.and_eq_true] at ha
    obtain ⟨i, rfl⟩ := (p.active j).mp ha.1.1
    exact ⟨⟨i, (onRow i).mp hj⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact (onRow _).mpr i.property

variable (P : Gadget F) (i : g.Choice m P)

private theorem profile_le (t : m.items) (j : Fin 8) : g.profile m i t j ≤ 4 * P.b :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans (P.cost _ (i t).2.property).le

def event : g.Supply m P i ↪ Candidate V (h + e) P.b where
  toFun
    | .inl ⟨t, j, k⟩ => (p.marked t, .inl (j, Fin.castLE (profile_le P i t j) k))
    | .inr (t, k) => (p.row t.val, .inr k)
  inj' := by
    rintro (⟨t, j, k⟩ | ⟨t, k⟩) (⟨a, z, w⟩ | ⟨a, w⟩) he
    · obtain ⟨hr, hj⟩ := Prod.mk.inj he
      cases p.marked.injective hr
      obtain ⟨rfl, hk⟩ := Prod.mk.inj (Sum.inl.inj hj)
      have hk' : k = w := Fin.castLE_injective _ hk
      rw [hk']
    · cases (Prod.mk.inj he).2
    · cases (Prod.mk.inj he).2
    · obtain ⟨hr, hw⟩ := Prod.mk.inj he
      exact congrArg Sum.inr (Prod.ext (Subtype.ext (p.row.injective hr)) (Sum.inr.inj hw))

variable (shape : V × B (h + e) → Fin 8 → ℕ)
  (code : ∀ t, shape (p.marked t) = g.profile m i t)

include code in
theorem enabled_iff (q : Candidate V (h + e) P.b) :
    enabled data shape q = true ↔ q ∈ Set.range (p.event P i) := by
  constructor
  · rcases q with ⟨x, ⟨j, k⟩ | k⟩
    · simp only [enabled, Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨hx, hk⟩
      obtain ⟨t, rfl⟩ := (p.marks x).mp hx
      rw [code] at hk
      exact ⟨.inl ⟨t, j, ⟨k.val, hk⟩⟩, rfl⟩
    · intro h
      obtain ⟨t, rfl⟩ := (p.untouched_iff x).mp h
      exact ⟨.inr (t, k), rfl⟩
  · rintro ⟨⟨t, j, k⟩ | ⟨t, k⟩, rfl⟩
    · change ((rows (data (p.marked t).1)).control.1 (p.marked t).2 &&
        decide (k.val < shape (p.marked t) j)) = true
      simp only [Bool.and_eq_true, decide_eq_true_eq, code]
      exact ⟨(p.marks _).mpr ⟨t, rfl⟩, k.isLt⟩
    · exact (p.untouched_iff _).mpr ⟨t, rfl⟩

theorem read_event (col : Bool) (s : g.Supply m P i) :
    let q := p.event P i s
    let f := readPath nav q.1.1
    Prod.map f f (paths nav data col q) = Prod.map p.site p.site (g.contact m col s) := by
  rcases s with ⟨t, j, k⟩ | ⟨t, k⟩
  · exact Prod.ext (p.gadget col t (sixPair j).1) (p.gadget col t (sixPair j).2)
  · exact p.endpoints col t.val

variable [Fintype E]

def survivor : g.Survivors m P i ↪ Candidate V (h + e) P.b :=
  (Function.Embedding.subtype _).trans (p.event P i)

include code in
theorem survives_iff (collision : V → (Path d ℓ).obj → (Path d ℓ).obj → Bool)
    (test : ∀ v a b, collision v a b = true ↔ readPath nav v a = readPath nav v b)
    (q : Candidate V (h + e) P.b) :
    let z := paths nav data (g.layout m P i) q
    (enabled data shape q && !(collision q.1.1 z.1 z.2)) = true ↔
      q ∈ Set.range (p.survivor P i) := by
  have cross (s : g.Supply m P i) :
      let q := p.event P i s
      let z := paths nav data (g.layout m P i) q
      collision q.1.1 z.1 z.2 = false ↔
        (g.contact m (g.layout m P i) s).1 ≠ (g.contact m (g.layout m P i) s).2 := by
    have he := p.read_event P i (g.layout m P i) s
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    simp only [Prod.map_fst, Prod.map_snd] at h₁ h₂
    simp only [← Bool.not_eq_true, test, h₁, h₂, p.site.injective.eq_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', p.enabled_iff P i shape code]
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    exact ⟨⟨s, (cross s).mp hs⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s.val, rfl⟩, (cross s.val).mpr s.property⟩

theorem pick_layout {n a : ℕ} (index : B n ≃ V × B (h + e))
    (profile : B a → Fin 8 → ℕ) (x : (Side.Input n a).obj)
    (active : ∀ j, (x j).1 = (rows (data (index j).1)).control.1 (index j).2)
    (value : ∀ t, profile (x (index.symm (p.marked t))).2 = g.profile m i t) :
    Side.pick profile x = g.layout m P i := by
  apply Side.pick_eq_side profile (g.profile m i) x (p.marked.trans index.symm.toEmbedding) _ value
  intro j
  rw [active, p.marks]
  exact exists_congr fun t => index.symm_apply_eq.symm

/-- This version allows the host index set itself to be padded. -/
theorem extract_layout {n a : ℕ} (host : V ↪ B n) (profile : B a → Fin 8 → ℕ)
    (x : B n → (Side.Tagged d h e k ℓ a).obj)
    (read : ∀ v, (x (host v)).1 = data v)
    (pad : ∀ v, v ∉ Set.range host → ∀ j, (rows (x v).1).control.1 j = false)
    (value : ∀ t, profile ((x (host (p.marked t).1)).2 (p.marked t).2) = g.profile m i t) :
    Side.pick profile (Side.extract x) = g.layout m P i := by
  let places := rowIndex n (h + e)
  let addr := (host.prodMap (.refl (B (h + e)))).trans places.symm.toEmbedding
  have hread (j : V × B (h + e)) : Side.extract x (addr j) =
      Side.clean ((rows (data j.1)).control.1 j.2, (x (host j.1)).2 j.2) := by
    change Side.collect (x (places (places.symm (host j.1, j.2))).1)
      (places (places.symm (host j.1, j.2))).2 = _
    simp only [Equiv.apply_symm_apply, Side.collect, read]
  apply Side.pick_eq_side profile (g.profile m i) _ (p.marked.trans addr)
  · intro j
    constructor
    · intro hj
      have hv : (places j).1 ∈ Set.range host := by
        by_contra hn
        exact Bool.noConfusion ((pad _ hn (places j).2).symm.trans hj)
      obtain ⟨v, hv⟩ := hv
      have he : addr (v, (places j).2) = j := places.symm_apply_eq.mpr (Prod.ext hv rfl)
      rw [← he, hread] at hj
      obtain ⟨t, ht⟩ := (p.marks _).mp hj
      exact ⟨t, (congrArg addr ht).trans he⟩
    · rintro ⟨t, rfl⟩
      rw [Function.Embedding.trans_apply, hread]
      exact (p.marks _).mpr ⟨t, rfl⟩
  · intro t
    rw [Function.Embedding.trans_apply, hread]
    simp only [Side.clean, (p.marks _).mpr ⟨t, rfl⟩, ite_true, value]

end Chart
end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-! # A subround matching determined by fixed-width arrays -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
open Finset Coloring Packing
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u h : ℕ}
  {S : Scheme F} {r : S.format.obj} {G : HostNet F L h u}
  (p : S.Posting r G) (hu : 0 < u) (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load)

abbrev rowData (c : Color (h - a)) (q : g.Colony) := Match.rows (p.records a ha g c q.1)

abbrev Matchings := Matching (gSrc a ha g) (gDst a ha g) (G.regroup a ha).ix

def Controls (m : Matchings a ha g) :=
  Rows.Controls (p.rowData a ha g m.color) (p.stubs hu a ha g).pos m

def chart (m : Matchings a ha g) (ctl : p.Controls hu a ha g m) :
    Match.Chart (p.groupNav a) (p.records a ha g m.color) g m where
  stubs := p.stubs hu a ha g
  records := p.records_correct hu a ha g m.color
  controls := ctl
  contacts e := Prod.ext (p.nav_target hu e) rfl
  labels := p.record_label hu a ha g m.color
  site := siteCode _ _
  key _ := rfl

theorem all_colors (c : Color (h - a)) :
    ∃ m : Matchings a ha g, m.color = c ∧ p.Controls hu a ha g m := by
  let r := p.rowData a ha g c
  let b := p.stubs hu a ha g
  obtain ⟨m, hc, hh, _⟩ := Rows.controlled_matching r b.pos
    (b.represents _ _ (p.records_correct hu a ha g c)) (Fintype.card G.E) (coreBins Δ)
    (fun _ _ => card_le_univ _) (g.destinations _ _ _ (G.regroup a ha).edge)
  exact ⟨m, hc, by unfold Controls; rw [hc]; exact hh⟩

theorem matching (σ : ℝ) (hB : 0 < B') (bounds : G.Bounded Δ D B')
    (hbins : 256 * (coreBins Δ + 1) ≤ 2 ^ k)
    (slack : (2 : ℝ) ^ k * B' * (Fintype.card G.V * 2 ^ a : ℕ) ≤ σ) :
    ∃ m : Matchings a ha g, p.Controls hu a ha g m ∧
      (G.X : ℝ) / 4 - (L.Z + σ) ≤ u * (m.count : ℝ) := by
  let H := G.regroup a ha
  let b := p.stubs hu a ha g
  have hb := G.regroup_bounded a ha bounds
  obtain ⟨m, hc, hm⟩ := Rows.controlled_subround (gSrc a ha g) (gDst a ha g) H.ix
    (p.rowData a ha g) (fun _ => b.pos) (fun _ => b.key)
    (fun c => b.represents _ _ (p.records_correct hu a ha g c)) u B' (coreBins Δ)
    (Nat.cast_pos.mpr hu) hB.le
    (fun q t => (g.outgoing H.src H.ix u (Nat.cast_nonneg _) H.outgoing q t).trans (hb.2.2 _ _))
    (g.destinations _ _ _ H.edge)
  have hs : (2 : ℝ) ^ k * B' * Fintype.card (G.V × Cell a) ≤ σ := by
    rwa [Fintype.card_prod, card_cell]
  have hl : (∑ v, ∑ i, H.load v i) ≤ 2 * ((G.X : ℝ) + L.Z) := by
    rw [mul_add]; exact H.sum_load
  have hk : (256 : ℝ) * (coreBins Δ + 1) ≤ 2 ^ k := by exact_mod_cast hbins
  have hσ : 0 ≤ σ := (show 0 ≤ (2 : ℝ) ^ k * B' * Fintype.card (G.V × Cell a) by positivity).trans hs
  have h := bin_charge hB (by positivity) (Nat.cast_nonneg _) L.total_nonneg hσ hk hs hl g.card_bound
  have he : (u : ℝ) * Fintype.card H.E = G.X := by
    change (u : ℝ) * Fintype.card G.E = ↑(Fintype.card G.E * u)
    rw [Nat.cast_mul, mul_comm]
  refine ⟨m, hc, ?_⟩
  rw [he] at hm
  linarith only [h, hm]

def score (c : Color (h - a)) :=
  ∑ v : G.V × Cell a, (univ.filter fun i => (Match.rows (p.records a ha g c v)).control.1 i).card

theorem match_score (m : Matchings a ha g) (ctl : p.Controls hu a ha g m) :
    p.score a ha g m.color = m.count :=
  (p.chart hu a ha g m ctl).mark_count

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
end

import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Boundary
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Scenario
import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.Initial
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact

/-!
# A fixed partition for an entire wave

Enlarge each radius by one to include both ends of every incident
seam. The coloring still separates the enlarged neighborhoods.
Vertices outside them have singleton parts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
open Finset
open scoped Classical
variable {F N A : Type} [Field F] {a : Design} {x y : Wire}
  (w : Scenario F N A a x y) (j : Fin a.waves)

def leader (v u : w.V) : Prop :=
  w.π.mark u = (finProdFinEquiv.symm j).1 ∧ w.atlas.near (a.U + 1) u v

def loc (v : w.V) := if h : ∃ u, w.leader j v u then h.choose else v

theorem loc_of_leader {v u : w.V} (h : w.leader j v u) : w.loc j v = u := by
  have he : ∃ u, w.leader j v u := ⟨u, h⟩
  rw [loc, dite_eq_left he]
  exact w.π.injective_at (by omega) he.choose_spec.2.symm h.2.symm (he.choose_spec.1.trans h.1.symm)

theorem loc_near (v : w.V) : w.atlas.near (a.U + 1) (w.loc j v) v := by
  unfold loc
  split
  · rename_i h
    exact h.choose_spec.2
  · exact .refl _ _ _

structure Balanced (s : w.At j.val) (q : w.At (j.val + 1)) : Prop where
  energy : ∀ i, (∑ v ∈ univ.filter (fun v => w.loc j v = i), q.stage.energyCre a.chart a.H a.g v) ≤
    ∑ v ∈ univ.filter (fun v => w.loc j v = i), s.stage.energyCre a.chart a.H a.g v
  time : ∀ i, (∑ v ∈ univ.filter (fun v => w.loc j v = i), q.stage.timeCre a.chart a.H a.U v) ≤
    ∑ v ∈ univ.filter (fun v => w.loc j v = i), s.stage.timeCre a.chart a.H a.U v
  outside : ∀ v, (¬ ∃ u, w.leader j v u) →
    q.stage.energyCre a.chart a.H a.g v = s.stage.energyCre a.chart a.H a.g v ∧
    q.stage.timeCre a.chart a.H a.U v = s.stage.timeCre a.chart a.H a.U v

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
end

/-! # Checking a wave certificate in bounded neighborhoods -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere
open Surface.Local Finset Coloring
open scoped Classical

namespace Geometry.Credits

variable {I : Type} [Fintype I] {g ℓ D : ℕ} {a : Design}

/-- At a root, check the whole neighborhood. A nonroot belongs
to another region unless its neighborhood contains no root. -/
def part (color : I → Fin a.R) (center : I) (j : Fin a.waves) : Finset I :=
  univ.filter fun i => color center = (finProdFinEquiv.symm j).1 ∨
    (i = center ∧ ∀ t, color t ≠ (finProdFinEquiv.symm j).1)

/-- The check uses only colors, the central caps and the
certificates at the occupied addresses in the neighborhood. -/
def localCheck (color : I → Fin a.R) (center : I)
    (z : I → Credits g ℓ D a.waves) (E M : ℕ) : Prop :=
  ((z center).power 0 ≤ E ∧ (z center).time 0 ≤ M) ∧
  ∀ j : Fin a.waves,
    (∑ i ∈ part color center j, (z i).power j.succ) ≤ ∑ i ∈ part color center j, ((z i).power j.castSucc + 1) ∧
    (∑ i ∈ part color center j, (z i).time j.succ) ≤ ∑ i ∈ part color center j, (z i).time j.castSucc

end Geometry.Credits

namespace Surface.Local.Scenario
open Geometry

variable {F N A : Type} [Field F] {a : Design} {x y : Wire}
  (w : Scenario F N A a x y) (v : w.V) {g ℓ D : ℕ}

abbrev Ball := ↥(w.atlas.ball (a.U + 1) v)

def central : w.Ball v := ⟨v, mem_filter_univ _ |>.mpr (.refl _ _ _)⟩

theorem card_ball : Fintype.card (w.Ball v) ≤ 2 ^ ((a.d + 1) * (a.U + 1)) := by
  have h (t : w.Ball v) := (w.atlas.around_iff _ _ _).mpr (mem_filter.mp t.property).2
  choose f hf using h
  have hi : Function.Injective f := by
    intro i j he
    exact Subtype.ext (w.atlas.coord.injective ((hf i).symm.trans (he ▸ hf j)))
  simpa [B] using Fintype.card_le_of_injective f hi

def checkAt (z : w.Ball v → Credits g ℓ D a.waves) (E M : ℕ) :=
  Credits.localCheck (a := a) (fun t => w.π.mark t.val) (w.central v) z E M

private theorem part_eq (j : Fin a.waves) :
    (Credits.part (a := a) (fun t : w.Ball v => w.π.mark t.val) (w.central v) j).image Subtype.val =
      region (w.loc j) v := by
  let color := (finProdFinEquiv.symm j).1
  have none : (∀ t : w.Ball v, w.π.mark t.val ≠ color) ↔ ¬ ∃ u, w.leader j v u := by
    constructor
    · rintro h ⟨u, hu, he⟩
      exact h ⟨u, mem_filter.mpr ⟨mem_univ _, he.symm⟩⟩ hu
    · exact fun h t ht => h ⟨t.val, ht, (mem_filter.mp t.property).2.symm⟩
  ext u
  simp only [mem_image, Credits.part, region, mem_filter_univ]
  constructor
  · rintro ⟨t, h|⟨rfl, h⟩, rfl⟩
    · exact w.loc_of_leader j ⟨h, (mem_filter.mp t.property).2⟩
    · exact dite_eq_right (none.mp h)
  · intro he
    have hnear := w.loc_near j u
    rw [he] at hnear
    let t : w.Ball v := ⟨u, mem_filter.mpr ⟨mem_univ _, hnear⟩⟩
    refine ⟨t, ?_, rfl⟩
    by_cases h : ∃ z, w.leader j u z
    · obtain ⟨z, hz⟩ := h
      have hz' : z = v := (w.loc_of_leader j hz).symm.trans he
      left
      exact hz' ▸ hz.1
    · have hu : u = v := by simpa [loc, h] using he
      right
      exact ⟨Subtype.ext hu, none.mpr (hu ▸ h)⟩

theorem check_iff (z : w.V → Credits g ℓ D a.waves) (E M : w.V → ℕ) :
    Credits.Check w.loc z E M ↔ ∀ v, w.checkAt v (fun t => z t.val) (E v) (M v) := by
  have he (v : w.V) (j : Fin a.waves) (f : w.V → ℕ) :
      (∑ t ∈ region (w.loc j) v, f t) =
        ∑ t ∈ Credits.part (a := a) (fun t : w.Ball v => w.π.mark t.val) (w.central v) j, f t.val := by
    rw [← part_eq, sum_image Subtype.val_injective.injOn]
  constructor
  · intro h v
    refine ⟨h.initial v, fun j => ?_⟩
    have hp := h.power j v
    have ht := h.time j v
    simp only [he, add_zero] at hp ht
    exact ⟨hp, ht⟩
  · intro h
    refine ⟨fun v => (h v).1, fun j v => ?_, fun j v => ?_⟩
    · simp only [he]; exact ((h v).2 j).1
    · simp only [he, add_zero]; exact ((h v).2 j).2

end Surface.Local.Scenario
end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-! Recover the energy and time credits directly from a printed row. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Finset
open scoped Classical

variable {F K N J L V E T X : Type} {r t q : ℕ}

private def Body.tally (b : Body F r t q K N) (P : ℕ) (f : Role → ℕ → ℕ) :=
  (b.rows.map fun u => f u.role (P * u.a + u.b)).sum

def Body.energyCre (b : Body F r t q K N) (P H g : ℕ) :=
  (1 + 2 * g) * b.tally P (Role.mobile (2 * P * H)) + b.tally P Role.collected

def Body.timeCre (b : Body F r t q K N) (P H U : ℕ) :=
  U * b.tally P Stage.collectorUnit + b.tally P (fun c _ => c.clock) +
    (b.ports.map fun e => P * e.2.2 / (2 * P * H)).sum

namespace Matches
variable {R : Reference J L N V E T X} {β : V ⊕ ℕ → K}
  {s : Stage F r t T V E X} {G : Record F r t V E K N} (h : Matches R.world β s G)
include h

private theorem tally (tag : E → Fin q × Fin q) (P : ℕ) (f : Role → ℕ → ℕ) (v : V) :
    (G.body tag v).tally P f = s.tally P f v := by
  symm
  apply congrArg List.sum
  exact image_match (h.rows v) fun _ _ ha => by simp only [energyOf, ha.left, ha.right, ha.role]

variable [Fintype V]

theorem energyCre (tag : E → Fin q × Fin q) (P H g : ℕ) (v : V) :
    (G.body tag v).energyCre P H g = s.energyCre P H g v := by
  rw [Body.energyCre, h.tally, h.tally]
  rfl

theorem timeCre {src dst : E → V} {g : ℕ} (hl : s.Layout src dst g)
    (tag : E → Fin q × Fin q) (P H U : ℕ) (v : V) :
    (G.body tag v).timeCre P H U = s.timeCre P H U v := by
  rw [Body.timeCre, Stage.timeCre, h.tally, h.tally]
  have hp : (s.scene.cell v).ports = G.ports v := by
    exact (h.ports v).trans (List.map_id _)
  have he : s.scene.level = G.level := funext h.level
  have hn := hl.unique v
  unfold Stage.ports at hn
  rw [Stage.edges, List.sum_toFinset _ hn, hp]
  simp only [Record.body, Stage.ledger, List.map_map, Function.comp_def, he]

end Matches

variable {R Q U M : ℕ}

def Metadata.energyCre (b : Metadata F r t R Q U M N) (P H g : ℕ) :=
  b.elim 0 (fun z => z.2.2.2.toBody.energyCre P H g)

def Metadata.timeCre (b : Metadata F r t R Q U M N) (P H U' : ℕ) :=
  b.elim 0 (fun z => z.2.2.2.toBody.timeCre P H U')

namespace Scenario
variable {A : Type} [Field F] {a : Design} {x y : Wire}
  (w : Scenario F N A a x y) {i j : ℕ}

theorem stored_energyCre (s : w.At i) (v : w.V) :
    Metadata.energyCre (w.stored s (w.atlas.coord v)).2 a.chart a.H a.g =
      s.stage.energyCre a.chart a.H a.g v := by
  rw [stored, Palette.records_at]
  exact s.match'.energyCre w.π.edge _ _ _ v

theorem stored_timeCre (s : w.At i) (v : w.V) :
    Metadata.timeCre (w.stored s (w.atlas.coord v)).2 a.chart a.H a.U =
      s.stage.timeCre a.chart a.H a.U v := by
  rw [stored, Palette.records_at]
  exact s.match'.timeCre s.layout w.π.edge _ _ _ v

variable {w} {menu : a.Menu F N A j} (c : w.Code i menu) (v : w.V)

theorem Code.energyCre :
    Metadata.energyCre (menu ((c.tape (w.atlas.coord v).1).2 (w.atlas.coord v).2)).2
      a.chart a.H a.g = c.frame.stage.energyCre a.chart a.H a.g v := by
  rw [c.read, w.stored_energyCre]

theorem Code.timeCre :
    Metadata.timeCre (menu ((c.tape (w.atlas.coord v).1).2 (w.atlas.coord v).2)).2
      a.chart a.H a.U = c.frame.stage.timeCre a.chart a.H a.U v := by
  rw [c.read, w.stored_timeCre]

end Scenario
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# Addressing the local metadata

One can use the entire bounded-radius input view as the next
dictionary address. This pays a constant factor per wave, avoiding
any need to encode station functions themselves.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Assembly Coloring
open scoped Classical

namespace Design
variable (a : Design) {F N A : Type} {e k : ℕ}

abbrev selectors (k : ℕ) := Format.vec a.m (.vec a.h (.addr k))
abbrev observed (e k : ℕ) := Fmt.wave a.d a.U (a.U + 1) (.addr e) (.addr k)
abbrev nextWidth (e k : ℕ) := (a.observed e k).width

theorem nextWidth_eq (e k : ℕ) :
    a.nextWidth e k = 2 ^ ((a.d + 1) * (a.U + 1)) * (2 ^ ((a.d + 1) * a.U) * (e + k)) := by
  simp only [nextWidth, observed, Fmt.wave, Fmt.view, Format.width_vec, Format.width_pair, Format.width_addr]

def number (S : Format) : S.obj ≃ B S.width :=
  S.code.trans (Fintype.equivOfCardEq (by simp [Format.width]))

variable [Field F] [Fintype F] [ExpChar F a.p]
variable (hF : a.M * (2 * a.D + 1) < Fintype.card F) (j : Fin a.waves) (menu : a.Menu F N A e)

def nextMenu (k : ℕ) : a.Menu F N A (a.nextWidth e k) := fun v =>
  let w := (number (a.observed e k)).symm v
  ((menu (w 0 0).1).1, route a.p a.l hF j a.g a.H (fun i u => (menu (w i u).1).2)
    (fun i => (w i 0).2.val))

def tariff (k : ℕ) (w : (a.observed e k).obj) :=
  charge a.p a.l hF j a.g a.H (fun i => (menu (w 0 i).1).2) (w 0 0).2.val

def around (v : (a.port e).obj) (z : (a.selectors k).obj) :=
  Fmt.around a.U (a.U + 1) (show (Fmt.waveIn a.m a.d a.h (.addr e) (.addr k)).obj from (v, z))

def update (v : (a.port e).obj) (z : (a.selectors k).obj) :=
  Fmt.update (D := .addr (a.nextWidth e k)) (number (a.observed e k)) (a.around v z)

end Design
namespace Scenario
variable {F N A : Type} [Field F] {a : Design} {e k i : ℕ} {x y : Wire}
    {menu : a.Menu F N A e} (w : Scenario F N A a x y)

theorem Code.around (s : w.Code i menu) (tape : (a.selectors k).obj) (v : B a.m × B a.h)
    (j : B ((a.d + 1) * (a.U + 1))) (l : B ((a.d + 1) * a.U)) :
    let u := w.atlas.around a.U (w.atlas.around (a.U + 1) v j) l
    ((a.around s.tape tape) v.1).2 v.2 j l = ((s.tape u.1).2 u.2, tape u.1 u.2) := by
  unfold Design.around Fmt.around Fmt.expand Fmt.zip Atlas.around
  simp only [s.host]

end Scenario
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # The deterministic address update implements the semantic expansion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
open Assembly Coloring Transcript
open scoped Classical

variable {F A N : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p]
  {e k : ℕ} {x y : Wire} {menu : a.Menu F N A e}
  (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (j : Fin a.waves) (s : w.Code j.val menu)

abbrev actions := Frame.commands w.c a.p a.l hF j s.frame

abbrev Branch := Wave.Index (actions w hF j s)

def scalar (i : Branch w hF j s) := ∏ v, (actions w hF j s v).action.weight (i v)

variable (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

def selector : Selector (Branch w hF j s) (a.selectors k).obj :=
  (Frame.code w.c a.p a.l hF j s.frame hk).relabel (Equiv.curry _ _ _)

local notation "C" => selector w hF j s hk
local notation "Rec" => w.π.records w.c w.pos s.frame.record (Frame.info w.size s.frame)

theorem weighted (tape : (a.selectors k).obj) :
    Fmt.weight (a.tariff hF j menu k) (a.around s.tape tape) =
      ((C).read tape).elim 0 (scalar w hF j s) := by
  have h := Frame.charge_prod w.c a.p a.l hF j s.frame w.size hk (Function.uncurry tape)
  change _ = ((C).read tape).elim 0 (scalar w hF j s) at h
  rw [← h, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun u _ => ?_
  have ha := s.around w tape (v, u)
  unfold Design.tariff
  simp only [ha, Atlas.around_zero, s.read, stored]
  rfl

private theorem read_next (i : Branch w hF j s) (v : B a.m × B a.h) :
    a.nextMenu hF j menu k (((a.update s.tape ((C).write i)) v.1).2 v.2) =
      (w.header v, w.π.records w.c w.pos (Wave.update (actions w hF j s) s.frame.record i)
        (Wave.carryInfo (actions w hF j s) i (Frame.info w.size s.frame)) v) := by
  have hr := Frame.routed a.p a.l hF j w.c s.frame w.size hk i v
  have ha := s.around w ((C).write i) v
  simp only [Design.nextMenu, Design.update, Fmt.update, Equiv.symm_apply_apply, ha,
    Atlas.around_zero, s.read, stored]
  exact congrArg (w.header v, ·) hr

/-- The update and its weights use only the common menu and the
physical tapes, independently of the world realizing the tapes. -/
theorem step :
    ∃ q : Branch w hF j s → w.Code (j.val + 1) (a.nextMenu hF j menu k),
      (∀ i, (q i).tape = a.update s.tape ((C).write i)) ∧
      ∀ u v, w.eval s.frame u v = ∑ i, scalar w hF j s i * w.eval (q i).frame u v := by
  obtain ⟨keys, ext, hkeys⟩ := w.controls
  obtain ⟨q, hq, hinfo, he⟩ := Frame.advance w.c a.p a.l hF j s.frame hkeys w.room
  let out (i : Branch w hF j s) : w.Code (j.val + 1) (a.nextMenu hF j menu k) :=
    { frame := q i
      tape := a.update s.tape ((C).write i)
      host := s.host
      read := by
        intro v
        rw [stored, hq, hinfo]
        exact read_next w hF j s hk i v }
  refine ⟨out, fun _ => rfl, fun u v => ?_⟩
  have h : s.frame.stage.value a.chart = ∑ i, scalar w hF j s i • (q i).stage.value a.chart := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact he x
  unfold eval
  simp only [h, map_sum, map_smul, smul_eq_mul]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
end

/-! # The physical control kernel for one wave -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Assembly Coloring
open scoped Classical
universe w
variable {F N A : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p]
  {I : Type w} {e k u v n v' n' : ℕ} {x y : Wire} {L : Set (Table F)}

namespace Design
variable (a : Design) [ExpChar F a.p] (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (j : Fin a.waves) (menu : a.Menu F N A e) (k : ℕ)

/-- One dictionary call for the product of local scalar weights and
the new metadata addresses. -/
def table := weightTable (D := .addr (a.nextWidth e k))
  (number (a.observed e k)) (a.tariff hF j menu k)

def cost (e k v n v' n' : ℕ) (Z : Format) :=
  waveCost a.m a.d a.h a.U (a.U + 1) v n v' n' (.addr e) (.addr k) (.addr (a.nextWidth e k)) +
    4 * (a.selectors k).width + 4 * Z.width

end Design

variable (family : I → Scenario F N A a x y) (Z : Format) (payload : I → Val x → Val y → Z.obj)
  (hF : a.M * (2 * a.D + 1) < Fintype.card F) (j : Fin a.waves) (menu : a.Menu F N A e)

theorem one_wave (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)
    (unique : ∀ s i j, (family s).atlas.graph i j ≠ i →
      ∃! l, (family s).atlas.graph ((family s).atlas.graph i j) l = i)
    (hu : 3 ≤ u) (hU : 0 < a.U)
    (h₁ : Access F u L (a.m + (a.d + 1) * a.U) v n)
    (h₂ : Access F u L (a.m + (a.d + 1) * (a.U + 1)) v' n')
    (hv : 2 ^ a.h * (e + k) ≤ v) (hv' : 2 ^ a.h * (2 ^ ((a.d + 1) * a.U) * (e + k)) ≤ v')
    (hw : 2 * a.nextWidth e k ≤ u) (ht : a.table hF j menu k ∈ L) :
    Transforms F u L (snapshot family Z payload j.val menu)
      (snapshot family Z payload (j.val + 1) (a.nextMenu hF j menu k)) (a.cost e k v n v' n' Z) := by
  let X := snapshot family Z payload j.val menu
  let data (z : X.state × (a.selectors k).obj) :
      (Fmt.waveIn a.m a.d a.h (.addr e) (.addr k)).obj := (z.1.2.tape, z.2)
  have hs := computes_wave (D := .addr (a.nextWidth e k)) hu hU (Nat.succ_pos _) h₁ h₂
    (by simpa using hv) (by simpa [Fmt.view] using hv') (Design.number (a.observed e k))
    (a.tariff hF j menu k) (by simpa only [Format.width_addr, two_mul] using hw) ht data (by
      intro z
      change ∀ i j, _ → _
      simp only [data, z.1.2.host]
      exact unique z.1.1)
  obtain ⟨fn, hfn, he⟩ := hs
  let _ := Fintype.ofFinite (a.selectors k).obj
  have kernels := (Kernel.sum_hidden hu hfn).par (Map.circuit hu (Circuit.id F Z))
  refine ⟨_, kernels, ?_⟩
  rintro ⟨i, s⟩
  let w := family i
  let sel := w.selector hF j s hk
  obtain ⟨q, hq, hv⟩ := w.step hF j s hk
  refine ⟨w.Branch hF j s, inferInstance, fun z => ⟨i, q z⟩, w.scalar hF j s, hv, ?_⟩
  rintro a' b' ⟨v, z⟩
  have term (c : (a.selectors k).obj) : fn (s.tape, c) v =
      (sel.read c).elim 0 (fun k => if (q k).tape = v then w.scalar hF j s k else 0) := by
    have eq := he (⟨i, s⟩, c) v
    change fn (s.tape, c) v = @ite F (a.update s.tape c = v) (Classical.propDecidable _)
      (Fmt.weight (a.tariff hF j menu k) (a.around s.tape c)) 0 at eq
    rw [w.weighted hF j s hk] at eq
    change fn (s.tape, c) v = @ite F (a.update s.tape c = v) (Classical.propDecidable _)
      ((sel.read c).elim 0 _) 0 at eq
    cases h : sel.read c with
    | none => simpa only [h, Option.elim_none, ite_self] using eq
    | some k =>
      have hk := (sel.valid _ _).mp h
      simp only [h, Option.elim_some] at eq
      simp only [Option.elim_some]
      have et : (q k).tape = a.update s.tape c := by rw [hk]; exact hq k
      rw [et]
      by_cases he : a.update s.tape c = v <;> simpa [he] using eq
  change (∑ c, fn (s.tape, c) v) * (if payload i a' b' = z then 1 else 0) =
    ∑ k, @ite F (((q k).tape, payload i a' b') = (v, z))
      (Classical.propDecidable _) (w.scalar hF j s k) 0
  simp only [term, Transcript.Selector.sum, Finset.sum_mul, Prod.mk.injEq]
  by_cases h : payload i a' b' = z <;> simp [h]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# Composition across all waves

The number of calls, the address-width inflation, and the dictionary
are independent of the number of hosts and blocks in the family.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Assembly Coloring
open scoped Classical

namespace Design
variable (a : Design) {F N A : Type} {e k : ℕ}

def widthAt (e k : ℕ) : ℕ → ℕ
  | 0 => e
  | i + 1 => a.nextWidth (widthAt e k i) k

def factor := 2 ^ ((a.d + 1) * (a.U + 1)) * 2 ^ ((a.d + 1) * a.U) + 1

theorem width_bound (e k i : ℕ) : a.widthAt e k i + k ≤ a.factor ^ i * (e + k) := by
  induction i with
  | zero => simp [widthAt]
  | succ i ih =>
    rw [widthAt, nextWidth_eq, pow_succ', mul_assoc]
    refine le_trans ?_ (Nat.mul_le_mul_left a.factor ih)
    conv_rhs => rw [factor, add_mul, one_mul, mul_assoc]
    omega

def maxWidth (e k : ℕ) := a.factor ^ a.waves * (e + k)

theorem fits_width {i : ℕ} (h : i ≤ a.waves) : a.widthAt e k i + k ≤ a.maxWidth e k :=
  (a.width_bound _ _ _).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by unfold factor; omega) h))

def totalCost (e k v n v' n' : ℕ) (Z : Format) :=
  4 * ((a.port e).pair Z).width + ∑ i ∈ Finset.range a.waves, a.cost (a.widthAt e k i) k v n v' n' Z

variable [Field F] [Fintype F] [ExpChar F a.p] (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (menu : a.Menu F N A e) (k : ℕ)

def menuAt : (i : ℕ) → i ≤ a.waves → a.Menu F N A (a.widthAt e k i)
  | 0, _ => menu
  | i + 1, h => a.nextMenu hF ⟨i, h⟩ (menuAt i (Nat.le_of_succ_le h)) k

def calls := Finset.univ.image (fun j : Fin a.waves => a.table hF j (a.menuAt hF menu k j.val j.isLt.le) k)

theorem card_calls : (a.calls hF menu k).card ≤ a.waves := by
  exact Finset.card_image_le.trans_eq (Fintype.card_fin _)

end Design

universe w
variable {F N A : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p]
  {I : Type w} {e k u v n v' n' : ℕ} {x y : Wire} {L : Set (Table F)}
  (family : I → Scenario F N A a x y) (Z : Format) (payload : I → Val x → Val y → Z.obj)
  (hF : a.M * (2 * a.D + 1) < Fintype.card F) (menu : a.Menu F N A e)

theorem all_waves (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)
    (unique : ∀ s i j, (family s).atlas.graph i j ≠ i →
      ∃! l, (family s).atlas.graph ((family s).atlas.graph i j) l = i)
    (hu : 3 ≤ u) (hU : 0 < a.U)
    (h₁ : Access F u L (a.m + (a.d + 1) * a.U) v n)
    (h₂ : Access F u L (a.m + (a.d + 1) * (a.U + 1)) v' n')
    (hv : 2 ^ a.h * a.maxWidth e k ≤ v)
    (hv' : 2 ^ a.h * (2 ^ ((a.d + 1) * a.U) * a.maxWidth e k) ≤ v')
    (hw : 2 * a.maxWidth e k ≤ u) (ht : ↑(a.calls hF menu k) ⊆ L) :
    Transforms F u L (snapshot family Z payload 0 menu)
      (snapshot family Z payload a.waves (a.menuAt hF menu k a.waves le_rfl))
      (a.totalCost e k v n v' n' Z) := by
  suffices ∀ i (hi : i ≤ a.waves),
      Transforms F u L (snapshot family Z payload 0 menu)
        (snapshot family Z payload i (a.menuAt hF menu k i hi))
        (4 * ((a.port e).pair Z).width + ∑ j ∈ Finset.range i, a.cost (a.widthAt e k j) k v n v' n' Z)
      from this _ le_rfl
  intro i
  induction i with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    exact Transforms.refl hu _
  | succ i ih =>
    intro hi
    have he := a.fits_width (e := e) (k := k) (Nat.le_of_succ_le hi)
    have hn : a.nextWidth (a.widthAt e k i) k ≤ a.maxWidth e k :=
      (Nat.le_add_right (a.widthAt e k (i + 1)) k).trans (a.fits_width hi)
    have call := ht (Finset.mem_image_of_mem _ (Finset.mem_univ (⟨i, hi⟩ : Fin a.waves)))
    rw [Finset.sum_range_succ, ← add_assoc]
    exact (ih (Nat.le_of_succ_le hi)).comp (one_wave family Z payload hF ⟨i, hi⟩ _ hk unique hu hU h₁ h₂
      ((Nat.mul_le_mul_left _ he).trans hv)
      ((Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ he)).trans hv')
      ((Nat.mul_le_mul_left _ hn).trans hw) call)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# The two costs of reading a bounded neighborhood

Only work done once per host pays for global addresses. Work repeated
in each of its blocks depends on the short labels and on the price
per bit, independently of the threshold of the permutation theorem.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Assembly Coloring Rounds.Contraction
open BatchDescent.Phase.Poly (pow_sum)

structure Rates where
  m : ℕ
  h : ℕ
  X : ℕ
  Y : ℕ
  short : 10000 ≤ Y
  long : 1000 + 10 * m + 10 * Y ≤ X

namespace Rates
variable (a : Rates)
theorem incl : a.Y ≤ a.X := by have := a.long; omega
theorem two : 2 ≤ a.Y := by have := a.short; omega
theorem two' : 2 ≤ a.X := a.two.trans a.incl

def bound (b z i : ℕ) := b * a.X ^ i + (b * 2 ^ a.h + z) * a.Y ^ i
abbrev Paid (b z i n : ℕ) := n ≤ a.bound b z i
abbrev Row := a.Paid 1 0
abbrev Host := a.Paid (2 ^ a.m) 0

variable {a} {b z i j n l : ℕ}

theorem Paid.up (h : a.Paid b z i n) (e : i ≤ j) : a.Paid b z j n := by
  refine h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right ?_ e))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right ?_ e)))
  · exact lt_of_lt_of_le (by decide) a.two'
  · exact lt_of_lt_of_le (by decide) a.two

theorem Paid.plus (h : a.Paid b z i n) (e : a.Paid b z j l) :
    a.Paid b z (max i j + 1) (n + l) := by
  refine (Nat.add_le_add h e).trans ?_
  unfold bound
  rw [add_add_add_comm, ←mul_add, ←mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (pow_sum a.two' ..)) (Nat.mul_le_mul_left _ (pow_sum a.two ..))

theorem Paid.times (h : a.Paid b z i n) (e : l ≤ a.Y) : a.Paid b z (i + 1) (l * n) := by
  refine (Nat.mul_le_mul e h).trans ?_
  unfold bound
  rw [mul_comm a.Y, add_mul, mul_assoc, mul_assoc, pow_succ, pow_succ]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a.incl)) _

theorem Paid.scale (h : a.Paid b z i n) (l : ℕ) (e : l ≤ 10000 := by decide) :
    a.Paid b z (i + 1) (l * n) := h.times (e.trans a.short)

theorem high (h : n ≤ a.X ^ i) : a.Row i n := by
  simpa only [Row, Paid, bound, one_mul, add_zero] using h.trans (Nat.le_add_right _ (2 ^ a.h * a.Y ^ i))

theorem low (h : n ≤ a.Y ^ i) : a.Row i (2 ^ a.h * n) := by
  simpa only [Row, Paid, bound, one_mul, add_zero] using
    (Nat.mul_le_mul_left (2 ^ a.h) h).trans (Nat.le_add_left _ (a.X ^ i))

theorem big (h : n ≤ a.X) : a.Row 1 n := high (by simpa using h)

theorem Row.hosts (h : a.Row i n) : a.Host i (2 ^ a.m * n) := by
  simpa only [Host, Paid, bound, one_mul, add_zero, mul_add, mul_assoc] using Nat.mul_le_mul_left (2 ^ a.m) h

theorem Row.fan (h : a.Row i n) (e : 2 ^ l ≤ a.Y) : a.Host (i + 1) (2 ^ (a.m + l) * n) := by
  simpa only [pow_add, mul_assoc] using Row.hosts (Paid.times h e)

theorem Host.carry (h : a.Host i n) : a.Paid (2 ^ a.m) z i (n + z) := by
  refine (Nat.add_le_add h (Nat.le_mul_of_pos_right z (pow_pos (lt_of_lt_of_le (by decide) a.two) i))).trans_eq ?_
  unfold bound
  rw [add_zero, add_mul, add_assoc]

variable (a) {F : Type} [Field F] (p : Prices F)

theorem fee (s v : ℕ) (hs : 2 ^ s ≤ a.Y) (hW : 1 + p.W ≤ a.Y) (hw : 1 + p.w ^ p.power ≤ a.X)
    (hv : a.Row i v) : a.Host (max i 1 + 4) (p.fee (a.m + s) v) := by
  have h := (((Row.fan (Paid.plus hv (big hw)) hs).times hW).scale 1000)
  unfold Prices.fee
  rw [mul_assoc, mul_assoc, add_assoc v]
  exact h

theorem gather (s v n : ℕ) (hs : 2 ^ s ≤ a.Y) (hv : a.Row 4 v) (hn : a.Host 8 n) :
    a.Host 205 (gatherCost a.m s v n) := by
  have lt := (Nat.lt_two_pow_self (n := s)).le.trans hs
  have hl := a.long
  have h₁ := Row.fan (high (Nat.pow_le_pow_left (show 100 + (a.m + s + 3 * a.m + 1) ≤ a.X by omega) 200)) hs
  have h₂ := Row.fan (Paid.plus (big (show a.m + s + 1 ≤ a.X by omega)) hv) hs
  have e := ((hn.scale 4).plus (h₁.scale 4)).plus (h₂.scale 1100)
  unfold gatherCost
  rw [mul_assoc 1100, add_right_comm (a.m + s) v 1]
  exact e.up (by decide)

theorem rows (d : ℕ) (A : Format) (hd : 2 ^ d ≤ a.Y) (hA : A.width ≤ a.Y ^ 4) :
    a.Host 5 (Fmt.rows a.m d a.h A).width := by
  rw [Fmt.width_rows]
  have hm := big (show a.m ≤ a.X by have := a.long; omega)
  exact Row.hosts ((Paid.times hm hd).plus (low hA))

theorem expand (d r v n : ℕ) (A : Format) (hd : 2 ^ d ≤ a.Y) (hs : 2 ^ ((d + 1) * r) ≤ a.Y)
    (hv : a.Row 4 v) (hn : a.Host 8 n) (hA : A.width ≤ a.Y ^ 4)
    (hB : (Fmt.view d r A).width ≤ a.Y ^ 4) :
    a.Host 206 (expandCost a.m d a.h r v n A) := by
  have ht : 100 + (a.m + 2 ^ ((d + 1) * r)) ≤ a.X := by have := a.long; omega
  have hb := Row.hosts (high (Nat.pow_le_pow_left ht 200))
  have hh := (a.rows d A hd hA).plus (a.rows d _ hd hB)
  exact ((hh.plus hb).scale 200).plus (a.gather _ _ _ hs hv hn)

theorem update (d : ℕ) (A D : Format) (hd : 2 ^ d ≤ a.Y)
    (hw : 1 + A.width + D.width ≤ a.Y ^ 4) : a.Host 5 (updateCost a.m d a.h A D) := by
  have hm := big (show a.m ≤ a.X by have := a.long; omega)
  exact Row.hosts (((Paid.times hm hd).scale 4).plus (low hw))

theorem wave (d r t v n v' n' : ℕ) (A C D : Format)
    (hd : 2 ^ d ≤ a.Y) (hr : 2 ^ ((d + 1) * r) ≤ a.Y) (ht : 2 ^ ((d + 1) * t) ≤ a.Y)
    (hv : a.Row 4 v) (hn : a.Host 8 n) (hv' : a.Row 4 v') (hn' : a.Host 8 n')
    (hw : 1 + (Fmt.wave d r t A C).width + D.width ≤ a.Y ^ 4) :
    a.Host 209 (waveCost a.m d a.h r t v n v' n' A C D) := by
  have h₂ : (Fmt.wave d r t A C).width ≤ a.Y ^ 4 := by omega
  have mono (s : ℕ) (B : Format) : B.width ≤ (Fmt.view d s B).width := by
    rw [Fmt.view, Format.width_vec]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have h₁ := (mono t (Fmt.view d r (A.pair C))).trans h₂
  have h₀ := (mono r (A.pair C)).trans h₁
  have hc := ((a.rows d _ hd h₀).scale 12).plus (a.expand d r _ _ _ hd hr hv hn h₀ h₁)
  exact (hc.plus (a.expand d t _ _ _ hd ht hv' hn' h₁ h₂)).plus (a.update d _ _ hd hw)

end Rates
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # A uniform price for a complete movement schedule -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Assembly Coloring Rounds.Contraction
open scoped Classical
namespace Design
variable (a : Design) {F : Type} [Field F] (p : Prices F) (e k : ℕ)

abbrev hops := (a.d + 1) * (a.U + 1)
def payloadCap := 2 ^ a.h * (2 ^ a.hops * a.maxWidth e k)
def fees (r : ℕ) := p.fee (a.m + r) (a.payloadCap e k)
def price := a.totalCost e k (a.payloadCap e k) (a.fees p e k ((a.d + 1) * a.U))
  (a.payloadCap e k) (a.fees p e k a.hops)

theorem le_hops : (a.d + 1) * a.U ≤ a.hops := Nat.mul_le_mul_left _ (Nat.le_succ _)
theorem degree_le_hops : a.d ≤ a.hops :=
  (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

/-- A common pair of budgets may be used for all three parts of
concentration. The exterior register is only carried here. -/
theorem price_bound (Z : Format) (X Y : ℕ) (hs : 10000 ≤ Y) (hl : 1000 + 10 * a.m + 10 * Y ≤ X)
    (hW : 1 + p.W ≤ Y) (hw : 1 + p.w ^ p.power ≤ X) (ht : 2 ^ a.hops ≤ Y)
    (hb : 1 + 2 * a.maxWidth e k ≤ Y) (hN : a.waves ≤ Y) :
    a.price p e k Z ≤ 2 ^ a.m * X ^ 215 + (2 ^ (a.m + a.h) + Z.width) * Y ^ 215 := by
  let c : Rates := ⟨a.m, a.h, X, Y, hs, hl⟩
  let v := a.payloadCap e k
  let j := (a.d + 1) * a.U
  let n := a.fees p e k j
  let n' := a.fees p e k a.hops
  have hd := (Nat.pow_le_pow_right (by decide : 0 < 2) a.degree_le_hops).trans ht
  have hj := (Nat.pow_le_pow_right (by decide : 0 < 2) a.le_hops).trans ht
  have w₀ : e + k ≤ a.maxWidth e k := a.fits_width (Nat.zero_le _)
  have w₁ : Y ≤ Y ^ 4 := Nat.le_self_pow (by decide) _
  have hv : c.Row 4 v := by
    apply Rates.low
    change 2 ^ a.hops * a.maxWidth e k ≤ Y ^ 4
    refine (Nat.mul_le_mul ht (by omega : a.maxWidth e k ≤ Y)).trans ?_
    rw [← pow_two]
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have hn : c.Host 8 n := c.fee p _ _ hj hW hw hv
  have hn' : c.Host 8 n' := c.fee p _ _ ht hW hw hv
  have hz : c.Host 4 (a.selectors k).width := by
    rw [selectors, Format.width_vec, Format.width_vec, Format.width_addr]
    exact Rates.Row.hosts (Rates.low (by change k ≤ Y ^ 4; omega))
  have start : c.Paid (2 ^ a.m) Z.width 6 (4 * ((a.port e).pair Z).width) := by
    rw [Format.width_pair]
    have he := c.rows a.d (.addr e) hd (by rw [Format.width_addr]; change e ≤ Y ^ 4; omega)
    exact (Rates.Host.carry he).scale 4
  have one (i : ℕ) (hi : i ∈ Finset.range a.waves) :
      c.Paid (2 ^ a.m) Z.width 212 (a.cost (a.widthAt e k i) k v n v n' Z) := by
    let q := a.widthAt e k i
    let l := a.nextWidth q k
    have hq : l + k ≤ a.maxWidth e k := a.fits_width (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    have hr : 1 + (a.observed q k).width + (Format.addr l).width ≤ c.Y ^ 4 := by
      rw [Format.width_addr]
      change 1 + l + l ≤ Y ^ 4
      omega
    have he := c.wave a.d a.U (a.U + 1) v n v n' (.addr q) (.addr k) (.addr l)
      hd hj ht hv hn hv hn' hr
    have h' := Rates.Host.carry (z := Z.width) (he.plus (hz.scale 4))
    refine le_trans ?_ ((h'.scale 4).up (by decide))
    unfold cost
    change _ + 4 * Z.width ≤ 4 * (_ + Z.width)
    rw [mul_add]
    exact Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (by decide)) _
  have sum := Finset.sum_le_sum one
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at sum
  have hh : c.Paid (2 ^ a.m) Z.width 213
      (∑ i ∈ Finset.range a.waves, a.cost (a.widthAt e k i) k v n v n' Z) :=
    sum.trans (Rates.Paid.times (show c.Paid _ _ _ _ from le_rfl) hN)
  rw [pow_add]
  exact (start.plus hh).up (by decide)

end Design

universe w
variable {F N A : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p]
  {I : Type w} {e k u : ℕ} {x y : Wire} {L : Set (Table F)}
  (family : I → Scenario F N A a x y) (Z : Format) (payload : I → Val x → Val y → Z.obj)
  (hF : a.M * (2 * a.D + 1) < Fintype.card F) (menu : a.Menu F N A e) (p : Prices F)

theorem priced_waves (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)
    (unique : ∀ s i j, (family s).atlas.graph i j ≠ i →
      ∃! l, (family s).atlas.graph ((family s).atlas.graph i j) l = i)
    (hu : 3 ≤ u) (hU : 0 < a.U) (hw : a.m + a.hops ≤ p.w)
    (hb : 2 * a.maxWidth e k ≤ u) (ht : ↑(a.calls hF menu k) ⊆ L) :
    Transforms F u L (snapshot family Z payload 0 menu)
      (snapshot family Z payload a.waves (a.menuAt hF menu k a.waves le_rfl))
      (a.price p e k Z) := by
  have h₀ : 0 < a.m + (a.d + 1) * a.U := by positivity
  have h₁ := Nat.add_le_add_left a.le_hops a.m
  refine all_waves family Z payload hF menu hk unique hu hU
    (p.access hu h₀ (h₁.trans hw) _) (p.access hu (h₀.trans_le h₁) hw _) ?_ ?_ hb ht
  · exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by positivity))
  · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) a.le_hops))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Regional balances for the actual encoded wave successor -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
open Assembly Coloring Transcript
open scoped Classical

variable {F A N : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p]
  {e k : ℕ} {x y : Wire} {menu : a.Menu F N A e}
  (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (j : Fin a.waves) (s : w.Code j.val menu)
  (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

local notation "C" => actions w hF j s
local notation "S" => selector w hF j s hk

private theorem affected (i : Fin ((w.π.plan w.pos).count j)) (v : w.V)
    (h : (C i).affected w.atlas.src w.atlas.dst v) :
    w.leader j v ((w.π.plan w.pos).root j i) := by
  let u := (w.π.plan w.pos).root j i
  have hc : w.π.mark u = (finProdFinEquiv.symm j).1 := (w.π.mem_roots _ u).mp ⟨i, rfl⟩
  refine ⟨hc, ?_⟩
  rcases h with h | ⟨e, ⟨z, rfl⟩, he⟩
  · exact ((w.π.vertex_range le_rfl).mp h).mono (by omega)
  · have hh := (w.π.seam_spec a.U u z).1.near
    rcases he with rfl | rfl
    · exact hh.1
    · exact hh.2

private theorem body_next (i : Branch w hF j s) (q : w.Code (j.val + 1) (a.nextMenu hF j menu k))
    (he : q.tape = a.update s.tape ((S).write i)) (v : w.V) :
    q.frame.record.body w.π.edge v = (Wave.update C s.frame.record i).body w.π.edge v := by
  let p := w.atlas.coord v
  have hr := Frame.routed a.p a.l hF j w.c s.frame w.size hk i p
  have ha := s.around w ((S).write i) p
  have hn := q.read p
  rw [he] at hn
  unfold Design.nextMenu Design.update Fmt.update at hn
  simp only [Equiv.symm_apply_apply, ha, Atlas.around_zero, s.read, stored] at hn
  have hb := (congrArg Prod.snd hn).symm.trans hr
  rw [Palette.records_at, Palette.records_at] at hb
  exact congrArg (fun u => u.2.2.2.toBody) (Option.some.inj hb)

/-- Any honest successor on this tape has the same local credits
as the semantic execution of the commands. -/
theorem balanced_of_tape (hP : 0 < a.chart) (hH : 0 < a.H)
    (i : Branch w hF j s) (q : w.Code (j.val + 1) (a.nextMenu hF j menu k))
    (he : q.tape = a.update s.tape ((S).write i)) : w.Balanced j s.frame q.frame := by
  let f := s.frame
  have hp := Frame.prepared w.c a.p a.l hF j f
  obtain ⟨t, β, h, _⟩ := Wave.execute C hp.separate f.stage f.address (hp.inputs f.match')
    f.layout f.valid (fun y hy => w.room _ (f.reach.trans hy)) f.calm
  have hL : (t i).Layout w.atlas.src w.atlas.dst a.g :=
    ⟨f.layout.loopless, (h i).reach.ports_eq.symm ▸ f.layout.incident,
      (h i).reach.ports_eq.symm ▸ f.layout.unique, (h i).reach.ports_eq.symm ▸ f.layout.degree⟩
  have hm := hp.outputs f.match' (h i)
  have hb := body_next w hF j s hk i q he
  have heq v : q.frame.stage.energyCre a.chart a.H a.g v = (t i).energyCre a.chart a.H a.g v := by
    rw [← q.frame.match'.energyCre w.π.edge, ← hm.energyCre w.π.edge, hb]
  have htq v : q.frame.stage.timeCre a.chart a.H a.U v = (t i).timeCre a.chart a.H a.U v := by
    rw [← q.frame.match'.timeCre q.frame.layout w.π.edge, ← hm.timeCre hL w.π.edge, hb]
  have hreg := (h i).history.regional hP hH f.layout (w.loc j)
    (fun a => ⟨_, fun v hv => w.loc_of_leader j (affected w hF j s a v hv)⟩)
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [heq]
    exact hreg.1
  · simp_rw [htq]
    exact hreg.2.1
  · intro v hv
    rw [heq, htq]
    exact hreg.2.2 v (fun a ha => hv ⟨_, affected w hF j s a v ha⟩)

theorem step_balanced (hP : 0 < a.chart) (hH : 0 < a.H) :
    ∃ q : Branch w hF j s → w.Code (j.val + 1) (a.nextMenu hF j menu k),
      (∀ i, (q i).tape = a.update s.tape ((S).write i)) ∧
      (∀ i, w.Balanced j s.frame (q i).frame) ∧
      ∀ u v, w.eval s.frame u v = ∑ i, scalar w hF j s i * w.eval (q i).frame u v := by
  obtain ⟨q, he, hq⟩ := step w hF j s hk
  exact ⟨q, he, fun i => balanced_of_tape w hF j s hk hP hH i (q i) (he i), hq⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
end

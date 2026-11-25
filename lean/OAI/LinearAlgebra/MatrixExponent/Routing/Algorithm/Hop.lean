import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Padding
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Compatible
import OAI.LinearAlgebra.MatrixExponent.Protocol.ReplayRel
import OAI.LinearAlgebra.MatrixExponent.Protocol.Wired
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Computability

/-!
# Agreement of branch kernels for arbitrary actions

The inventory execution and the unrenamed kernels already work over any
group. Compare these kernels on matching charts and then transfer to the
transport coordinates. This extends Control.Sample and Control.Compatible.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Coloring Transport
open Protocol (Pin)
open scoped Classical

namespace Rig
variable {G F J : Type} [Group G] [Field F] {U : J → Subgroup G} {g : G}
    {a : Parameters F U g} (s : Rig a)

private def demandPos {h W : ℕ} (i : Protocol.End (fun _ : Site h => W)) : Fin W ⊕ Fin W :=
  if i.2 then .inr i.1.2 else .inl i.1.2

local instance {h : ℕ} : DecidableEq (Site h) := Classical.decEq _

private theorem unrenamed_demand {h : ℕ} [MulAction G (Site h)] (σ : Equiv.Perm (B h))
    (hc : ∀ i : Site h, (a.balls (Site h)).name i ((a.balls (Site h)).shape i).dst = inflate h σ i)
    (u : s.clock.path (Site h)) (i : Site h) :
    (s.execute.kernel u i).pull
      (fun x => demandPos ((Protocol.demandRename (a.balls (Site h))
        a.table σ s.clock.width hc).eqv x.val))
      (fun x => (s.endpoints u x.val).2) = s.unrenamed u i := by
  refine congrArg (fun k => (s.execute.kernel u i).pull k
    (fun x => (s.endpoints u x.val).2)) ?_
  funext x
  obtain ⟨p, l, rfl⟩ := Pin.exists_atCopy (T := Protocol.request (a.balls (Site h)) a.table)
    (z := Stock.copies ((a.balls (Site h)).payload a.table) s.clock.width) x
  obtain ⟨j|j, v⟩ := p
  · have hl : l.val < s.clock.width := by
      have := l.isLt
      simpa [Stock.copies, Market.payload] using this
    have he := Protocol.demandRename_apply (a.balls (Site h)) a.table σ s.clock.width hc j
      l ⟨l.val, hl⟩ rfl v.val
    refine (congrArg demandPos he).trans ?_
    let side : Bool := v.val
    let slot : Fin s.clock.width := ⟨l.val, hl⟩
    change (if side then (Sum.inr slot : Fin _ ⊕ Fin _) else Sum.inl slot) =
      if some side = some true then Sum.inr slot else Sum.inl slot
    simp only [Option.some.injEq]
  · have := l.isLt
    simp [Stock.copies, Market.payload] at this

end Rig

namespace Rig
variable {K G J : Type} [Field K] [Group G] {U : J → Subgroup G} {g : G}
  {a : Parameters K U g} (s : Rig a)
  {I V : Type} [Fintype I] [MulAction G I] [Nonempty I]
  [Fintype V] [MulAction G V] [Nonempty V] {i : I} {j : V}

private abbrev branchPorts (I : Type) [Fintype I] [MulAction G I] :=
  marketPorts (I := I) a.core a.radius a.unit g a.reach s.w s.hw

theorem branch_match (x : s.clock.path I) (y : s.clock.path V)
    (hh : s.clock.chartView s.w s.j₀ ⟨⟨I, i⟩, s.clock.selector x⟩ =
      s.clock.chartView s.w s.j₀ ⟨⟨V, j⟩, s.clock.selector y⟩)
    (hg : a.generators ⟨I, i⟩ = a.generators ⟨V, j⟩) :
    s.unrenamed x i = s.unrenamed y j := by
  obtain ⟨f, he, hk, hd, hr⟩ := s.clock.replay_of_view s.w s.j₀ s.hw s.h₀ x y hh
  have hv := f.replay_rel a.offers (s.branchPorts I) (s.branchPorts V) s.clock.height a.nz s.clock.room
    s.clock.μ a.path hk hd (a.ready I) (a.ready V) a.local_supply hr
  obtain ⟨hw, heq⟩ := Protocol.execute_start_rel (s.clock.runs I) (s.clock.runs V)
    (a.copies_match f he) hv
  exact s.unrenamed_eq f he hg hw heq

end Rig

namespace Algorithm
variable {F : Type} [Field F] {m h : ℕ} (T : Layout F m) (s : Rig T.params)
    (σ : Equiv.Perm (B h))

abbrev arena :=
  letI := T.action h σ
  T.params.balls (Site h)

abbrev Path :=
  letI := T.action h σ
  s.clock.path (Site h)

abbrev requests (u : Path T s σ) : (arena T σ).Edge → ℕ :=
  letI := T.action h σ
  s.widthAt u

abbrev choose (u : Path T s σ) : Site h → B s.clock.bits :=
  letI := T.action h σ
  s.clock.selector u

abbrev place (u : Path T s σ) : Protocol.End (requests T s σ u) ↪ Port h s.p :=
  letI := T.action h σ
  s.endpoints u

abbrev src (e : (arena T σ).Edge) := (arena T σ).name e.1 e.2.val.1
abbrev dst (e : (arena T σ).Edge) := (arena T σ).name e.1 e.2.val.2

abbrev initial := Protocol.Demand F σ s.clock.width
abbrev result (u : Path T s σ) := Protocol.Links F (src T σ) (dst T σ) (requests T s σ u)

theorem target_at (i : Site h) :
    (arena T σ).name i ((arena T σ).shape i).dst = inflate h σ i := by
  let _ := T.action h σ
  change (market _ _ _ _ _).name i ((market _ _ _ _ _).shape i).dst = _
  rw [market_dst, inv_inv]
  exact T.target h σ i

def operator : (initial T s σ).Expansion (result T s σ) := by
  let _ := T.action h σ
  exact (s.execute (I := Site h)).rename
    (Protocol.demandRename (T.params.balls (Site h)) T.params.table σ s.clock.width
      (target_at T σ)) (fun _ => .refl _)

def side (i : Site h) (x : (initial T s σ).localPort i) : Fin s.clock.width ⊕ Fin s.clock.width :=
  if (x.val.2 : Bool) = true then .inr x.val.1.2 else .inl x.val.1.2

def channel (u : Path T s σ) (i : Site h) (x : (result T s σ u).localPort i) : B s.p :=
  (place T s σ u x.val).2

structure Example where
  h : ℕ
  σ : Equiv.Perm (B h)
  u : Path T s σ
  i : Site h

def sample (t : Example T s) : Profile F s.p s.clock.width :=
  ((operator T s t.σ).kernel t.u t.i).pull (side T s t.σ t.i) (channel T s t.σ t.u t.i)

def observed (t : Example T s) : s.clock.Input :=
  ⟨@Root.mk _ _ _ (T.action t.h t.σ) t.i, choose T s t.σ t.u⟩

def Compatible : Prop :=
  ∃ E : Finset T.G, ∀ x y : Example T s,
    let u := observed T s x
    let v := observed T s y
    Root.Agree E u.toRoot v.toRoot →
    (∀ i ∈ E, u.mark (u.label i) = v.mark (v.label i)) → sample T s x = sample T s y

local instance {h : ℕ} : DecidableEq (Site h) := Classical.decEq _

private theorem side_def {m h : ℕ} (T : Layout F m) (s : Rig T.params)
    (σ : Equiv.Perm (B h)) (i : Site h) (x : (initial T s σ).localPort i) :
    side T s σ i x = Rig.demandPos x.val := by
  unfold side Rig.demandPos
  congr 1

theorem sample_eq (x : Example T s) :
    sample T s x = letI := T.action x.h x.σ; s.unrenamed x.u x.i := by
  let _ := T.action x.h x.σ
  refine Eq.trans ?_ (s.unrenamed_demand x.σ (target_at T x.σ) x.u x.i)
  refine congrArg (fun k => (s.execute.kernel x.u x.i).pull k
    (fun v => (s.endpoints x.u v.val).2)) ?_
  exact funext fun j => side_def T s x.σ x.i _

theorem compatible : Compatible T s := by
  have ht := (s.clock.chartView_local s.w s.j₀).pair (Decor.local_root T.params.local_generators)
  obtain ⟨E, hE⟩ := ht
  refine ⟨E, fun x y hx hy => ?_⟩
  obtain ⟨he, hg⟩ := Prod.mk.inj (hE (observed T s x) (observed T s y) hx hy)
  let _ := T.action x.h x.σ
  let _ := T.action y.h y.σ
  exact (sample_eq T s x).trans ((s.branch_match x.u y.u he hg).trans
    (sample_eq T s y).symm)

end Algorithm
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# The finite menu of local profiles

A profile can depend on the branch only through finitely many
observations. Record these observations, the local guard, and the
enable mask. A class with no representative receives weight zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm

open Coloring Transport
open scoped Classical

variable {F : Type} [Field F] {m : ℕ} (T : Layout F m) (s : Rig T.params)

abbrev active (x : s.clock.Input) (j : B s.p) :=
  (s.bank.program T.params.unit _ T.params.reach s.count x j).1

def masked (v : Example T s) : Profile F s.p s.clock.width :=
  (sample T s v).mask (s.clock.guard s.w (observed T s v)) (active T s (observed T s v))

structure Palette where
  l : ℕ
  key : s.clock.Input → B l
  local_key : Decor.Local key
  table : B l → Profile F s.p s.clock.width
  fast : ∀ i, Protocol.Frame.Fast (table i)
  agrees : ∀ v, table (key (observed T s v)) = masked T s v
  valid : ∀ x z a c, table (key x) z a c ≠ 0 →
    s.clock.guard s.w x = true ∧ ∀ j, active T s x j ≠ true → ∀ i, c j i = false

private abbrev Pattern (E : Finset T.G) :=
  ((↥E → ↥E → Bool) × (↥E → B s.clock.bits)) × Bool × (B s.p → Bool)

private def pattern (E : Finset T.G) (x : s.clock.Input) : Pattern T s E :=
  ((fun i j => x.see i j, fun i => x.mark (x.label i)), s.clock.guard s.w x, active T s x)

private theorem pattern_local (E : Finset T.G) :
    Decor.Local (pattern T s E) := by
  have ho : Decor.Local (fun x : s.clock.Input => (pattern T s E x).1) :=
    ⟨E, fun _ _ hh hm => Prod.ext (funext fun i => funext fun j => hh _ i.property _ j.property)
      (funext fun i => hm _ i.property)⟩
  have he := s.bank.program_local T.params.unit _ T.params.reach s.count
    (s.clock.count_local s.w s.j₀)
  exact ho.pair ((s.clock.guard_local s.w).pair (he.map (fun v j => (v j).1)))

theorem palette (he : Compatible T s) : Nonempty (Palette T s) := by
  obtain ⟨E, hE⟩ := he
  let code := Coloring.encode (Pattern T s E)
  let k := code ∘ pattern T s E
  have same (x y : Example T s) (eq : k (observed T s x) = k (observed T s y)) :
      masked T s x = masked T s y := by
    have e := code.injective eq
    have hs := hE x y
      (fun i hi j hj => congrArg (fun z => z.1.1 ⟨i, hi⟩ ⟨j, hj⟩) e)
      (fun i hi => congrArg (fun z => z.1.2 ⟨i, hi⟩) e)
    exact congrArg₂ (fun (f : Profile F s.p s.clock.width) v => f.mask v.1 v.2)
      hs (congrArg Prod.snd e)
  let off : Profile F s.p s.clock.width := Protocol.Frame.diagonal (fun _ _ => 0)
  let f i := if h : ∃ v, k (observed T s v) = i then masked T s h.choose else off
  refine ⟨⟨_, k, (pattern_local T s E).map code, f, ?_, ?_, ?_⟩⟩
  · intro i
    dsimp only [f]
    split
    · rename_i hh
      apply Profile.mask_fast
      exact ((operator T s hh.choose.σ).fast _ _).pull _ _
    · exact Protocol.Frame.fast_diagonal _
  · intro v
    have hv : ∃ u, k (observed T s u) = k (observed T s v) := ⟨v, rfl⟩
    simp only [f, dite_eq_left hv]
    exact same _ _ hv.choose_spec
  · intro x z a c hn
    dsimp only [f] at hn
    split at hn
    · rename_i hv
      have eq := congrArg Prod.snd (code.injective hv.choose_spec)
      obtain ⟨hg, ha⟩ := Prod.mk.inj eq
      unfold masked Profile.mask at hn
      rw [hg, ha] at hn
      by_contra hh
      exact hn (ite_eq_right hh)
    · simp [off, Protocol.Frame.diagonal] at hn

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-!
# Transport from an arbitrary resolving dispatch

This extends Control.Engine, Control.Correct and Control.Install. The local
program and weight exponent are fixed at all heights and scales. The theorem
makes no efficiency assumption on the dispatch.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring Transport
open scoped Classical

section
variable {F : Type} [Field F] {m h z : ℕ} (T : Layout F m) (s : Rig T.params)
    (σ : Equiv.Perm (B h)) (u : Path T s σ) (i : Site h)

theorem sample_apply {group : Port h s.p → ℕ} {a : Orders h s.p}
    (P : Protocol.Placement (src T σ) (dst T σ) (requests T s σ u) group a)
    (hP : P.embed = place T s σ u) (x y : Site h → Data s.clock.width (2 ^ z))
    (c : Site h → Channels s.p (2 ^ z)) :
    (sample T s ⟨h, σ, u, i⟩).apply z (x i) (y i) (c i) =
      (operator T s σ).kernel u i z ((initial T s σ).view i (Protocol.outside σ _ x y))
        ((result T s σ u).view i (P.inside c)) := by
  unfold sample Profile.apply Protocol.Frame.pull
  refine congrArg₂ ((operator T s σ).kernel u i z) ?_ ?_
  · funext ⟨⟨⟨j, k⟩, b⟩, e⟩ t
    let v := Sum.elim (Function.curry (x i)) (Function.curry (y i))
    cases b
    · have hs : side T s σ i ⟨⟨⟨j, k⟩, false⟩, e⟩ = .inl k := ite_eq_right Bool.false_ne_true
      change v (side T s σ i ⟨⟨⟨j, k⟩, false⟩, e⟩) t = x j (k, t)
      rw [hs]
      exact congrArg (fun l => x l (k, t)) (show j = i from e).symm
    · have hs : side T s σ i ⟨⟨⟨j, k⟩, true⟩, e⟩ = .inr k := ite_eq_left rfl
      change v (side T s σ i ⟨⟨⟨j, k⟩, true⟩, e⟩) t = y (inflate h σ j) (k, t)
      rw [hs]
      exact congrArg (fun l => y l (k, t)) (show inflate h σ j = i from e).symm
  · funext k t
    have he : (P.embed k.val).1 = i := (P.owner _).trans k.property
    change c i ((place T s σ u k.val).2, t) = c (P.embed k.val).1 ((P.embed k.val).2, t)
    rw [he, hP]

end

section
variable {F : Type} [Field F] {m h : ℕ} (T : Layout F m) (s : Rig T.params)
    (P : Palette T s)

abbrev Selectors (h : ℕ) := Format.vec (h + 1) (.addr s.clock.bits)
abbrev Commands (h : ℕ) := Controls h s.p (.addr P.l)

def atSite (σ : Equiv.Perm (B h)) (z : (Selectors T s h).obj) (i : Site h) : s.clock.Input :=
  ⟨@Root.mk _ _ _ (T.action h σ) i, z⟩

abbrev Dispatch (h : ℕ) := ((Perm h).pair (Selectors T s h)).obj → (Commands T s P h).obj

def Resolves (f : Dispatch T s P h) : Prop :=
  ∀ σ : Equiv.Perm (B h), ∀ z i, f (σ, z) i =
    Decor.resolve (s.program P.key (atSite T s σ z i))
      (fun j => (T.action h σ).smul (s.bank.hop j) i)

abbrev systemOf (f : Dispatch T s P h) (group : Port h s.p → ℕ) (z : ℕ) :
    System F h s.p s.clock.width (2 ^ z) where
  selector := Selectors T s h
  config := .addr P.l
  group := group
  dispatch := f
  kernel i := (P.table i).apply z

structure Engine (h : ℕ) where
  f : Dispatch T s P h
  group : Port h s.p → ℕ
  resolves : Resolves T s P f
  groups : ∀ σ x y i j, s.bank.generator T.params.unit i = s.bank.generator T.params.unit j →
    (T.action h σ).smul (s.bank.generator T.params.unit i).val x = y →
    group (x, i) = group (y, j)

namespace Engine

variable {T s P} (H : Engine T s P h) (σ : Equiv.Perm (B h))

abbrev system (z : ℕ) := systemOf T s P H.f H.group z

theorem key (z : (Selectors T s h).obj) (i : Site h) :
    (H.f (σ, z) i).1 = P.key (atSite T s σ z i) := by rw [H.resolves σ z i]; rfl

theorem orders (z : (Selectors T s h).obj) :
    letI := T.action h σ
    commands (H.f (σ, z)) = s.bank.orders T.params.unit _ T.params.reach s.count z := by
  funext ⟨i, j⟩
  unfold commands
  rw [H.resolves σ z i]
  rfl

theorem enabled (z : (Selectors T s h).obj) (i : Site h) (j : B s.p) :
    (i, j) ∈ Enabled (commands (H.f (σ, z))) ↔ active T s (atSite T s σ z i) j = true := by
  simp only [Enabled, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [H.orders]
  rfl

def placement (u : Path T s σ) :
    Protocol.Placement (src T σ) (dst T σ) (requests T s σ u) H.group
      (commands (H.f (σ, choose T s σ u))) := by
  let _ := T.action h σ
  exact s.bank.placement T.params.unit _ T.params.reach s.count (s.clock.selector u) (s.widthAt u)
    (s.bounded u) (s.clock.count_branch s.w s.j₀ s.hw s.h₀ u)
    H.group (H.groups σ) _ (H.orders σ _)

end Engine
end

variable {F : Type} [Field F] {m h z : ℕ}

private theorem injective_selector {G J I : Type} [Group G] {U : J → Subgroup G} {g : G}
    {a : Parameters F U g} (s : Rig a) [Fintype I] [MulAction G I] :
    Function.Injective (s.clock.selector (I := I)) :=
  (a.balls I).selector_injective a.offers s.clock.batch s.clock.bound s.clock.μ a.path s.clock.width

namespace Engine
variable {T : Layout F m} {s : Rig T.params} {P : Palette T s} (H : Engine T s P h)
    (σ : Equiv.Perm (B h))

private def codes : Path T s σ ↪ (Selectors T s h).obj := by
  let _ := T.action h σ
  exact ⟨choose T s σ, injective_selector s⟩

private theorem eligible (t : (Selectors T s h).obj) :
    (∀ i, s.clock.guard s.w (atSite T s σ t i) = true) ↔ ∃ u, choose T s σ u = t := by
  let _ := T.action h σ
  have ht := s.clock.guard_iff s.w s.hw t
  refine ⟨fun h => (ht.mp h).exists, fun ⟨u, hu⟩ => ht.mpr ⟨u, hu, ?_⟩⟩
  exact fun v hv => injective_selector s (hv.trans hu.symm)

private theorem agrees (u : Path T s σ) (x y : Site h → Data s.clock.width (2 ^ z))
    (c : Site h → Channels s.p (2 ^ z)) (hc : Protocol.Padded (commands (H.f (σ, choose T s σ u))) c)
    (i : Site h) :
    (P.table (H.f (σ, choose T s σ u) i).1).apply z (x i) (y i) (c i) =
      (operator T s σ).kernel u i z ((initial T s σ).view i (Protocol.outside σ _ x y))
        ((result T s σ u).view i ((H.placement σ u).inside c)) := by
  let e : Example T s := ⟨h, σ, u, i⟩
  rw [H.key]
  change (P.table (P.key (observed T s e))).apply _ _ _ _ = _
  rw [P.agrees]
  have hg : s.clock.guard s.w (observed T s e) = true :=
    (eligible σ (choose T s σ u)).mpr ⟨u, rfl⟩ i
  have hy : ∀ j, active T s (observed T s e) j ≠ true → ∀ k, c i (j, k) = false := by
    intro j hj
    exact hc (i, j) (mt (H.enabled σ _ i j).mp hj)
  trans (sample T s e).apply z (x i) (y i) (c i)
  · exact ite_eq_left ⟨hg, hy⟩
  · exact sample_apply T s σ u i _ rfl x y c

private theorem surviving (t : (Selectors T s h).obj) (x y : Site h → Data s.clock.width (2 ^ z))
    (c : Site h → Channels s.p (2 ^ z)) (hne : (H.system z).value (H.f (σ, t)) x y c ≠ 0) :
    (∃ u, choose T s σ u = t) ∧ Protocol.Padded (commands (H.f (σ, t))) c := by
  have hi (i : Site h) : s.clock.guard s.w (atSite T s σ t i) = true ∧
      ∀ j, active T s (atSite T s σ t i) j ≠ true → ∀ k, c i (j, k) = false := by
    have hw := Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ _)
    change (P.table (H.f (σ, t) i).1).apply z (x i) (y i) (c i) ≠ 0 at hw
    rw [H.key] at hw
    exact P.valid _ _ _ _ hw
  refine ⟨(eligible σ t).mp (fun i => (hi i).1), ?_⟩
  rintro ⟨i, j⟩ hij k
  exact (hi i).2 _ (mt (H.enabled σ t i j).mpr hij) k

private theorem width (u : Path T s σ) :
    2 * (∑ e, requests T s σ u e) ≤ 4812 * s.clock.width * 2 ^ h := by
  let _ := T.action h σ
  have he := s.clock.width_total s.w s.hw u
  change (∑ e, requests T s σ u e) ≤ 1203 * Fintype.card (Site h) * s.clock.width at he
  rw [show Fintype.card (Site h) = 2 ^ h * 2 by simp [pow_succ]] at he
  exact (Nat.mul_le_mul_left 2 he).trans_eq (by ring)

theorem correct (z : ℕ) : (H.system z).Correct 4812 := by
  apply Protocol.system_correct
  intro σ
  exact ⟨{
    E := (arena T σ).Edge
    I := Path T s σ
    src := src T σ
    dst := dst T σ
    m := requests T s σ
    proc := operator T s σ
    choose := codes σ
    place := H.placement σ
    cost := width σ
    agrees := H.agrees σ
    invalid := H.surviving σ
  }⟩

end Engine

/-- The same local instructions and profile table work for all permitted
heights. The port packing at each height is independent of the dispatch,
scale, and permutation. -/
theorem Layout.protocol (T : Layout F m) :
    ∃ (s : Rig T.params) (P : Palette T s) (D : ℕ),
      ∀ h b, h / m + T.overhead ≤ b → b ≤ h →
      ∃ group : Port h s.p → ℕ,
        (∀ x, group x < 2 ^ (h + 2)) ∧
        (∀ i, (Finset.univ.filter (fun k => group k = i)).card ≤ 2 ^ (b + s.p)) ∧
        ∀ f : Dispatch T s P h, Resolves T s P f → ∀ z,
          (systemOf T s P f group z).Correct 4812 ∧
          Install.Weight F (systemOf T s P f group z).localWeight (2 ^ z * (100 + z) ^ D) := by
  obtain ⟨s⟩ := T.params.rig
  obtain ⟨P⟩ := palette T s (compatible T s)
  obtain ⟨d, hd⟩ := profile_weight P.table P.fast
  refine ⟨s, P, d, fun h b hb hb' => ?_⟩
  obtain ⟨g, hl, hg, hm⟩ := T.portGroup h b s.p hb hb' (s.bank.generator T.params.unit)
  refine ⟨g, hl, hg, fun f hf z => ?_⟩
  let H : Engine T s P h := ⟨f, g, hf, hm⟩
  exact ⟨H.correct z, hd z⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-!
# Resolving a layout by indexed reads

First evaluate the fixed lists of observation and hop permutations.
Their address tables are shared by all sites. Each site's decision
table sees only comparisons and selector marks. The chosen remote
address is then read from the hop table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring Transport

variable {w h p q t l c : ℕ}

private abbrev Addresses (h t : ℕ) := B t → Site h → Site h
private abbrev Source (h t q : ℕ) := (B t → Site h) × (Site h → B q)
private abbrev InputFromDispatch (h t p q : ℕ) := (Site h → B q) × Addresses h t × Addresses h p

private def view (x : Source h t q) : RAM.Observation t q :=
  (fun j k => decide (x.1 j = x.1 k), x.2 ∘ x.1)

private def dispatchAt (b : RAM.Observation t q → Decor.Plan l p p)
    (x : InputFromDispatch h t p q) (i : Site h) :=
  Decor.resolve (b (view (fun j => x.2.1 j i, x.1))) (fun j => x.2.2 j i)

private theorem addresses_at (ht : t ≤ w) (hh : h + 1 ≤ w) (i : Site h) :
    RAM w (fun (x : Addresses h t) j => x j i) (2 ^ t * 3) :=
  .tab ht _ (fun j => (RAM.at ht j).comp (.at hh i))

private def viewCost (t : ℕ) := 2 ^ t * (2 ^ t * 7 + 1) + (3 + 2 ^ t * 6) + 1

private theorem view_ram (ht : t ≤ w) (hh : h + 1 ≤ w) :
    RAM w (view : Source h t q → _) (viewCost t) := by
  have e : RAM w (fun (x : Source h t q) j k => decide (x.1 j = x.1 k)) (2 ^ t * (2 ^ t * 7 + 1)) :=
    .tab ht _ (fun j => .tab ht _ (fun k =>
      ((RAM.fst.comp (.at ht j)).pair (RAM.fst.comp (.at ht k))).comp (.eq hh)))
  exact e.pair ((RAM.snd.pair RAM.fst).comp (RAM.gather hh ht))

private theorem resolve_ram (hp : p ≤ w) :
    RAM w (fun x : Decor.Plan l p p × (B p → Site h) => Decor.resolve x.1 x.2)
      (2 + 2 ^ p * 28 + 1) := by
  let A := Decor.Plan l p p × (B p → Site h)
  have H : RAM w (fun x : A => (Decor.resolve x.1 x.2).2) (2 ^ p * 28) := by
    refine RAM.tab hp _ (m := 27) (fun j => ?_)
    have T : RAM w (fun x : A => x.1.2 j) 3 := (RAM.fst.comp RAM.snd).comp (.at hp j)
    have K := (T.comp RAM.snd).comp RAM.snd
    have a := (RAM.snd.pair (K.comp RAM.fst)).comp (.read hp)
    exact (T.comp RAM.fst).pair (((T.comp RAM.snd).comp RAM.fst).pair (a.pair (K.comp RAM.snd)))
  exact (RAM.fst.comp RAM.fst).pair H

private def rowCost (t p c : ℕ) := 20 + 3 * 2 ^ t + viewCost t + c + 31 * 2 ^ p

private theorem dispatchAt_ram (ht : t ≤ w) (hh : h + 1 ≤ w) (hp : p ≤ w)
    {b : RAM.Observation t q → Decor.Plan l p p} (hb : RAM w b c) :
    RAM w (dispatchAt (h := h) b) (2 ^ (h + 1) * (rowCost t p c + 1)) := by
  refine RAM.tab hh _ (fun i => ?_)
  have X : RAM w (fun (x : InputFromDispatch h t p q) j => x.2.1 j i) (2 + 2 ^ t * 3) :=
    (RAM.snd.comp RAM.fst).comp (addresses_at ht hh i)
  have Y : RAM w (fun (x : InputFromDispatch h t p q) j => x.2.2 j i) (2 + 2 ^ p * 3) :=
    (RAM.snd.comp RAM.snd).comp (addresses_at hp hh i)
  have H := ((X.pair RAM.fst).comp (view_ram ht hh)).comp hb
  exact ((H.pair Y).comp (resolve_ram hp)).mono (by unfold rowCost; omega)

variable {F : Type} [Field F] {m : ℕ}

theorem Layout.dispatch (T : Layout F m) (ht : T.Computes Computable) (s : Rig T.params)
    (P : Palette T s) :
    ∃ c, ∀ᶠ h in Filter.atTop, ∃ f : Dispatch T s P h,
      Resolves T s P f ∧ RAM (3 * (h + 1) + 10) f (2 ^ (h + 1) * (100 + h) ^ c) := by
  obtain ⟨t, g, b, w, c, hb, he⟩ := RAM.menu (s.program_local P.local_key)
  obtain ⟨d, hd⟩ := T.addresses ht g
  obtain ⟨e, he'⟩ := T.addresses ht s.bank.hop
  let D := max 1 (max d e)
  refine ⟨D + 1, ?_⟩
  filter_upwards [hd, he', Filter.eventually_ge_atTop (w + t + s.p + rowCost t s.p c)]
    with h hX hY hh
  obtain ⟨X, hX, eX⟩ := hX
  obtain ⟨Y, hY, eY⟩ := hY
  let v := 3 * (h + 1) + 10
  have H := dispatchAt_ram (show t ≤ v by unfold v; omega) (show h + 1 ≤ v by unfold v; omega)
    (show s.p ≤ v by unfold v; omega) (hb.widen (by unfold v; omega))
  let A := ((Perm h).pair (Selectors T s h)).obj
  have M : RAM v (fun x : A => (x.2, X x.1, Y x.1))
      (1 + (1 + (2 ^ (h + 1) * (100 + h) ^ d + 2 ^ (h + 1) * (100 + h) ^ e + 1)) + 1) :=
    RAM.snd.pair (RAM.fst.comp (hX.pair hY))
  refine ⟨_, ?_, (M.comp H).mono ?_⟩
  · intro σ z i
    let r := atSite T s σ z i
    have eq : view (fun j => X σ j i, z) = RAM.observe g r := by
      apply Prod.ext
      · funext a b
        rw [Bool.eq_iff_iff]
        simp only [view, RAM.observe, Root.see, decide_eq_true_eq, eX]
        rfl
      · funext a
        exact congrArg z (eX σ a i)
    change Decor.resolve (b (view (fun j => X σ j i, z))) (fun j => Y σ j i) = _
    rw [eq, he]
    exact congrArg _ (funext fun j => eY σ j i)
  · have hr : 2 ^ (h + 1) * (rowCost t s.p c + 1) ≤ 2 ^ (h + 1) * (100 + h) ^ 1 :=
      Nat.mul_le_mul_left _ (by rw [pow_one]; omega)
    have := budget_mono (h + 1) h (show 1 ≤ D by unfold D; omega)
    have := budget_mono (h + 1) h (show d ≤ D by unfold D; omega)
    have := budget_mono (h + 1) h (show e ≤ D by unfold D; omega)
    have := budget_step (h + 1) h D
    have := budget_base (h + 1) h D
    have := Nat.two_pow_pos (h + 1)
    omega

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-! # The generator carried by an enabled port -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring Transport
open scoped Classical

variable {F : Type} [Field F] {m h : ℕ} {T : Layout F m} {s : Rig T.params}
  {P : Palette T s} {f : Dispatch T s P h}

/-- Even for an arbitrary selector, the ends of every enabled hop
carry the same generator, acting in one of its two directions. -/
theorem Resolves.hop (hf : Resolves T s P f) (σ : Equiv.Perm (B h))
    (z : (Selectors T s h).obj) (t : Port h s.p) (ht : t ∈ Enabled (commands (f (σ, z)))) :
    let u := (commands (f (σ, z)) t).2.2
    let g := s.bank.generator T.params.unit t.2
    g = s.bank.generator T.params.unit u.2 ∧
      ((T.action h σ).smul g.val t.1 = u.1 ∨ (T.action h σ).smul g.val⁻¹ t.1 = u.1) := by
  let _ := T.action h σ
  have ha : commands (f (σ, z)) = s.bank.orders T.params.unit _ T.params.reach s.count z := by
    funext ⟨i, j⟩
    unfold commands
    rw [hf σ z i]
    rfl
  rw [ha] at ht ⊢
  obtain ⟨e, b, j, rfl, hj⟩ := s.bank.covered T.params.unit _ T.params.reach s.count z t
    (Finset.mem_filter.mp ht).2
  rw [s.bank.orders_pin T.params.unit _ T.params.reach s.count z e b j hj]
  let x := attach _ T.params.unit _ _ T.params.reach e b j
  let y := attach _ T.params.unit _ _ T.params.reach e (!b) j
  let g := s.bank.generator T.params.unit (s.bank x.2)
  change g = s.bank.generator T.params.unit (s.bank y.2) ∧
    (g.val • x.1 = y.1 ∨ g.val⁻¹ • x.1 = y.1)
  simp only [g, Bank.generator, Bank.read_slot, Option.elim_some]
  refine ⟨rfl, ?_⟩
  rcases attach_link _ T.params.unit _ _ T.params.reach e b j with he | he
  · exact .inl he
  · exact .inr (inv_smul_eq_iff.mpr he.symm)

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

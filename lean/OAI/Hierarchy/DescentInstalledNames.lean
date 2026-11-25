import OAI.Hierarchy.DescentChosenRouterNames
import OAI.Hierarchy.DescentResetInstalled

namespace OAI
/-! # Installing the paid bases of the chosen dyadic reset in their real physical sites -/

namespace Hierarchy.DescentChosenRouter
open DescentGL DescentColonies DescentBaseProfile DescentRouterSlots DescentMixedRouter DescentResetInvoice
open DescentRotor Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]

/-- Records a chosen remix, the physical old endpoints of every bundle, the
shared direct-link ticket and the actual output reservation. The fallback map
is defined on an old occurrence; all its bundles therefore use the same old terminal. -/
structure Placement (V I H A : Type) [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
    (k Y : ℕ) where
  b : V→ℕ
  depth : ∀v,b v≤k
  L : Layout k
  keys : Finset (V×ℕ)
  hub : V→Prop
  old : Bool→I→V×Block k
  row : Bool→V×Block k→Fin Y
  fall : Bool→V×Block k→H
  ends : Bool→A→Good b keys hub
  span : A→ℕ
  room : ∀s g,(∑a : {a // ends s a=g},span a.val)≤Y
  ticket : {i // useRotor b depth L keys hub old i}→Reserve span
  owned : ∀i s,ends s (ticket i).1=base b depth L keys hub old i s
  columns : Bool→Good b keys hub→Equiv.Perm (Fin Y) := fun _ _=>Equiv.refl _
  fallbackBook : ∀s (t : H), Book (LinkId (owner b depth L keys hub old ends span fall) s (.inr t)) :=
    fun _ _=>Book.observed _


variable {k n : ℕ} (P : Placement V I H A k (2^n))
abbrev Placement.Good := DescentChosenRouter.Good P.b P.keys P.hub
abbrev Placement.Site := DescentChosenRouter.Site (H:=H) P.b P.keys P.hub
abbrev Placement.Public := DescentChosenRouter.Public (H:=H) (Y:=2^n) P.b P.keys P.hub
abbrev Placement.Contact := DescentChosenRouter.Contact P.b P.depth P.L P.keys P.hub P.old P.span P.fall

def Placement.contact : I→P.Contact := DescentChosenRouter.contact P.b P.depth P.L P.keys P.hub P.old
  P.span P.ticket P.fall
def Placement.input : Bool→I→P.Public := pub P.b P.depth P.L P.keys P.hub P.old P.row P.fall
def Placement.site (_ : Bool) : P.Public→P.Site := DescentChosenRouter.site P.b P.keys P.hub
def Placement.owner : Bool→P.Contact→P.Site := DescentChosenRouter.owner P.b P.depth P.L P.keys P.hub P.old
  P.ends P.span P.fall
theorem Placement.align (s : Bool) (i : I) : P.site s (P.input s i)=P.owner s (P.contact i) :=
  aligned P.b P.depth P.L P.keys P.hub P.old P.ends P.span P.ticket P.owned P.row P.fall s i

def head (s : Bool) (g : P.Good) := first (Y:=2^n) (H:=H) P.b P.keys P.hub s g
def tail (s : Bool) (g : P.Good) := (last P.b P.depth P.L P.keys P.hub P.old P.ends P.span P.room P.fall s g).trans
  (P.columns s g).toEmbedding
abbrev Cells (s : Bool) (g : P.Good) := Item P.contact P.owner s (.inl g)
def source (s : Bool) (g : P.Good) (e : Cells P s g) :=
  head P s g (root P.contact P.input P.site P.owner s (.inl g) P.align e)
def target (s : Bool) (g : P.Good) (e : Cells P s g) :=
  tail P s g (link P.contact P.owner s (.inl g) e)

variable {K : Type} [Field K] {h C₀ bits u : ℕ} (G : NonlinearExpanders.Graph n h) (hw : 0<bits)
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u P.contact P.input P.site P.owner P.align
variable (pay : ℝ)

/-- The complete actual installed devices, all from the same measured per-base
matrix budget. Formal construction below takes physical row/column loads. -/
abbrev Hardware := ∀s g,BaseCircuit K G C₀ bits u hw (source P s g) (target P s g) pay

def build {F B : ℝ} (hu : 0<u) (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures K G.arcs C₀ bits p)
    (unit : (u:ℝ)≤B) (scale : ((2^n:ℕ):ℝ)^2*bits≤F)
    (row : ∀s g i,(∑j,(matrixOfBundles (source P s g) (target P s g) i j:ℝ))≤9*F*B/((2^n:ℕ)*u:ℕ))
    (col : ∀s g j,(∑i,(matrixOfBundles (source P s g) (target P s g) i j:ℝ))≤9*F*B/((2^n:ℕ)*u:ℕ)) :
    Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw (F*B) :=
  fun s g=>Classical.choice (circuit_of_matrix G C₀ bits u hw hu menu _ _ unit scale (row s g) (col s g))

variable (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)

private def transportCircuit {E : Type} {a b : Fintype E} {src dst : E → Fin (2^n)}
    (circuit : @BaseCircuit E a n h K _ G C₀ bits u hw src dst pay) :
    @BaseCircuit E b n h K _ G C₀ bits u hw src dst pay := by
  cases Subsingleton.elim a b
  exact circuit

def selected (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay) (s : Bool) : (w : P.Site)→Ch s w
  | .inl g => .good (head P s g) (tail P s g) pay
      (transportCircuit (G:=G) (hw:=hw) (pay:=pay) (hardware s g))
  | .inr t => .exceptional ⟨fallback_root (Y:=2^n) P.b P.keys P.hub s t,P.fallbackBook s t⟩

local notation "sel" => selected P G hw pay hardware

theorem typed_name (s : Bool) (g : P.Good) : ((sel s (.inl g)).isExceptional=false) := rfl

theorem budget (s : Bool) (g : P.Good) : (sel s (.inl g)).goodBudget=pay := rfl

private theorem fallback_inactive (s : Bool) (t : H) : (s, Sum.inr t) ∉ rotorSites sel := by
  intro active
  have impossible : true = false := (Finset.mem_filter.mp active).2
  exact Bool.noConfusion impossible

/-- Each paid rotor is assigned its actual side and legal dyadic base ID. -/
theorem named :
    ∃ f : ↥(rotorSites sel) → Bool×BaseId P.b,Function.Injective f := by
  have hgood (a : ↥(rotorSites sel)) : ∃ g : P.Good, a.val.2=.inl g := by
    rcases a with ⟨⟨s,g|t⟩,mem⟩
    · exact ⟨g,rfl⟩
    · exact False.elim (fallback_inactive P G hw pay hardware s t mem)
  let f (a : ↥(rotorSites sel)) : Bool × BaseId P.b := (a.val.1,(hgood a).choose.val)
  refine ⟨f,fun a b eq=>?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (f a).1 = (f b).1
    exact congrArg Prod.fst eq
  rw [(hgood a).choose_spec,(hgood b).choose_spec]
  have same : (hgood a).choose.val = (hgood b).choose.val :=
    congrArg (fun p : Bool × BaseId P.b => p.2) eq
  exact congrArg Sum.inl (Subtype.ext same)

theorem per_base (p : Bool×P.Site) (active : p∈rotorSites sel) : (sel p.1 p.2).goodBudget≤pay := by
  rcases p with ⟨s,g|t⟩
  · exact le_rfl
  · exact False.elim (fallback_inactive P G hw pay hardware s t active)

theorem chosen_exceptional (s : Bool) (i : I) :
    (sel s (P.owner s (P.contact i))).isExceptional=true ↔ ¬useRotor P.b P.depth P.L P.keys P.hub P.old i := by
  have names : (∃ g : P.Good, P.owner s (P.contact i) = .inl g) ↔
      useRotor P.b P.depth P.L P.keys P.hub P.old i :=
    in_good_iff P.b P.depth P.L P.keys P.hub P.old P.ends P.span P.ticket P.fall s i
  cases atSite : P.owner s (P.contact i) with
  | inl g =>
    have run := names.mp ⟨g, atSite⟩
    simp [selected, Choice.isExceptional, run]
  | inr t =>
    have off : ¬ useRotor P.b P.depth P.L P.keys P.hub P.old i := by
      intro run
      obtain ⟨g, eq⟩ := names.mpr run
      have clash := atSite.symm.trans eq
      cases clash
    simp [selected, Choice.isExceptional, off]

/-- Ordinary core wires have no hub endpoint. A core wire using the fallback
tree therefore has an original endpoint in the actual reached/overflowed key set. -/
theorem flagged (core : Finset I) (ordinary : ∀i∈core,∀s,¬P.hub (P.old s i).1)
    (i : I) (fb : i∈badCore sel core) :
    label P.b (baseOf P.b P.depth P.L (P.old false i))∈P.keys ∨
      label P.b (baseOf P.b P.depth P.L (P.old true i))∈P.keys := by
  obtain ⟨member,atEnd⟩ := Finset.mem_filter.mp fb
  have no := atEnd.elim ((chosen_exceptional P G hw pay hardware false i).mp)
    ((chosen_exceptional P G hw pay hardware true i).mp)
  have marks := (fallback_iff P.b P.depth P.L P.keys P.hub P.old i).mp no
  have bad := marks.resolve_right (not_or.mpr ⟨ordinary i member false,ordinary i member true⟩)
  exact (Finset.mem_filter.mp bad).2

end
end Hierarchy.DescentChosenRouter

end OAI

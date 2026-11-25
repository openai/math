import OAI.Hierarchy.DescentPackedPrivateInput

namespace OAI
/-! # Unique physical roots in the shared host, coarse group and relative family ticket grid -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentChosenRouter DescentCommonHost DescentResetHostSize DescentRelativeContacts DescentHostDirectory
open DescentPackedPrivateMenu DescentPackedFallbackTree DescentSIMDLookup DescentRouterSlots DescentMixedRouter
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "X" => Z.placement
local notation "r" => (Z.k-T.commonDepth)
local notation "Y" => (2^Z.n:ℕ)

abbrev RootTicket := Code r ⊕ (Code r×Option (Fin Y))

def rootTicket : (X).Site→RootTicket Z T
  | .inl g=>.inl (goodLabel Z T g)
  | .inr t=>.inr (fallLabel Z T t,(T.code t).2.2)

def rootBlock (g : (X).Site) : DescentColonies.Block T.commonDepth :=
  ⟨(X).siteGroup T.commonDepth T.code g,siteGroup_lt (X) T.commonDepth T.code T.commonLow T.codeLegal g⟩

def rootLocation {H : ℕ} (vertex : Z.V↪Fin H) :
    (X).Site↪Fin H×DescentColonies.Block T.commonDepth×RootTicket Z T where
  toFun g:=(vertex (rootVertex Z T g),rootBlock Z T g,rootTicket Z T g)
  inj':=by
    intro a b eqn
    have vertexSame:=vertex.injective (congrArg Prod.fst eqn)
    have groupSame:=congrArg (fun z=>z.2.1.val) eqn
    have kindSame:=congrArg (fun z=>z.2.2) eqn
    cases a with
    | inl a=>
      cases b with
      | inl b=>
        have label:=Sum.inl.inj kindSame
        have residue:=congrArg (fun z : Code r=>z.val.2) label
        exact congrArg Sum.inl (Subtype.ext (DescentCanonicalPorts.recover (m:=T.commonDepth) (X).b groupSame
          (Prod.ext vertexSame residue)))
      | inr b=>cases kindSame
    | inr a=>
      cases b with
      | inl b=>cases kindSame
      | inr b=>
        have label:=Sum.inr.inj kindSame
        have names : shortName T.commonDepth (T.code a)=shortName T.commonDepth (T.code b) :=
          Prod.ext vertexSame (congrArg (fun z : Code r × Option (Fin Y) => (z.1.val,z.2)) label)
        exact congrArg Sum.inr (T.code.injective (relative_injective (k:=T.commonDepth) («r»:=0) (T.codeLegal a).1
          (T.codeLegal b).1 groupSame names))

def atRoot {H : ℕ} (vertex : Z.V↪Fin H) (position : Fin H×DescentColonies.Block T.commonDepth×RootTicket Z T) :
    Option (X).Site :=
  if found : ∃q,rootLocation Z T vertex q=position then some found.choose else none

theorem root_at {H : ℕ} (vertex : Z.V↪Fin H) (g : (X).Site) : atRoot Z T vertex (rootLocation Z T vertex g)=some g := by
  let ready : ∃q,rootLocation Z T vertex q=rootLocation Z T vertex g:=⟨g,rfl⟩
  rw [atRoot,dite_eq_left ready,(rootLocation Z T vertex).injective ready.choose_spec]

theorem empty_at {H : ℕ} (vertex : Z.V↪Fin H) (position : Fin H×DescentColonies.Block T.commonDepth×RootTicket Z T) :
    atRoot Z T vertex position=none ↔ ∀q,rootLocation Z T vertex q≠position := by
  unfold atRoot
  split
  next found =>
    constructor
    · intro e; cases e
    · intro miss; exact False.elim ((miss found.choose) found.choose_spec)
  next missing =>
    exact ⟨fun _ q h => missing ⟨q,h⟩,fun _ => rfl⟩

/-- Each pass fixes only a relative root role. Its two physical array axes are exactly the
old vertex and the coarse group. Per-host names never enter a private cell. -/
def rootsOf {H count : ℕ} (vertex : Z.V↪Fin H) (unit : 0<Z.unit) (s : Bool)
    (arrivals : Z.Fallback→Panel Ht count) (ticket : RootTicket Z T) :
    Fin H→DescentColonies.Block T.commonDepth→Key (n:=Z.n) r Ht count (layerBits Z) := fun u j=>
  match atRoot Z T vertex (u,j,ticket) with
  | none=>none
  | some (.inl g)=>rotorKey Z T unit count s g
  | some (.inr t)=>fallbackKey Z T s t (arrivals t)

theorem rootsOf_read {H count : ℕ} (vertex : Z.V↪Fin H) (unit : 0<Z.unit) (s : Bool)
    (arrivals : Z.Fallback→Panel Ht count) (g : (X).Site) :
    rootsOf Z T vertex unit s arrivals (rootTicket Z T g) (vertex (rootVertex Z T g)) (rootBlock Z T g)=
      (match g with | .inl g=>rotorKey Z T unit count s g | .inr t=>fallbackKey Z T s t (arrivals t)) := by
  unfold rootsOf
  rw [show (vertex (rootVertex Z T g),rootBlock Z T g,rootTicket Z T g)=rootLocation Z T vertex g from rfl,root_at]
  cases g <;> rfl

end
end Hierarchy.DescentSixParty.ResetInput

end OAI

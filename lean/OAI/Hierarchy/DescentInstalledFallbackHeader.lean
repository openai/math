import OAI.Hierarchy.DescentResetPaletteCode
import OAI.Hierarchy.DescentInstalledRotorHeader

namespace OAI
/-! # Physical endpoint fields of both reset device families in the absolute sparse parent archive -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentChosenRouter DescentCommonHost DescentResetHostSize DescentRelativeContacts
open DescentDenseHostOrder DescentResetPaletteCode DescentHostDirectory DescentRouterSlots DescentMixedRouter
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "P₀" => Z.placement
local notation "Q" => DescentCommonPalette.rotor Z.graph
local notation "same" => funext (fun e=>(Z.allWidths e).symm)
local notation "wires" => installedWireNames A T.home (P₀).input T.hub same Z.bank Z.tables
local notation "sel" => selected (P₀) Z.graph Z.positive Z.pay Z.circuit
local notation "dev" => DescentMixedRouter.device Z.graph Z.positive Z.unit (P₀).contact (P₀).input (P₀).site (P₀).owner (P₀).align (D:=d)
local notation "r" => Z.k-T.commonDepth
local notation "m" => T.commonDepth

def rootVertex : (P₀).Site→Z.V
  | .inl g=>g.val.1
  | .inr t=>(T.code t).1

def goodLabel (g : (P₀).Good) : Code r :=
  ⟨((P₀).b g.val.1-m,g.val.2.val%2^((P₀).b g.val.1-m)),
    mem_codes (Nat.sub_le_sub_right ((P₀).depth _) m) (Nat.mod_lt _ (Nat.two_pow_pos _))⟩

def fallLabel (t : Z.Fallback) : Code r :=
  ⟨(shortName m (T.code t)).2.1,mem_codes (Nat.sub_le_sub_right (T.codeLegal t).2.1 m)
    (Nat.mod_lt _ (Nat.two_pow_pos _))⟩

def privateLocal (s : Bool) : (g : (P₀).Site)→(dev (sel s g)).Site→Local Z.graph r Ht
  | .inl g,v=>
    let layers := DescentChosenRouter.selectedRotorLayers (P₀) Z.graph Z.positive Z.pay Z.circuit s g
    (s,goodLabel Z T g,.inl ((DescentCommonPalette.rotorSiteEquiv Z.graph d layers C Z.width Z.unit).symm v))
  | .inr t,v=>(s,fallLabel Z T t,.inr ((T.code t).2.2,raiseTree (T.bookHeight s t) v))

def privateSiteAt (s : Bool) (g : (P₀).Site) (v : (dev (sel s g)).Site) : (W).graph.Site :=
  (resetNames Z T).symm (.inr ⟨(s,g),v⟩)

def privateWireAt (s : Bool) (g : (P₀).Site) (e : (dev (sel s g)).Edge) : (W).graph.Edge :=
  (wires).symm (.inr (.inr (.inr ⟨(s,g),e⟩)))

theorem local_rom_host {H : ℕ} (vertex : Z.V↪Fin H) (s : Bool) (g : (P₀).Site) (v : (dev (sel s g)).Site) :
    (rawHostRank Z T vertex (placed Z T (privateSiteAt Z T s g v))).val=
      rom Z.graph r Ht (ordinal Z.graph r Ht (privateLocal Z T s g v)).val+
      (roster Z.graph r Ht).card*(vertex (rootVertex Z T g)).val := by
  rw [rawHostRank_read,rom_read]
  have siteName : commonName Z T (privateSiteAt Z T s g v) =
      bankNode (P₀) Z.graph m T.code Z.positive Z.pay Z.circuit d ⟨(s,g),v⟩ :=
    congrArg (rawName (P₀) Z.graph m T.code Z.positive Z.pay Z.circuit d)
      ((resetNames Z T).apply_symm_apply (.inr ⟨(s,g),v⟩))
  have shapeEq : localShape Z T (placed Z T (privateSiteAt Z T s g v))=
      member Z.graph r Ht (privateLocal Z T s g v) := by
    apply Subtype.ext
    change shape Z.graph (commonName Z T (privateSiteAt Z T s g v))=_
    rw [siteName]
    cases g <;> rfl
  have posEq : position Z.graph (commonName Z T (privateSiteAt Z T s g v))=rootVertex Z T g := by
    rw [siteName]
    cases g <;> rfl
  change (localRank Z.graph r Ht (localShape Z T _)).val+
    (roster Z.graph r Ht).card*(vertex (position Z.graph (commonName Z T _))).val=_
  rw [shapeEq,posEq]

theorem private_geometry (s : Bool) (g : (P₀).Site) (e : (dev (sel s g)).Edge) :
    physicalFields A T.home (P₀).input T.hub same Z.bank Z.tables (privateWireAt Z T s g e)=
      ⟨.inr ⟨(s,g),(dev (sel s g)).src e⟩,.inr ⟨(s,g),(dev (sel s g)).dst e⟩,(dev (sel s g)).width e,true⟩ := by
  let name : (Bool × A.graph.Edge) ⊕ (Z.Fallback ⊕ Z.bank.Edge) := .inr (.inr (.inr ⟨(s,g),e⟩))
  exact (sourceFields_read A T.home (P₀).input T.hub same Z.bank Z.tables ((wires).symm name)).trans
    (congrArg (sourceFields A T.home (P₀).input T.hub Z.bank) ((wires).apply_symm_apply name))

theorem private_block (s : Bool) (g : (P₀).Site) (v : (dev (sel s g)).Site) :
    (blockId Z T (privateSiteAt Z T s g v)).val=(P₀).siteGroup m T.code g := by
  exact congrArg (rawCoordinate (P₀) Z.graph m T.code Z.positive Z.pay Z.circuit d)
    ((resetNames Z T).apply_symm_apply (.inr ⟨(s,g),v⟩))

variable {H L : ℕ} (vertex : Z.V↪Fin H) (key : A.graph.Edge↪Fin L)
def privateHost (s : Bool) (g : (P₀).Site) (v : (dev (sel s g)).Site) : ℕ :=
  rom Z.graph r Ht (ordinal Z.graph r Ht (privateLocal Z T s g v)).val+
    (roster Z.graph r Ht).card*(vertex (rootVertex Z T g)).val

/-- Both endpoint name rows and both blocks come from the same actual group. No ordinal of the
moving site type enters the palette lookup. The ROM is shared by all groups and all placements. -/
theorem privateArchive (s : Bool) (g : (P₀).Site) (e : (dev (sel s g)).Edge) :
    let wire:=privateWireAt Z T s g e
    let lo:=(W).graph.src wire
    let hi:=(W).graph.dst wire
    ((installedResetOrdinal Z T vertex key wire).val,
      (rawHostRank Z T vertex (placed Z T lo)).val,(rawHostRank Z T vertex (placed Z T hi)).val,
      (blockId Z T lo).val,(blockId Z T hi).val,(W).graph.width wire,decide (wire∈(W).core))=
      ((DescentResetCableSlots.complete (P₀) vertex T.code (fun t=>(T.codeLegal t).2) Ht T.bookHeight
        Z.graph Z.positive Z.pay Z.circuit d key (.inr (.inr (.inr ⟨(s,g),e⟩)))).val,
       privateHost Z T vertex s g ((dev (sel s g)).src e),privateHost Z T vertex s g ((dev (sel s g)).dst e),
       (P₀).siteGroup m T.code g,(P₀).siteGroup m T.code g,(dev (sel s g)).width e,true) := by
  let wire:=privateWireAt Z T s g e
  have raw:=private_geometry Z T s g e
  have sc : (W).graph.src wire=privateSiteAt Z T s g ((dev (sel s g)).src e) :=
    (Equiv.eq_symm_apply _).2 (congrArg RawFields.src raw)
  have tc : (W).graph.dst wire=privateSiteAt Z T s g ((dev (sel s g)).dst e) :=
    (Equiv.eq_symm_apply _).2 (congrArg RawFields.dst raw)
  have width : (W).graph.width wire=(dev (sel s g)).width e := congrArg RawFields.width raw
  have core : decide (wire∈(W).core)=true := congrArg RawFields.core raw
  dsimp only
  change ((installedResetOrdinal Z T vertex key wire).val,_,_,_,_,(W).graph.width wire,decide (wire∈(W).core))=_
  rw [sc,tc,width,core,local_rom_host,local_rom_host,private_block,private_block]
  change ((DescentResetCableSlots.complete _ _ _ _ _ _ _ _ _ _ _ _ ((wires) ((wires).symm _))).val,_) = _
  rw [Equiv.apply_symm_apply]
  rfl

def privateRecord (s : Bool) (g : (P₀).Site) (e : (dev (sel s g)).Edge) : Fin 7→ℕ :=
  ![1,privateHost Z T vertex s g ((dev (sel s g)).src e),privateHost Z T vertex s g ((dev (sel s g)).dst e),
    (P₀).siteGroup T.commonDepth T.code g,(P₀).siteGroup T.commonDepth T.code g,(dev (sel s g)).width e,1]

def actualRecord (e : (W).graph.Edge) : Fin 7→ℕ :=
  ![1,(rawHostRank Z T vertex (placed Z T ((W).graph.src e))).val,
    (rawHostRank Z T vertex (placed Z T ((W).graph.dst e))).val,
    (blockId Z T ((W).graph.src e)).val,(blockId Z T ((W).graph.dst e)).val,(W).graph.width e,if e∈(W).core then 1 else 0]

theorem record_actual (s : Bool) (g : (P₀).Site) (e : (dev (sel s g)).Edge) :
    actualRecord Z T vertex (privateWireAt Z T s g e)=privateRecord Z T vertex s g e := by
  let wire:=privateWireAt Z T s g e
  have raw:=private_geometry Z T s g e
  have sc : (W).graph.src wire=privateSiteAt Z T s g ((dev (sel s g)).src e) :=
    (Equiv.eq_symm_apply _).2 (congrArg RawFields.src raw)
  have tc : (W).graph.dst wire=privateSiteAt Z T s g ((dev (sel s g)).dst e) :=
    (Equiv.eq_symm_apply _).2 (congrArg RawFields.dst raw)
  have hw : (W).graph.width wire=(dev (sel s g)).width e := congrArg RawFields.width raw
  have hc : wire∈(W).core := of_decide_eq_true (congrArg RawFields.core raw)
  funext j
  change actualRecord Z T vertex wire j=_
  simp [actualRecord,privateRecord,sc,tc,hw,hc,local_rom_host,privateHost,private_block]

end
end Hierarchy.DescentSixParty.ResetInput

end OAI

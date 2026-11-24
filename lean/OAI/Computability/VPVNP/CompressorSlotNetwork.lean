import OAI.Computability.VPVNP.CompressorSlotSchedule
import OAI.Computability.VPVNP.CompressorSlotOrder

/-!
# The selected shrinking layout in the RAM slot directory

Both ends of an actual arc have adjacent field identifiers. The low bit is
zero for the outgoing end and one for the incoming end. The real owner array
uses the same convention on absolute sites. The native row and inverse scans
therefore leave two direct tables from which the next substep can query its
incoming site and slot using its outgoing site and slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotSchedule

open Compression Compression.PackingData Compression.SurvivingSlots Slots BurstRAM

variable {V H Tag L : Type*} {d c N J nL pad : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- Direct mixed-radix index of one absolute site. -/
def siteIndex : Site V Tag L ≃ Fin (N*(J*nL)) :=
  (vertices.prodCongr ((tags.prodCongr lanes).trans finProdFinEquiv)).trans finProdFinEquiv

/-- Decode one candidate field by splitting off its side bit and using the
actual arc-address decoder. The owners are the two role endpoints of the
chosen layout, including the cyclic target of each padding arc. -/
def slotDirectory (layout : Bool) : Directory (ActualId P subdiv pad × Fin 2)
    (RecordCount N J nL d c pad subdiv * 2) ((N*(J*nL))*2) where
  address := endpointAddress (arcAddress P subdiv vertices tags lanes pad)
  decode := fun j ↦ let p := finProdFinEquiv.symm j
    (decodeArc P subdiv vertices tags lanes pad p.1).map fun i ↦ (i,p.2)
  decode_eq_some := by
    intro j ⟨i,s⟩
    obtain ⟨⟨a,b⟩,rfl⟩ := finProdFinEquiv.surjective j
    simp only [Equiv.symm_apply_apply]
    change _ ↔ finProdFinEquiv (arcAddress P subdiv vertices tags lanes pad i,s) = finProdFinEquiv (a,b)
    simp only [Option.map_eq_some_iff, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨x,h,rfl,rfl⟩; exact ⟨(decodeArc_eq_some _ _ _ _ _ _ _ _).mp h, rfl⟩
    · rintro ⟨h,rfl⟩; exact ⟨i, (decodeArc_eq_some _ _ _ _ _ _ _ _).mpr h, rfl, rfl⟩
  owner := fun ⟨i,s⟩ ↦ finProdFinEquiv (siteIndex vertices tags lanes
    (actualEnd P subdiv tags layout (decide (s=1)) i),s)

private theorem owner_iff (layout : Bool) (e : ActualId P subdiv pad × Fin 2) (s : Site V Tag L) (b : Fin 2) :
    (slotDirectory P subdiv vertices tags lanes layout).owner e = finProdFinEquiv (siteIndex vertices tags lanes s,b) ↔
      actualEnd P subdiv tags layout (decide (e.2=1)) e.1 = s ∧ e.2 = b := by
  simp only [slotDirectory, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]

private theorem field_lt (i j : ActualId P subdiv pad) (side : Fin 2) :
    endpointAddress (arcAddress P subdiv vertices tags lanes pad) (i,side) <
        endpointAddress (arcAddress P subdiv vertices tags lanes pad) (j,side) ↔
      arcAddress P subdiv vertices tags lanes pad i < arcAddress P subdiv vertices tags lanes pad j := by
  change side.val + 2 * (arcAddress _ _ _ _ _ _ i).val < side.val + 2 * (arcAddress _ _ _ _ _ _ j).val ↔ _
  rw [Fin.lt_def]; omega

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- The two side arrays have exactly the common degree at each real owner. -/
theorem slotDirectory_degree (hc : 2 ≤ c) (layout : Bool) (b : Fin ((N*(J*nL))*2)) :
    Fintype.card {e // (slotDirectory P subdiv vertices tags lanes layout (pad := pad)).owner e = b} =
      survivingDegree d c subdiv + pad := by
  obtain ⟨⟨v,side⟩,rfl⟩ := finProdFinEquiv.surjective b
  obtain ⟨s,rfl⟩ := (siteIndex vertices tags lanes).surjective v
  let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad)
  let t := finProdFinEquiv (siteIndex vertices tags lanes s,side)
  let eqv : {e // D.owner e = t} ≃ {i // actualEnd P subdiv tags layout (decide (side=1)) i = s} := {
    toFun e := ⟨e.val.1, by
      obtain ⟨h, hs⟩ := (owner_iff P subdiv vertices tags lanes layout e.val s side).mp e.prop
      simpa only [hs] using h⟩
    invFun i := ⟨(i.val,side), (owner_iff P subdiv vertices tags lanes layout _ _ _).mpr ⟨i.prop,rfl⟩⟩
    left_inv e := Subtype.ext (Prod.ext rfl ((owner_iff P subdiv vertices tags lanes layout e.val s side).mp e.prop).2.symm)
    right_inv _ := rfl }
  exact (Fintype.card_congr eqv).trans (actualEnd_card P subdiv tags hc layout (decide (side=1)) s)

private theorem field_rank (layout : Bool) (i : ActualId P subdiv pad) (side : Fin 2) :
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad)
    Fintype.card {x // D.owner x = D.owner (i,side) ∧ D.address x < D.address (i,side)} =
      addressRank P subdiv vertices tags lanes layout (decide (side=1)) i := by
  intro D
  let s := actualEnd P subdiv tags layout (decide (side=1)) i
  let eqv : {x // D.owner x = D.owner (i,side) ∧ D.address x < D.address (i,side)} ≃
      {j // actualEnd P subdiv tags layout (decide (side=1)) j = s ∧
        arcAddress P subdiv vertices tags lanes pad j < arcAddress P subdiv vertices tags lanes pad i} := {
    toFun x := ⟨x.val.1, by
      rcases x with ⟨⟨j,t⟩, hx, hlt⟩
      obtain ⟨he, ht⟩ := (owner_iff P subdiv vertices tags lanes layout (j,t) s side).mp hx
      change t = side at ht; subst t
      exact ⟨he, (field_lt P subdiv vertices tags lanes j i side).mp hlt⟩⟩
    invFun x := ⟨(x.val,side), (owner_iff P subdiv vertices tags lanes layout _ _ _).mpr ⟨x.prop.1,rfl⟩,
      (field_lt P subdiv vertices tags lanes _ _ _).mpr x.prop.2⟩
    left_inv x := by
      rcases x with ⟨⟨j,t⟩, hx, hlt⟩
      have ht : t = side := ((owner_iff P subdiv vertices tags lanes layout _ s side).mp hx).2
      subst t; rfl
    right_inv _ := rfl }
  exact Fintype.card_congr eqv

variable [Module (ZMod 2) Tag]

/-- Every rectangular RAM index contains the regularized graph's prescribed
slot at the specified absolute endpoint, with the orientation bit retained. -/
theorem rectangular_slot (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout : Bool) {d' : ℕ} (hd : survivingDegree d c subdiv ≤ d') (hJ : 1 < J)
    (i : ActualId P subdiv (d' - survivingDegree d c subdiv)) (side : Fin 2) :
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := d' - survivingDegree d c subdiv)
    let hD := fun b ↦ (slotDirectory_degree P subdiv vertices tags lanes hc layout b).trans (Nat.add_sub_of_le hd)
    (sortedFields D d' hD (i,side)).val =
      ((if side=1 then I.incoming else I.outgoing) (paddedBaseId P subdiv i)).2.val + d'*(D.owner (i,side)).val := by
  intro order I D hD
  rw [sortedFields_val]
  congr 1
  rw [field_rank]
  simpa only [decide_eq_true_eq] using addressRank_eq_slot P subdiv vertices tags lanes hc hφ layout
    (decide (side=1)) hd hJ i

open BurstRAM.PrivateRAM PrimedStackRAM

/-- Starting with the rectangular outgoing slot, fetch its absolute field,
advance to the adjacent incoming field, and read the incoming rectangular slot. -/
def oppositeLookup : List (Op 3 2) :=
  [.stateWord 0, .publicWord 1 0, .binary .add 1 1 0, .read 2 1,
    .constant 1 1, .binary .add 2 2 1, .publicWord 1 1, .binary .add 2 1 2, .read 2 2]

theorem oppositeLookup_native {w : ℕ} (p : Fin 2 → Word w) (m : Memory w) (idx : Word w) :
    let M := (template oppositeLookup 2).instantiate w p
    let ptr := p 0 + idx
    let field := m ptr.val
    let inv := p 1 + (field + 1)
    let target := m inv.val
    ∃ es, execute M.program 10 (M.program.start idx) m [] = some ⟨es, some target⟩ ∧
      after m es = m ∧ es.length = 9 ∧ countProbes es = 2 := by
  intro M ptr field inv target
  refine ⟨[.tick,.tick,.tick,.read ptr field,.tick,.tick,.tick,.tick,.read inv target], ?_, rfl, rfl, rfl⟩
  change execute M.program (1 + oppositeLookup.length) ⟨_,idx,fun _ => 0, fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace]; rfl

omit [Module (ZMod 2) Tag] [DecidableEq V] [DecidableEq Tag] [DecidableEq L] in
/-- The two native reads on any occupied outgoing slot return the incoming
slot of the same arc. The numbers used here are the paper's slot numbers by
`rectangular_slot`. Lane zero can use the destination site to read off the
remaining-lane displacement; the other lanes use the same matching. -/
theorem lookup_from_tables {w rows inverse : ℕ} (layout : Bool) (i : ActualId P subdiv pad)
    {deg : ℕ} (hc : ∀ b, Fintype.card {e // (slotDirectory P subdiv vertices tags lanes layout (pad := pad)).owner e = b} = deg)
    (m : Memory w) (tab : Tables (slotDirectory P subdiv vertices tags lanes layout) deg rows inverse hc m)
    (p : Fin 2 → Word w) (hrow : (p 0).val = rows) (hinv : (p 1).val = inverse)
    (hrows : rows + ((N*(J*nL))*2)*deg ≤ 2^w)
    (hfields : inverse + RecordCount N J nL d c pad subdiv*2 ≤ 2^w) :
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad)
    let src := Fin.ofNat (2^w) (sortedFields D deg hc (i,0)).val
    let dst := Fin.ofNat (2^w) (sortedFields D deg hc (i,1)).val
    let M := (template oppositeLookup 2).instantiate w p
    ∃ es, execute M.program 10 (M.program.start src) m [] = some ⟨es, some dst⟩ ∧
      after m es = m ∧ es.length = 9 ∧ countProbes es = 2 := by
  intro D src dst M
  let a := D.address (i,0)
  let b := D.address (i,1)
  have hab : a.val+1 = b.val := by
    change 0 + 2 * (arcAddress P subdiv vertices tags lanes pad i).val + 1 =
      1 + 2 * (arcAddress P subdiv vertices tags lanes pad i).val
    omega
  have hs : (p 0 + src).val = rows + (sortedFields D deg hc (i,0)).val := by
    have h := (sortedFields D deg hc (i,0)).isLt
    rw [Fin.val_add, hrow, show src.val = _ from Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have ha : m (p 0 + src).val = Fin.ofNat (2^w) a.val := by rw [hs]; exact tab.bySlot (i,0)
  have hb : (p 1 + (m (p 0 + src).val + 1)).val = inverse + b.val := by
    have fit : b.val < RecordCount N J nL d c pad subdiv * 2 := b.isLt
    have bfit : b.val < 2^w := by omega
    have total : inverse+b.val < 2^w := by omega
    rw [ha, Fin.val_add, hinv, Fin.val_add, Fin.val_ofNat, Fin.val_one',
      Nat.mod_eq_of_lt (show a.val < 2^w by omega), Nat.mod_eq_of_lt (show 1 < 2^w by omega),
      hab, Nat.mod_eq_of_lt bfit, Nat.mod_eq_of_lt total]
  have hr : m (p 1 + (m (p 0 + src).val + 1)).val = dst := by rw [hb]; exact tab.byField (i,1)
  simpa only [hr] using oppositeLookup_native p m src

end CompressorRecords.SlotSchedule

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.CompressorRecordsShrinkHistory
import OAI.Computability.VPVNP.PairNodeArguments

/-!
# Private fields for absorbed edges in a shrinking pass

Each absorbed edge receives one slot indexed by its dense motif and role
ordinal. The local history scans the restricted list of owners. The source
and target maps at that owner use the same private field.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkHiddenSlots

open BurstRAM CompressorRecords ShrinkHistoryRows Compression LocalHistory
open scoped Classical Fin.CommRing

variable {a g w : ℕ} (X : State a (packingLaneBits a g))

/-- The identifier carried by a row of the hidden owner directory. -/
def id (e : X.packingData.Motif × Fin 4) : ℕ := ((hiddenOrder X).entries.symm e).val

theorem id_eq (m : X.packingData.Motif) (t : Fin 4) :
    id X (m,t) = (ShrinkMotifOrder.stateNumber X m).val * 4 + t.val := by
  change t.val + 4 * (ShrinkMotifOrder.stateNumber X m).val = _
  omega

theorem id_injective : Function.Injective (id X) :=
  Fin.val_injective.comp (hiddenOrder X).entries.symm.injective

/-- The base of a private bit field, shared between its two map incidences. -/
def address (base stride : ℕ) (e : X.packingData.Motif × Fin 4) : ℕ := base + id X e * stride

set_option maxHeartbeats 1500000 in
/-- Each entry in the native local row contains its full dense identifier. -/
theorem directory_id (layout : Bool) (p : Fin 6 → Word w) (mem : Memory w)
    (dir : Directory (hiddenOrder X) (packedOrder X) (X.packingData.shrinkInternalOwner layout) p mem)
    (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)
    (j : Fin (residents (hiddenOrder X) (X.packingData.shrinkInternalOwner layout) v).length) :
    let e := ((residents (hiddenOrder X) (X.packingData.shrinkInternalOwner layout) v).entries j).val
    mem ((p 5).val + ((packedOrder X).entries.symm v).val * (p 4).val + j.val) = (id X e : Word w) :=
  dir.idAt v j

variable (base stride : ℕ) {e e' : X.packingData.Motif × Fin 4}

theorem addresses_disjoint (hne : e ≠ e') :
    address X base stride e + stride ≤ address X base stride e' ∨
    address X base stride e' + stride ≤ address X base stride e :=
  NodeArguments.Arena.disjoint ⟨base, stride⟩ (fun h => hne (id_injective X h))

theorem store_read (bits : List Bool) (old : Word w → Word w)
    (fit : address X base stride e + bits.length ≤ 2 ^ w) (i : Fin bits.length) :
    PrivateFields.storeBits (address X base stride e) bits old
      ((address X base stride e + i.val : ℕ) : Word w) = PrivateFields.bitValue w bits[i.val] :=
  PrivateFields.storeBits_read _ _ _ fit i

/-- Writing a resident field preserves every bit of any other slot. -/
theorem store_other (hne : e ≠ e') (bits : List Bool) (old : Word w → Word w)
    (size : bits.length ≤ stride) (i : Fin stride)
    (fit : address X base stride e + bits.length ≤ 2 ^ w)
    (readFit : address X base stride e' + i.val < 2 ^ w) :
    let cell : Word w := (address X base stride e' + i.val : ℕ)
    PrivateFields.storeBits (address X base stride e) bits old cell = old cell := by
  intro cell
  apply PrivateFields.storeBits_outside _ _ _ cell fit
  have val : cell.val = address X base stride e' + i.val := Nat.mod_eq_of_lt readFit
  rw [val]
  rcases addresses_disjoint X base stride hne with before | after <;> omega

section Incidences

open NetworkKernel PackingData ShrinkMotif
open private readSupplyEnd layoutCases_absorbed from OAI.Computability.VPVNP.ShrinkSupplyLocal

variable {b pad : ℕ} (layout : Bool) (subdiv : Fin 4 → ℕ)
variable (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
variable {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
variable (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad) (hpos : ∀ t, 0 < subdiv t)
local notation "Y" => X.packingData.shrinkOutput layout subdiv (fun m t ↦ widths m (layout,t)) I

/-- The party reading an absorbed edge at the indicated end. -/
def party (layout : Bool) (t : Fin 4) : Bool → Fin 6
  | false => supply.src (!layout,t)
  | true => supply.dst (!layout,t)

theorem party_owner (m : X.packingData.Motif) (t : Fin 4) (dir : Bool) :
    X.packingData.shrinkPartySite layout m (party layout t dir) =
      X.packingData.shrinkInternalOwner layout (m,t) := by
  cases dir <;> simp only [shrinkPartySite, party, shrinkInternalOwner, role_src_absorbed, role_dst_absorbed]

variable (m : X.packingData.Motif) (t : Fin 4)
local notation "owner" => X.packingData.shrinkInternalOwner layout (m,t)
local notation "Labels" => internalLabel widths layout

/-- Select the absorbed column from the actual local supply argument.
Both ends use the hidden assignment at their common packed site. -/
def mapColumn (dir : Bool) (h : Placed (X.packingData.shrinkInternalOwner layout) Labels owner)
    (z : (Y).Half owner) : Labels (m,t) :=
  match dir with
  | false => (X.packingData.shrinkLocalSupplyArg layout subdiv widths I hpos m _
      ((party_owner X layout m t false).symm ▸ h) ((party_owner X layout m t false).symm ▸ z)).1 (!layout,t) rfl
  | true => (X.packingData.shrinkLocalSupplyArg layout subdiv widths I hpos m _
      ((party_owner X layout m t true).symm ▸ h) ((party_owner X layout m t true).symm ▸ z)).2 (!layout,t) rfl

private theorem placed_cast {U V : Type} {P : U → V} {F : U → Type} {v v' : V}
    (eqn : v = v') (h : Placed P F v') (e : U) (he : v = P e) :
    (eqn.symm ▸ h : Placed P F v) e he = h e (eqn.symm.trans he) := by
  cases eqn
  rfl

theorem mapColumn_eq (dir : Bool) (h : Placed (X.packingData.shrinkInternalOwner layout) Labels owner)
    (z : (Y).Half owner) : mapColumn X layout subdiv widths I hpos m t dir h z = h (m,t) rfl := by
  cases dir <;> simp only [mapColumn, shrinkLocalSupplyArg, readSupplyEnd, layoutCases_absorbed]
  exact placed_cast (party_owner X layout m t true) h (m,t) _

/-- A shared private slot gives the coordinate of either incident map column.
The half-wire argument is arbitrary, including unrelated assignments to the
source and target party's surviving fields. -/
theorem mapColumn_read (dir : Bool) (h : Placed (X.packingData.shrinkInternalOwner layout) Labels owner)
    (z : (Y).Half owner) (priv : Word w → Word w)
    (stored : ∀ j, priv ((address X base stride (m,t) + j.val : ℕ) : Word w) =
      PrivateFields.bitValue w (RAMSerialization.wordBits _ (h (m,t) rfl) j))
    (i : Fin (widths m (!layout,t))) :
    priv ((address X base stride (m,t) + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (RAMSerialization.wordBits _
        (mapColumn X layout subdiv widths I hpos m t dir h z) i) := by
  rw [mapColumn_eq]
  exact stored i

end Incidences

end PairSimulation.ShrinkHiddenSlots

end

end VPVNP
end Computability
end OAI

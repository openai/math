import OAI.Hierarchy.TaggedWideFrozenSlots
import OAI.Hierarchy.TaggedWideFrozenSeries
import OAI.Hierarchy.TaggedWideActivePlacement
import OAI.Hierarchy.TaggedWideLeafBanks

namespace OAI
/-! # The native widths and scatter fields of the original positive rows -/

noncomputable section
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing
open ProtocolRAM ProtocolRAMReportedPorts Tagged.WideStack TaggedShorterGroups
open scoped Classical Fin.CommRing
set_option quotPrecheck false

private theorem contents_transport {G : Type} [Fintype G] {D B M n : ℕ}
    (c c' : G→ℕ) (same : ∀g,c' g=c g) (bc : ∀g,c g≤D) (bc' : ∀g,c' g≤D)
    (hb : 0<B) (hw : B≤2^n) (pl : ∀g:G,Bool→Fin (c g)↪Fin D)
    (q : TaggedShorterScatter.Field (capacity G D B M) D) :
    TaggedShorterScatter.contents c' bc' hb hw
      (fun g b=>(finCongr (same g)).toEmbedding.trans (pl g b)) q =
      TaggedShorterScatter.contents c bc hb hw pl q := by
  have eqn : c'=c := funext same
  subst c'
  have fixed : (fun g b=>(finCongr (same g)).toEmbedding.trans (pl g b))=pl := by
    funext g b
    apply Function.Embedding.ext
    intro i
    rfl
  rw [fixed]

variable {F : Type*} [Field F] {W : ℕ} (s : Format) (ports lanes : ℕ)
variable (a : Inputs) (old : Fin (s.withSlots ports lanes).N→ProtocolRAMEmit.Row) (before : Memory W)
    (fit : (s.withSlots ports lanes).Limits W old)
    (ins : Leaf.Installed F (s.withSlots ports lanes).groups ports lanes (s.withSlots ports lanes).w (s.withSlots ports lanes).menu (s.withSlots ports lanes).γ old)
variable (active : ∀i,0<pieces old (s.withSlots ports lanes).w i → (a.directory.read before (a.owner.eval before (i.val:Word W))).val=(old i).group)
    (owner : ∀i,0<pieces old (s.withSlots ports lanes).w i → (old i).group<(s.withSlots ports lanes).groups)
    (slots : ∀b (i : ProtocolRAMPackedPlacement.Live old (s.withSlots ports lanes).w),(s.withSlots ports lanes).starts a before b i.val=(ins.port b i.val).val*lanes)
local notation "f" => s.withSlots ports lanes
local notation "group" => fun i : Fin (s.withSlots ports lanes).N=>(a.directory.read before (a.owner.eval before (i.val:Word W))).val
local notation "countEq" g:arg => regroup_count old group (f).w (f).menu (f).γ (Fin.val g) active

include ins active owner slots in
/-- The common ordinal of any live source is unchanged when the directory returns
a different group for an unused row. The output place is the purchased physical socket. -/
def Format.originalAnchor : (f).Anchored a before old fit where
  groupFit := by
    intro i live
    exact (active i live).trans_lt (owner i live)
  bound := by
    intro g
    change count (regroup old group) (f).w (f).menu (f).γ g.val ≤ (f).D
    rw [countEq g]
    exact ins.bank.bound g
  pl := fun g b=>(finCongr (countEq g)).toEmbedding.trans (ins.bank.place g b)
  located := by
    intro b g u
    let e := regroup_units old group (f).w (f).menu (f).γ g.val active
    obtain ⟨v,rfl⟩ := e.surjective u
    have rank := regroup_common old group (f).w (f).menu (f).γ g.val active ins.unique v
    change (ins.bank.place g b (Fin.cast (countEq g)
      (common (regroup old group) (f).w (f).menu (f).γ g.val fit.order.injective (e v)))).val =
      (f).starts a before b v.1.val + v.2.val
    rw [←rank]
    change ((staticUnit old g ins.port (ins.distinct g) ins.room le_rfl b)
      ((common old (f).w (f).menu (f).γ g.val ins.unique).symm
        (common old (f).w (f).menu (f).γ g.val ins.unique v))).val=_
    rw [Equiv.symm_apply_apply]
    rcases v with ⟨i,j⟩
    let live : ProtocolRAMPackedPlacement.Live old (f).w := ⟨i.val,Nat.zero_lt_of_lt j.isLt⟩
    change j.val+lanes*(ins.port b live.val).val=(f).starts a before b live.val+j.val
    rw [slots b live,Nat.mul_comm lanes,Nat.add_comm]

theorem Format.originalAnchor_field (q : TaggedShorterScatter.Field (f).window.C (f).D) :
    (s.originalAnchor ports lanes a old before fit ins active owner slots).word old (.inr q) =
      (TaggedShorterScatter.contents ins.bank.counts ins.bank.bound fit.batch fit.idFits ins.bank.place q : Word W) := by
  apply congrArg (fun n:ℕ=>(n:Word W))
  exact contents_transport ins.bank.counts _ (fun g=>countEq g) _ _ fit.batch fit.idFits ins.bank.place q

private theorem slotValue_transport {groups D : ℕ} (c c' : Fin groups → ℕ)
    (same : ∀g,c' g=c g) (pl : ∀g,Bool → Fin (c g) ↪ Fin D)
    (bits : TaggedShorterSlotWidth.Transport c → ℕ)
    (bits' : TaggedShorterSlotWidth.Transport c' → ℕ)
    (agree : ∀(g : Fin groups) (i : Fin (c' g)),bits' ⟨g,i⟩=bits ⟨g,Fin.cast (same g) i⟩)
    (x : TaggedShorterSlotWidth.Slot groups D) :
    TaggedShorterSlotWidth.value (fun g b=>(finCongr (same g)).toEmbedding.trans (pl g b)) bits' x =
      TaggedShorterSlotWidth.value pl bits x := by
  have equality : c'=c := funext same
  subst c'
  have fixed : (fun g b=>(finCongr (same g)).toEmbedding.trans (pl g b))=pl := by
    funext g b
    apply Function.Embedding.ext
    intro i
    rfl
  have widths : bits'=bits := by
    funext u
    rcases u with ⟨g,i⟩
    exact agree g i
  rw [fixed,widths]

/-- The native width port holds the original row's width at every occupied slot
and zero at every unoccupied slot, with the same public permutation of the pieces. -/
theorem Format.originalAnchor_width (x : TaggedShorterSlotWidth.Slot (f).groups (f).D) :
    (s.originalAnchor ports lanes a old before fit ins active owner slots).word old (.inl x) =
      (TaggedShorterSlotWidth.value ins.bank.place
        (TaggedShorterSlotWidth.reportWidth old (f).w (f).menu (f).γ ins.unique) x : Word W) := by
  apply congrArg (fun n : ℕ => (n : Word W))
  apply slotValue_transport ins.bank.counts _ (fun g=>countEq g) ins.bank.place
  intro g i
  let j := Fin.cast (countEq g) i
  have castBack : Fin.cast (countEq g).symm j=i := Fin.ext rfl
  have ranks := regroup_common_symm old group (f).w (f).menu (f).γ g.val active ins.unique j
  rw [castBack] at ranks
  change ((regroup old group) ((common (regroup old group) (f).w (f).menu (f).γ g.val
    ins.unique).symm i).1.val).width =
      (old ((common old (f).w (f).menu (f).γ g.val ins.unique).symm j).1.val).width
  rw [ranks]
  rfl

private theorem slotValue_lt {groups D bound : ℕ} {c : Fin groups → ℕ}
    (pl : ∀g, Bool → Fin (c g) ↪ Fin D) (bits : TaggedShorterSlotWidth.Transport c → ℕ)
    (positive : 0 < bound) (fits : ∀u, bits u < bound)
    (x : TaggedShorterSlotWidth.Slot groups D) : TaggedShorterSlotWidth.value pl bits x < bound := by
  obtain ⟨g,b,slot⟩ := x
  by_cases hit : slot ∈ Set.range (pl g b)
  · obtain ⟨i,rfl⟩ := hit
    exact (TaggedShorterSlotWidth.value_live pl bits (⟨g,i⟩ : TaggedShorterSlotWidth.Transport c) b).trans_lt (fits ⟨g,i⟩)
  · exact (TaggedShorterSlotWidth.value_blank pl bits (g,b,slot) hit).trans_lt positive

/-- The occupied row fits the native word by the original format limits. -/
theorem Format.originalAnchor_width_val (x : TaggedShorterSlotWidth.Slot (f).groups (f).D) :
    ((s.originalAnchor ports lanes a old before fit ins active owner slots).word old (.inl x)).val =
      TaggedShorterSlotWidth.value ins.bank.place
        (TaggedShorterSlotWidth.reportWidth old (f).w (f).menu (f).γ ins.unique) x := by
  rw [s.originalAnchor_width ports lanes a old before fit ins active owner slots x]
  apply Fin.val_cast_of_lt
  exact slotValue_lt (groups:=(f).groups) (D:=(f).D) ins.bank.place
    (TaggedShorterSlotWidth.reportWidth old (f).w (f).menu (f).γ ins.unique)
    (Nat.two_pow_pos _) (fun u =>
      (fit.widthFit (((common old (f).w (f).menu (f).γ u.1.val ins.unique).symm u.2).1.val)).trans_le fit.wide) x

end Hierarchy.ProtocolRAMFrozenWindow
end

end OAI

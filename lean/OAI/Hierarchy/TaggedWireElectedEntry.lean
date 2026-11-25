import OAI.Hierarchy.TaggedWireElectedTender
import OAI.Hierarchy.TaggedWidePacketAway

namespace OAI
/-! # The signed site operator of a physically elected calendar row -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open ProtocolRAM Calendar PurchaseStage ChosenPackets Probe Tagged AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing

namespace ChosenPackets.RowRouting
variable {F : Type} [Field F] {S N t H r : ℕ} (P : Placed F S) {phys : Fin N→Chord S}
    (letters : H=P.data.terms) (copies : r=t) (T : RowRouting (Row.packet P t) phys)

theorem retyped_entry (c : Histogram (Fin H) r) :
    let T':=retyped P letters copies T
    let c':=cast (congrArg₂ (fun alphabet amount => Histogram (Fin alphabet) amount) letters copies) c
    ∃ (input : (Row.retype P letters r).input=(Row.packet P t).input) (output : T'.post c=T.post c'),
      T'.entry c=Installs.transport input.symm output.symm (T.entry c') := by
  subst H r
  exact ⟨rfl,rfl,rfl⟩

theorem dormant_site (phys : Fin N→Chord S) (letters : ℕ) (mass : r=0)
    (c : Histogram (Fin letters) r) (s : Fin S) :
    let R:=dormant (F:=F) phys letters mass
    Subsingleton (State ((Row.passive (F:=F) (S:=S) letters mass).input) s) ∧ Subsingleton (State (R.post c) s) ∧
      ∀x y,R.entry c s x y=1 := by
  subst r
  have empty : (skipped (F:=F) phys letters).post c=0 := by
    ext q
    simp [post,skipped,Installs.load,installedWidths]
  exact ⟨Row.skip_state s,by rw [show (dormant (F:=F) phys letters rfl).post c=0 from empty];exact Row.skip_state s,
    skipped_away letters c⟩

/-- Eliminate the elected row and its routing together, so the entry's site types
remain indexed by the same physical row in each branch. -/
private theorem conditional_property {mass alphabet : ℕ} {p : Prop} [dp : Decidable p]
    {yes : p → Row F S alphabet mass} {no : (¬p) → Row F S alphabet mass}
    (on : ∀ h, RowRouting (yes h) phys) (off : ∀ h, RowRouting (no h) phys)
    (holds : ∀ row : Row F S alphabet mass, RowRouting row phys → Prop)
    (on_ok : ∀ h, holds (yes h) (on h)) (off_ok : ∀ h, holds (no h) (off h)) :
    let routed : RowRouting (if h : p then yes h else no h) phys := by
      cases dp with
      | isTrue h => exact on h
      | isFalse h => exact off h
    holds _ routed := by
  cases dp with
  | isTrue h => exact on_ok h
  | isFalse h => exact off_ok h

end ChosenPackets.RowRouting

namespace CalendarTape.HistogramFormat
variable {F X : Type} [Field F] {S N W q d : ℕ} {C : Chart W q d} (D : HistogramFormat C X)
    (a : Attempt) (x : X) (m : Memory W) (phys : Fin N→Chord S)
local notation "b" => enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)
local notation "snap" => HistogramShelf.snapshot C a m
local notation "I" => Fin (C.layout a).candidates
local notation "elected" => fun i:I=>(b).selected snap (i.val:Word W)

variable (view : D.observed a x m)
    (menu : ∀i : Fin (C.layout a).candidates,
      (enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)).selected
        (HistogramShelf.snapshot C a m) (i.val:Word W) → Placed F S)
    (arity : ∀i hi,(menu i hi).data.terms=
      ((enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)).termCount.read
        (HistogramShelf.snapshot C a m)
        ((enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)).packet.eval
          (HistogramShelf.snapshot C a m) (i.val:Word W))).val)
    (route : ∀i hi,RowRouting (Row.packet (menu i hi)
      (enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)).copies) phys)

private theorem elected_property (i : I)
    (holds : ∀ row : Row F S (D.letters a x i) (D.copies a x i), RowRouting row phys → Prop)
    (on_ok : ∀ hi : elected i, holds _ (RowRouting.retyped (menu i hi)
      ((view.1 i).trans (arity i hi).symm) ((view.2 i).trans (ite_eq_left hi)) (route i hi)))
    (off_ok : ∀ hi : ¬elected i, holds _ (RowRouting.dormant (F:=F) phys
      (D.letters a x i) ((view.2 i).trans (ite_eq_right hi)))) :
    holds (D.electedRow a x m view menu arity i) (D.electedTender a x m phys view menu arity route i) :=
  RowRouting.conditional_property (p := elected i)
    (fun hi => RowRouting.retyped (menu i hi) ((view.1 i).trans (arity i hi).symm)
      ((view.2 i).trans (ite_eq_left hi)) (route i hi))
    (fun hi => RowRouting.dormant (F:=F) phys (D.letters a x i) ((view.2 i).trans (ite_eq_right hi)))
    holds on_ok off_ok

theorem elected_entry (i : I) (hit : elected i) (c : Histogram (Fin (D.letters a x i)) (D.copies a x i)) :
    let R:=route i hit
    let c':=cast (congrArg₂ (fun alphabet amount => Histogram (Fin alphabet) amount) ((view.1 i).trans (arity i hit).symm)
      ((view.2 i).trans (ite_eq_left hit))) c
    ∃ (input : (D.electedRow a x m view menu arity i).input = (Row.packet (menu i hit) (b).copies).input)
      (output : (D.electedTender a x m phys view menu arity route i).post c = R.post c'),
      (D.electedTender a x m phys view menu arity route i).entry c =
        Installs.transport input.symm output.symm (R.entry c') := by
  let hists := cast (congrArg₂ (fun alphabet amount => Histogram (Fin alphabet) amount)
    ((view.1 i).trans (arity i hit).symm) ((view.2 i).trans (ite_eq_left hit))) c
  let holds (row : Row F S (D.letters a x i) (D.copies a x i)) (routed : RowRouting row phys) : Prop :=
    ∃ (input : row.input = (Row.packet (menu i hit) (b).copies).input)
      (output : routed.post c = (route i hit).post hists),
      routed.entry c = Installs.transport input.symm output.symm ((route i hit).entry hists)
  exact elected_property D a x m phys view menu arity route i holds
    (fun hi => RowRouting.retyped_entry (menu i hi) ((view.1 i).trans (arity i hi).symm)
      ((view.2 i).trans (ite_eq_left hi)) (route i hi) c)
    (fun hi => False.elim (hi hit))

theorem elected_empty (i : I) (off : ¬elected i) (c : Histogram (Fin (D.letters a x i)) (D.copies a x i)) (s : Fin S) :
    Subsingleton (State (D.electedRow a x m view menu arity i).input s) ∧
      Subsingleton (State ((D.electedTender a x m phys view menu arity route i).post c) s) ∧
      ∀ u v, (D.electedTender a x m phys view menu arity route i).entry c s u v = (1 : F) := by
  let holds (row : Row F S (D.letters a x i) (D.copies a x i)) (routed : RowRouting row phys) : Prop :=
    Subsingleton (State row.input s) ∧ Subsingleton (State (routed.post c) s) ∧
      ∀ u v, routed.entry c s u v = (1 : F)
  exact elected_property D a x m phys view menu arity route i holds
    (fun hi => False.elim (off hi))
    (fun hi => RowRouting.dormant_site (F:=F) phys (D.letters a x i) ((view.2 i).trans (ite_eq_right hi)) c s)

end CalendarTape.HistogramFormat
end Hierarchy.WireTelescope
end

end OAI

import OAI.Hierarchy.ProtocolRAMPrefixAgreement
import OAI.Hierarchy.TaggedWireEarnedCoordinate
import OAI.Hierarchy.TaggedWireMeasuredPaid
import OAI.Hierarchy.TaggedWireMeasuredCredits

namespace OAI
/-! # One elected packet measured in the same stock and paid banks as the controller -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing
variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball : Type} [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
local notation "G" => Commodity (Fin (2^h)) (Stages h d) k
local notation "shift" => Fintype.card G
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
local notation "roles" => ColumnWires.ends (horizontal n) extra

namespace EarnedInstall
open StockCommit RepairHistogram

variable (g : EarnedInstall p b π extra place u endRow name addr m reg)
  {F J : Type} [Field F] [Fintype J] (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k)))
  (req : J → ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)
  (rt : Fin (Fintype.card (TreeSite n k))) [Nonempty (Fin (Fintype.card (TreeSite n k)))]
  (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (Strip.horizontal n) extra e)) req)
  (pad : Chord K) {spare ports rows : ℕ} {ballot : Batch (P.terms+spare) ports}
  {a : Area} {s : Sources} {before archived : Memory w} {L : PortPlan (fresh a s) ballot before rows}
  {j : Fin rows} (N : NativePacketRow P spare ballot L j)

local notation "ch" => g.tender labels req rt P ballot.copies pad
local notation "occ" => fun r:R => L.enum ⟨j,N.ports r⟩
local notation "tag" => RepairHistogram.kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns before
local notation "bits" => histWidth P.count N.h
variable (code : Commodity (Fin (2^h)) (Stages h d) k ↪ Fin a.goods)
    (source : ∀r:ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k,
      RepairHistogram.kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns before
        (L.enum ⟨j,N.ports r⟩)=ColumnWires.account (code ∘ addr) r)

include source in
omit [Nonempty (Fin (Fintype.card X))] in
/-- Testing the original commodity address picks out precisely the role credits
sent to that commodity's native stock row. -/
theorem measured_stock (i : G) :
    (ch).install.load ((ch).bits N.h) (stockRow (p:=b.rows) (stockOrder h d k i)) =
      L.rowCredit j (fun e => (tag) e=some (code i)) := by
  classical
  rw [g.tender_stock, N.credit]
  apply Finset.sum_congr rfl
  intro r _
  rw [source]
  have same : (ColumnWires.account addr r=some i) ↔
      ColumnWires.account (code ∘ addr) r=some (code i) := by
    cases r with
    | extra x => cases x <;> simp [ColumnWires.account]
    | catalyst | radius | cross | horizontal => simp [ColumnWires.account]
  by_cases hit : ColumnWires.account addr r=some i
  · simp only [ite_eq_left hit,ite_eq_left (same.mp hit)]
  · simp only [ite_eq_right hit,ite_eq_right (mt same.mpr hit)]

omit [Fintype A] [Fintype B] [Nonempty (Fin (Fintype.card X))] in
private theorem paid_iff_cash (r : R) :
    paidRole r ↔ ColumnWires.account (code ∘ addr) r=none := by
  cases r with
  | extra x => cases x <;> simp [paidRole,ColumnWires.account]
  | catalyst | radius | horizontal | cross => simp [paidRole,ColumnWires.account]

def usesMate : R → Prop
  | .catalyst _ _ => True
  | _ => False

include source in
omit [Nonempty (Fin (Fintype.card X))] in
/-- Both paid parts of the installation come from the very same credited
histogram bytes. The archive edge and mask are the actual per-occurrence
word operands; all other edge answers are immaterial on a nonpaying role. -/
theorem measured_paid (stamp : LabelSource) (mask mate : Expr) (e : Fin b.rows)
    (primary : ∀r:R, paidRole r → stamp.edge.eval archived (((occ) r).val:Word w)=(p.primary b r).eval m reg)
    (on : ∀r:R, mask.eval archived (((occ) r).val:Word w)≠0 ↔ usesMate r)
    (second : ∀c j, mate.eval archived (((occ) (.catalyst c j)).val:Word w) =
      (p.mate b (.catalyst c j:R)).eval m reg) :
    (ch).install.load ((ch).bits N.h) (paidRow (g:=shift) e) =
      L.rowCredit j (primaryHit a s stamp before archived e) +
        L.rowCredit j (secondaryHit a s mask mate before archived e) +
        ∑ t : T, if ((p.primary b (treeRole n k t:R)).eval m reg).val=e.val
          then ballot.copies*P.selectorBits else 0 := by
  classical
  let port (r : R) : Fin a.occurrences := ⟨(L.enum ⟨j,N.ports r⟩).val,(L.enum ⟨j,N.ports r⟩).isLt⟩
  have decoded (r : R) : RepairHistogram.kind (goods:=a.goods) (fresh a s).plan.bank
      (fresh a s).columns before (port r)=ColumnWires.account (code ∘ addr) r := source r
  have edgeAt (r : R) (pay : paidRole r) :
      stamp.edge.eval archived ((port r).val:Word w)=(p.primary b r).eval m reg := primary r pay
  have mateAt (c : C) (axis : Fin k) :
      mate.eval archived ((port (.catalyst c axis)).val:Word w)=(p.mate b (.catalyst c axis:R)).eval m reg :=
    second c axis
  refine (g.tender_paid_read labels req rt P ballot.copies pad N.h e).trans ?_
  refine congrArg₂ Nat.add (congrArg₂ Nat.add ?_ ?_) rfl
  · refine Eq.trans ?_ (N.credit (fun i => primaryHit a s stamp before archived e i)).symm
    apply Finset.sum_congr rfl
    intro r _
    change _ = if primaryHit a s stamp before archived e (port r) then histWidth P.count N.h r else 0
    unfold primaryHit
    rw [decoded r,← paid_iff_cash code r]
    by_cases use : paidRole r
    · by_cases hit : ((p.primary b r).eval m reg).val=e.val <;> simp [use,edgeAt r use,hit]
    · simp [use]
  · refine Eq.trans ?_ (N.credit (fun i => secondaryHit a s mask mate before archived e i)).symm
    apply Finset.sum_congr rfl
    intro r _
    change _ = if secondaryHit a s mask mate before archived e (port r) then histWidth P.count N.h r else 0
    unfold secondaryHit
    rw [decoded r,← paid_iff_cash code r]
    have maskAt : mask.eval archived ((port r).val:Word w)≠0 ↔ usesMate r := on r
    rw [maskAt]
    cases r with
    | catalyst c j =>
      by_cases hit : ((p.mate b (.catalyst c j:R)).eval m reg).val=e.val <;>
        simp [usesMate,paidRole,mateAt,hit]
    | radius | cross | horizontal | extra => simp [usesMate]

include source in
omit [Nonempty (Fin (Fintype.card X))] in
/-- The mathematical routing is fixed before the row histogram is supplied.
At the later installation archive, all of its source-side operands still
use the same low memory; the actual edge and mask words are read there. -/
theorem measured_paid_at (stamp : LabelSource) (mask mate : Expr) (e : Fin b.rows)
    (cut : ℕ) (low : PrefixAgreement.Low cut archived m) (fits : ∀r:R,(p.primary b r).Fits w cut)
    (primary : ∀r:R, paidRole r → stamp.edge.eval archived (((occ) r).val:Word w)=
      (p.primary b r).eval archived reg)
    (on : ∀r:R, mask.eval archived (((occ) r).val:Word w)≠0 ↔ usesMate r)
    (second : ∀c j, mate.eval archived (((occ) (.catalyst c j)).val:Word w) =
      (p.mate b (.catalyst c j:R)).eval archived reg) :
    (ch).install.load ((ch).bits N.h) (paidRow (g:=shift) e) =
      L.rowCredit j (primaryHit a s stamp before archived e) +
        L.rowCredit j (secondaryHit a s mask mate before archived e) +
        ∑ t : T, if ((p.primary b (treeRole n k t:R)).eval archived reg).val=e.val
          then ballot.copies*P.selectorBits else 0 := by
  have preserved (r : R) : (p.primary b r).eval archived reg=(p.primary b r).eval m reg :=
    PrefixAgreement.expr _ _ _ _ (PrefixAgreement.inputEnd_of_fits _ (fits r)) low reg
  have sides (c : C) (axis : Fin k) : (p.mate b (.catalyst c axis:R)).eval archived reg =
      (p.mate b (.catalyst c axis:R)).eval m reg := preserved (.radius c axis true)
  simp only [preserved]
  exact g.measured_paid labels req rt P pad N code source stamp mask mate e
    (fun r h=>(primary r h).trans (preserved r)) on (fun c t=>(second c t).trans (sides c t))

end EarnedInstall
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI

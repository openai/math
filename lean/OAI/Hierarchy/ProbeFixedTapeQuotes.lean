import OAI.Hierarchy.ProbeFixedStripQuotes
import OAI.Hierarchy.ProtocolRAMCalendarChargePages

namespace OAI
/-! # Quoting a committed native port row at its actual stock and fee prices -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.CatalystArchive

open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing BigOperators

variable {A B C H F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N w q D z d : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H → ℝ} {cap : A → ℝ}
local notation "Roles" => Role C H (A⊕B) k
local notation "req" => demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
local notation "prices" => (fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap
variable {e : Role C H (A⊕B) k → Chord sites}
variable {menu : Probe.FixedMenu F e
    (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N}


namespace StripInput

omit [Nonempty (Fin k)] in
/-- Decode the commodity, the printed link, and the finite selector charge for a
single accepted packet. This yields the word-level inequality consumed by
`StockCommit.failedRows` on the original physical row, before reindexing it. -/
theorem selected_tape_quote {γ : ℝ} (grid : A → ℝ)
    (inside : quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid) ∈ prices)
    (failed : ε ≤ Probe.discrepancy F e req (quote M len (LocalCommodity.extraPrice (B:=B) grid))) :
    let key := quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid)
    let i := menu.select ⟨key,inside,failed⟩
    let P := menu.packet i
    ∀ (extra : ℕ) (x : StripInput menu w z d (P.terms+extra) D)
      (j : Fin x.raw.market.rows) (_live : j∈liveRows x.ballot x.mem x.raw.market.rows)
      (_arity : (x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))).val=P.terms)
      (_code : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1),
      let c := fresh x.form.pricedArea x.form.stockSource
      ∀ {paths : ℕ} (mount : (c.native w x.raw.market.rows x.ballot).ready x.mem)
        (bc : BroadcastRoom c x.ballot x.raw.market.rows w) (keys : CashKeys c.occurrences x.raw.market.rows c.goods paths)
        (link : Fin c.occurrences → ℕ → ℝ) (treePrice : Fin x.raw.market.rows → ℕ → ℝ)
        (idx : A → Fin x.raw.coordinates) (price : Fin x.raw.coordinates → ℝ) (ep : ℝ) (K width base : ℕ),
        let T := c.tape x.ballot x.mem x.plan mount bc keys link treePrice
        let port := fun r : Roles => PortPadding.inject x.ports (Fintype.equivFin Roles r)
        let row := fun v : Fin D => x.plan.enum ⟨j,v⟩
        let out := (c.native w x.raw.market.rows x.ballot).after x.mem
        0 ≤ γ → γ ≤ menu.margin → 0 ≤ ep → 0 ≤ tree →
        (∀ a,((x.addr a).eval x.mem (j.val:Word w)).val=(idx a).val) →
        (∀ r,account idx r=none → link (row (port r)) (out (keys.link (row (port r)))).val=printed M len r) →
        (∀ a,grid a ≤ price (idx a) ∧ price (idx a) ≤ grid a+ep) →
        c.price=(MenuROM.selectorCharges menu base).bank 0 → (MenuROM.selectorCharges menu base).Resident x.mem →
        (∀ code,treePrice j code ≤ tree) →
        (Fintype.card Roles:ℝ)*x.ballot.maxWidth*ep ≤ P.width*γ/2 → copied K P.width width ≤ x.ballot.copies →
        (∑ v,(T.put (row v):ℝ)*activePrice T.kind T.weight price (row v))+T.broadcast j+
          (copied K P.width width:ℝ)*(P.width*γ/2) ≤
            ∑ v,(T.take (row v):ℝ)*activePrice T.kind T.weight price (row v) := by
  intro key i P extra x j live arity code c paths mount bc keys link treePrice idx price ep K width base T port row out
    positive margin epPos treePos atStock atCash digits table resident lengths precise copies
  let R := packetAt i extra x j live arity code
  let kind := fun v : Fin D => T.kind (row v)
  let fee := fun v : Fin D => T.weight (row v)
  have bitEq : c.price.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))=(P.selectorBits:Word w) := by
    have packet : x.ballot.packet.eval x.mem (j.val:Word w)=(((Fintype.equivFin menu.index i).val+1:ℕ):Word w) :=
      Fin.ext (code.trans (Fin.val_cast_of_lt ((Nat.succ_lt_succ (Fintype.equivFin menu.index i).isLt).trans_le (by simpa only [Nat.add_comm 1] using x.codeFit))).symm)
    rw [table,packet]
    exact MenuROM.charge_lookup menu base x.mem resident i
  have value := c.read_broadcast x.ballot x.mem j mount bc.fits x.termFit x.copyFit x.sumFit (bc.keeps j)
  rw [ite_eq_left (Finset.mem_filter.mp live).2,bitEq] at value
  have br : T.broadcast j ≤ x.ballot.copies*(tree*P.selectorBits) := by
    change (x.ballot.copies:ℝ)*(treePrice j (out (keys.broadcast j)).val*((out (c.broadcast+j.val)).val:ℝ)) ≤ _
    have value' : out (c.broadcast+j.val)=(P.selectorBits:Word w) := value
    rw [value']
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact (mul_le_mul_of_nonneg_right (lengths _) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.mod_le _ _)) treePos)
  exact selected_role_quote menu len grid inside failed extra x.ballot x.plan j R idx kind fee price
    (T.broadcast j) ep K width positive margin epPos (fun r => x.role_kind j idx atStock r)
    atCash digits br precise copies

omit [Nonempty (Fin k)] in
/-- Read the chosen index and alphabet directly from the two genuine menu-ROM
words. The final width in this statement is the one decoded from the actual
row, so it can be used for an arbitrary selected row in `StockCommit.failedRows`. -/
theorem quote_at_live (x : StripInput menu w z d q D) (j : Fin x.raw.market.rows)
    (live : j∈liveRows x.ballot x.mem x.raw.market.rows) (grid : A → ℝ)
    (inside : quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid) ∈ prices)
    (selected : ∃ h : ε≤Probe.discrepancy F e req (quote M len (LocalCommodity.extraPrice (B:=B) grid)),
      let i := menu.select ⟨_,inside,h⟩
      x.ballot.packet.eval x.mem (j.val:Word w)=(((Fintype.equivFin menu.index i).val+1:ℕ):Word w) ∧
      x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))=((menu.packet i).terms:Word w))
    (ordinals : ∀ i,(menu.packet i).terms ≤ q ∧ (menu.packet i).terms < 2^w) :
    let c := fresh x.form.pricedArea x.form.stockSource
    ∀ {paths : ℕ} (mount : (c.native w x.raw.market.rows x.ballot).ready x.mem)
      (bc : BroadcastRoom c x.ballot x.raw.market.rows w) (keys : CashKeys c.occurrences x.raw.market.rows c.goods paths)
      (link : Fin c.occurrences → ℕ → ℝ) (treePrice : Fin x.raw.market.rows → ℕ → ℝ)
      (idx : A → Fin x.raw.coordinates) (price : Fin x.raw.coordinates → ℝ) (γ ep : ℝ) (K width base : ℕ),
      let T := c.tape x.ballot x.mem x.plan mount bc keys link treePrice
      let port := fun r : Roles => PortPadding.inject x.ports (Fintype.equivFin Roles r)
      let row := fun v : Fin D => x.plan.enum ⟨j,v⟩
      let out := (c.native w x.raw.market.rows x.ballot).after x.mem
      0 ≤ γ → γ ≤ menu.margin → 0 ≤ ep → 0 ≤ tree →
      (∀ a,((x.addr a).eval x.mem (j.val:Word w)).val=(idx a).val) →
      (∀ r,account idx r=none → link (row (port r)) (out (keys.link (row (port r)))).val=printed M len r) →
      (∀ a,grid a ≤ price (idx a) ∧ price (idx a) ≤ grid a+ep) →
      c.price=(MenuROM.selectorCharges menu base).bank 0 → (MenuROM.selectorCharges menu base).Resident x.mem →
      (∀ code,treePrice j code ≤ tree) →
      (∀i,(Fintype.card Roles:ℝ)*x.ballot.maxWidth*ep ≤ (menu.packet i).width*γ/2) →
      (∀i,copied K (menu.packet i).width width ≤ x.ballot.copies) →
      (∑ v,(T.put (row v):ℝ)*activePrice T.kind T.weight price (row v))+T.broadcast j+
        (copied K (x.nominal j) width:ℝ)*(x.nominal j*γ/2) ≤
          ∑ v,(T.take (row v):ℝ)*activePrice T.kind T.weight price (row v) := by
  obtain ⟨h,raw⟩ := selected
  let i := menu.select ⟨_,inside,h⟩
  let P := menu.packet i
  obtain ⟨extra,hq⟩ := Nat.exists_eq_add_of_le (ordinals i).1
  subst q
  have decoded := x.decoded_packet_words j i (ordinals i).2 raw
  intro c paths mount bc keys link trees idx price γ ep K width base T port row out γpos margin epPos treePos atStock atCash
    digits table resident lengths precise copies
  rw [x.nominal_code j i decoded.1]
  exact selected_tape_quote grid inside h extra x j live decoded.2 decoded.1 mount bc keys link trees idx price ep K width base
    γpos margin epPos treePos atStock atCash digits table resident lengths (precise i) (copies i)

end StripInput
end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI

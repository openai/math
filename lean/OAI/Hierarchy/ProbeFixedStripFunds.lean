import OAI.Hierarchy.ProbeFixedFailureFunds
import OAI.Hierarchy.ProbeCatalystCashEntry
import OAI.Hierarchy.ProtocolRAMCalendarCommitLayout

namespace OAI
/-! # Funding the actual two padded strip formats at their ordinary addresses -/

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
variable (x : _root_.OAI.Hierarchy.ProtocolRAM.CatalystArchive.StripInput (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) menu w z d q D)
local notation "header" => (⟨x.start,x.raw.market.rows,D⟩ : PortHeader)
local notation "field" => fun a : A => PortPadding.inject x.ports (Fintype.equivFin Roles (.extra (.inl a)))
local notation "padded" => PortPadding.extend x.slots none
local notation "old" => x.form.stockSource.old

/-- The joint physical address map for the actual committed rows and the
ordinary local roles from this menu. -/
def Placed := ∃ place : ↥(liveRows x.ballot x.mem x.raw.market.rows) × A ↪ Fin x.raw.coordinates,
  ∀ j a,((x.addr a).eval x.mem (j.val.val:Word w)).val=(place (j,a)).val

omit [Nonempty (Fin k)] in
/-- The physical field decoder distinguishes padding, paid links and exactly
one real field for each ordinary account. -/
theorem ordinary_operand (v : Fin D) (a : Expr) (hit : padded v=some a) :
    ∃ t : A, (field) t=v ∧ x.addr t=a := by
  by_cases real : v.val < Fintype.card Roles
  · let p : Fin (Fintype.card Roles) := ⟨v.val,real⟩
    have vr : PortPadding.inject x.ports p=v := Fin.ext rfl
    rw [← vr,PortPadding.extend_real] at hit
    let role := (Fintype.equivFin Roles).symm p
    change (account (id : A → A) role).map x.addr=some a at hit
    obtain ⟨t,mapped,read⟩ := Option.map_eq_some_iff.mp hit
    obtain ⟨s,ordinary,eq⟩ := ordinary_of_some _ _ mapped
    change s=t at eq
    subst t
    refine ⟨s,?_,read⟩
    exact (congrArg (fun role : Roles => PortPadding.inject x.ports (Fintype.equivFin Roles role))
      ordinary.symm).trans ((congrArg (PortPadding.inject x.ports)
      ((Fintype.equivFin Roles).apply_symm_apply p)).trans vr)
  · rw [PortPadding.extend_tail x.slots none v (Nat.le_of_not_lt real)] at hit
    cases hit

omit [Nonempty (Fin k)] in
theorem ordinary_stock (v : Fin D) (a : Expr) (hit : padded v=some a) :
    x.ballot.stock v=.lookup old a := by
  by_cases real : v.val < Fintype.card Roles
  · let p : Fin (Fintype.card Roles) := ⟨v.val,real⟩
    have vr : PortPadding.inject x.ports p=v := Fin.ext rfl
    rw [←vr,PortPadding.extend_real] at hit
    rw [←vr]
    change PortPadding.extend _ (Expr.lit 0) (PortPadding.inject x.ports p)=_
    rw [PortPadding.extend_real]
    change StripDirectory.inventory old _ (x.slots p)=_
    rw [hit]
    rfl
  · rw [PortPadding.extend_tail x.slots none v (Nat.le_of_not_lt real)] at hit
    cases hit

omit [Nonempty (Fin k)] in
/-- For either generated catalogue, stock checks and the final signed scatter
refer to exactly the same previous inventory. Degree one follows from the
physical joint row-and-role embedding on the selected rows. -/
theorem funded (place : ↥(liveRows x.ballot x.mem x.raw.market.rows) × A ↪ Fin x.raw.coordinates)
    (read : ∀ j a,((x.addr a).eval x.mem (j.val.val:Word w)).val=(place (j,a)).val)
    (seed : ∀ i : Fin x.raw.coordinates,(old).read x.mem (i.val:Word w)=x.mem (x.form.pricedArea.start+i.val))
    (i : Fin x.raw.coordinates) :
    let c := fresh x.form.pricedArea x.form.stockSource
    OuterBank.resourceBits (RepairHistogram.kind c.plan.bank c.columns x.mem)
      (consumedBits (n:=c.occurrences) c.columns x.mem) i ≤ (x.mem (x.form.pricedArea.start+i.val)).val := by
  exact (header).funded_of_slots x.form.pricedArea.start x.raw.coordinates x.form.limit old
    x.form.sources.reserve x.form.sources.half x.form.sources.price (Calendar.word x.form.board.modeOut)
    padded x.ballot x.form.board.wire x.mem x.loaded x.portFit x.termFit x.copyFit x.sumFit x.bankFit
    (field) x.addr x.ordinary_operand place read x.ordinary_stock seed i

omit [Nonempty (Fin k)] in
/-- The sum of all physical installation entries for a commodity stays within one
selected occurrence's maximum, since distinct moving rows have distinct slots. -/
theorem credit_bound (placed : x.Placed) (i : Fin x.raw.coordinates) :
    let c:=fresh x.form.pricedArea x.form.stockSource
    OuterBank.resourceBits (RepairHistogram.kind c.plan.bank c.columns x.mem)
      (installedBits (n:=c.occurrences) c.columns x.mem) i≤x.board.maxWidth*x.board.copies := by
  obtain ⟨place,read⟩:=placed
  apply (header).credit_bound_of_slots x.form.pricedArea.start x.raw.coordinates x.form.limit old
    x.form.sources.reserve x.form.sources.half x.form.sources.price (Calendar.word x.form.board.modeOut)
    padded x.ballot x.form.board.wire x.mem x.loaded x.portFit x.termFit x.copyFit x.sumFit x.bankFit
    (field) x.addr x.ordinary_operand place read (x.board.maxWidth*x.board.copies) i
  intro j v
  exact x.ballot.wire_bound x.mem (j.val:Word w) (x.form.board.wire v) x.termFit x.copyFit x.sumFit

omit [Nonempty (Fin k)] in
/-- Every actual selector branch pays at most the row-wide clipped wire bound.
Consequently a single-bank arithmetic bound suffices for the entire program. -/
theorem credit_fit (place : ↥(liveRows x.ballot x.mem x.raw.market.rows) × A ↪ Fin x.raw.coordinates)
    (read : ∀ j a,((x.addr a).eval x.mem (j.val.val:Word w)).val=(place (j,a)).val)
    (i : Fin x.raw.coordinates)
    (size : (x.mem (x.form.pricedArea.start+i.val)).val+x.board.maxWidth*x.board.copies < 2^w) :
    let c := fresh x.form.pricedArea x.form.stockSource
    (x.mem (x.form.pricedArea.start+i.val)).val+OuterBank.resourceBits (RepairHistogram.kind c.plan.bank c.columns x.mem)
      (installedBits (n:=c.occurrences) c.columns x.mem) i < 2^w := by
  apply (header).credit_fit_of_slots x.form.pricedArea.start x.raw.coordinates x.form.limit old
    x.form.sources.reserve x.form.sources.half x.form.sources.price (Calendar.word x.form.board.modeOut)
    padded x.ballot x.form.board.wire x.mem x.loaded x.portFit x.termFit x.copyFit x.sumFit x.bankFit
    (field) x.addr x.ordinary_operand place read (x.board.maxWidth*x.board.copies) i _ size
  intro j v
  exact x.ballot.wire_bound x.mem (j.val:Word w) (x.form.board.wire v) x.termFit x.copyFit x.sumFit

omit [Nonempty (Fin k)] in
theorem settlement (placed : x.Placed) (i : Fin x.raw.coordinates)
    (seed : ∀ j : Fin x.raw.coordinates,(old).read x.mem (j.val:Word w)=x.mem (x.form.pricedArea.start+j.val))
    (size : (x.mem (x.form.pricedArea.start+i.val)).val+x.board.maxWidth*x.board.copies < 2^w) :
    let c := fresh x.form.pricedArea x.form.stockSource
    let tags := RepairHistogram.kind (goods:=x.raw.coordinates) c.plan.bank c.columns x.mem
    OuterBank.resourceBits tags (consumedBits (n:=c.occurrences) c.columns x.mem) i ≤
        (x.mem (x.form.pricedArea.start+i.val)).val ∧
      (x.mem (x.form.pricedArea.start+i.val)).val+
        OuterBank.resourceBits tags (installedBits (n:=c.occurrences) c.columns x.mem) i < 2^w := by
  obtain ⟨p,read⟩ := placed
  exact ⟨x.funded p read seed i,x.credit_fit p read i size⟩

end StripInput

/-- The seed ROM copies precisely the word that the still-operational occurrence
expression reads, for both placed market boards. -/
theorem stage_seed_word (a : Area) (s : Sources) (g : LabelSource) (before : Memory w)
    (prior : s.old.base+s.old.size ≤ a.start) (i : Fin a.goods) :
    s.old.read (stageInput a s g before) (i.val:Word w) =
      stageInput a s g before (a.start+i.val) := by
  let m := (g.pass a.occurrences).apply before
  change s.old.read ((a.seed s).apply m) _ = (a.seed s).apply m _
  rw [a.seed_bank s m s.old _ prior]
  exact (ProtocolRAMGeneratedWrite.read_image a.start a.goods (.lookup s.old .row) m i).symm

/-- The actual stock window only reserves the used prefix of the old bank.
For that sharper layout, the seed still exactly duplicates every used word. -/
theorem stage_seed_word_prefix (a : Area) (s : Sources) (g : LabelSource) (before : Memory w)
    (prior : s.old.base+a.goods ≤ a.start) (width : a.goods≤2^w) (capacity : a.goods≤ s.old.size)
    (i : Fin a.goods) : s.old.read (stageInput a s g before) (i.val:Word w) =
      stageInput a s g before (a.start+i.val) := by
  let m := (g.pass a.occurrences).apply before
  change ((a.seed s).apply m) (s.old.base+(i.val:Word w).val%s.old.size)=((a.seed s).apply m) (a.start+i.val)
  rw [Fin.val_cast_of_lt (i.isLt.trans_le width),Nat.mod_eq_of_lt (i.isLt.trans_le capacity)]
  exact (a.seed_frame s m _ (.inl (lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) prior))).trans
    (a.seed_read s m i width capacity).symm

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI

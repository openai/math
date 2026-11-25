import OAI.Hierarchy.ProbeCatalystLiveDebit
import OAI.Hierarchy.ProbeNativeRoleAddress
import OAI.Hierarchy.ProbeStripPlacedBoard
import OAI.Hierarchy.ProbeStripCompiledFormat
import OAI.Hierarchy.ProbeMenuSizes

namespace OAI
/-! # Catalyst demand on a live rectangular histogram board -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing

variable {F E A B C H : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  [Fintype B] [Fintype C] [Fintype H] {k sites N w q D n z d balls : ℕ} [Nonempty (Fin sites)]
  {edge : E→ Chord sites} {req : A→E} {box : Set (E→ℝ)} {ε tree : ℝ}

/-- The real native debit on each physically padded role past the end of
the original heterogeneous ballot is zero, independently of its word or flag. -/
theorem placed_pad (s : Format z d k q n) (start : ℕ) (slot : Fin n→Option Expr) (m : Memory w)
    (loaded : (⟨start,s.market.rows,D⟩ : PortHeader).Loaded m) (fit : D≤2^w)
    (terms : q≤2^w) (copies : s.histMass<2^w) (total : q*s.histMass<2^w)
    (bound : n≤D) (maxFit : s.batch.batch.maxWidth<2^w) (j : Fin s.market.rows) (i : Fin D) (tail : n≤ i.val) :
    cashWord (PortPadding.occurrencePlan s start slot m loaded fit terms copies total) (j,i)=0 := by
  let l := PortPadding.occurrencePlan s start slot m loaded fit terms copies total
  have zero := PortPadding.placed_debit s start slot bound m (j.val:Word w) maxFit terms copies total i
  rw [PortPadding.extend_tail _ _ _ tail] at zero
  have out := (l.read j i).2.trans (congrArg Fin.val zero)
  change cashWord l (j,i)=0
  unfold cashWord
  dsimp only
  split
  · exact out
  · rfl

variable [Nonempty (Role C H (A⊕B) k)] {M : ℝ} {len : H→ℝ} {cap : A→ℝ}
local notation "Roles" => Role C H (A⊕B) k
local notation "needRoles" => demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
local notation "prices" => (fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap

/-- This is exactly the raw catalogue and channel compiler used on each side
of `payloadGeometry` and `purchasedGeometry`. -/
def nativeStrip {e : Roles→ Chord sites}
    (menu : Probe.FixedMenu F e needRoles prices ε tree N) (addr : A→Expr) (active : Expr)
    (board : StripDirectory.Boards z d k q (Fintype.card A) (Fintype.card Roles)) (prior : ℕ) :
    Format z d k q (Fintype.card Roles) :=
  board.build (StripDirectory.format ⟨addr,account id,active⟩ menu) prior

def nativeSlot (addr : A→Expr) (active : Expr) :=
  (⟨addr,account id,active⟩ : StripDirectory.Channels A Roles).slot

theorem native_perCopy {e : Roles→ Chord sites} (menu : Probe.FixedMenu F e needRoles prices ε tree N)
    (addr : A→Expr) (active : Expr)
    (board : StripDirectory.Boards z d k q (Fintype.card A) (Fintype.card Roles))
    (prior start : ℕ) (room : Fintype.card Roles≤D) (v : Roles) :
    let raw := nativeStrip menu addr active board prior
    let f := PortPadding.format D start (nativeSlot (H:=H) (C:=C) (B:=B) (k:=k) addr active) raw
    let b := enabledBatch raw.market.layout f.board
    b.perCopy (PortPadding.inject room (Fintype.equivFin Roles v)) =
      StripDirectory.entry menu b.packet (fun i => StripDirectory.useBits menu i v) := by
  intro raw f b
  change PortPadding.extend raw.board.batch.perCopy (.lit 0) (PortPadding.inject room (Fintype.equivFin Roles v))=_
  rw [PortPadding.extend_real]
  change StripDirectory.entry menu b.packet (fun i => StripDirectory.useBits menu i
    ((Fintype.equivFin Roles).symm ((Fintype.equivFin Roles) v)))=_
  rw [Equiv.symm_apply_apply]

/-- Classify the fresh signed StockCommit by the real destination expression.
For an ordinary role the evaluated address lies in the source stock bank.
Every other role has the physical one-past-the-end sentinel. -/
theorem placed_kind (raw : Format z d k q n) (start : ℕ) (slots : Fin n→Option Expr)
    (m : Memory w) (loaded : (⟨start,raw.market.rows,D⟩ : PortHeader).Loaded m) (fit : D≤2^w)
    (qFit : q≤2^w) (copyFit : raw.histMass<2^w) (total : q*raw.histMass<2^w) (ports : n≤D)
    (bankFit : (PortPadding.format D start slots raw).pricedArea.start+raw.coordinates<2^w)
    (j : Fin raw.market.rows) (v : Fin n)
    (address : ∀ a,slots v=some a → (a.eval m (j.val:Word w)).val<raw.coordinates) :
    let f := PortPadding.format D start slots raw
    let st := fresh f.pricedArea f.stockSource
    let l := PortPadding.occurrencePlan raw start slots m loaded fit qFit copyFit total
    RepairHistogram.kind (goods:=st.goods) st.plan.bank st.columns m (l.enum ⟨j,PortPadding.inject ports v⟩)=none
      ↔ slots v=none := by
  intro f st l
  let h : PortHeader := ⟨start,raw.market.rows,D⟩
  let field := PortPadding.inject ports v
  let tag := RepairHistogram.kind (goods:=st.goods) st.plan.bank st.columns m (l.enum ⟨j,field⟩)
  have read (i : Fin raw.coordinates) : tag=some i ↔ ∃ a,slots v=some a ∧
      (a.eval m (j.val:Word w)).val=i.val := by
    have t := StripDirectory.fresh_kind_iff h f.pricedArea.start raw.coordinates f.limit
      f.stockSource.old f.sources.reserve f.sources.half f.sources.price (Calendar.word f.board.modeOut)
      (PortPadding.extend slots none) (enabledBatch f.market.layout f.board) f.board.wire
      m loaded fit bankFit j field i
    change _ ↔ ∃ a,PortPadding.extend slots none (PortPadding.inject ports v)=some a ∧ _ at t
    simp only [PortPadding.extend_real] at t
    exact t
  change tag=none ↔ slots v=none
  cases hp : slots v with
  | none =>
    cases htag : tag with
    | none => simp
    | some i =>
      obtain ⟨a,ha,_⟩ := (read i).mp htag
      simp [hp] at ha
  | some a =>
    let i : Fin raw.coordinates := ⟨_,address a hp⟩
    have yes := (read i).mpr ⟨a,hp,rfl⟩
    simp [yes]

/-- The raw geometric slot operands and the frozen menu word suffice to
recover every real catalyst on an active row of the actual placed board. -/
theorem strip_realRead {e : Roles→ Chord sites} (menu : Probe.FixedMenu F e needRoles prices ε tree N)
    (addr : A→Expr) (active : Expr)
    (board : StripDirectory.Boards z d k q (Fintype.card A) (Fintype.card Roles))
    (prior start : ℕ) (ports : Fintype.card Roles≤D) (m : Memory w) :
    let raw := nativeStrip menu addr active board prior
    let slots := nativeSlot (B:=B) (H:=H) (C:=C) (k:=k) addr active
    let f := PortPadding.format D start slots raw
    let b := enabledBatch raw.market.layout f.board
    ∀ (loaded : (⟨start,raw.market.rows,D⟩ : PortHeader).Loaded m) (fit : D≤2^w)
      (terms : q≤2^w) (copies : raw.histMass<2^w) (total : q*raw.histMass<2^w),
    let l := PortPadding.occurrencePlan raw start slots m loaded fit terms copies total
    1+Fintype.card menu.index≤2^w →
    (PacketWidths.ofMenu menu).maximum≤board.maxWidth →
    board.maxWidth<2^w → board.copies*board.maxWidth<2^w →
    f.pricedArea.start+raw.coordinates<2^w →
    ∀ j : Fin raw.market.rows, j∈liveRows b m raw.market.rows →
    (∀ a,(addr a |>.eval m (j.val:Word w)).val<raw.coordinates) →
    ∀ v : Roles,cashWord l (j,PortPadding.inject ports (Fintype.equivFin Roles v))=
      released v (b.copies*((menuIndex menu.index (b.packet.eval m (j.val:Word w)).val).elim 0
        (fun i=>cashRate M (menu.packet i).width))) := by
  intro raw slots f b loaded fit terms copies total l codeRoom coeff capFit wide bankRoom j on addresses v
  let field := Fintype.equivFin Roles v
  have slot : slots field=(account (id : A→A) v).map addr := by
    change (account id ((Fintype.equivFin Roles).symm (Fintype.equivFin Roles v))).map addr=_
    rw [Equiv.symm_apply_apply]
  have logical : slots field=none ↔ account (id : A→A) v=none := by rw [slot];simp
  have valid (x : Expr) (got : slots field=some x) : (x.eval m (j.val:Word w)).val<raw.coordinates := by
    rw [slot] at got
    obtain ⟨a,_,eq⟩ := Option.map_eq_some_iff.mp got
    exact eq ▸ addresses a
  have kind := (placed_kind raw start slots m loaded fit terms copies total ports bankRoom j field valid).trans logical
  apply menu_live_cash menu l ports j on codeRoom capFit wide _ _ v kind
  · intro i a
    exact (StripDirectory.cap_debit menu i a).trans (((PacketWidths.ofMenu menu).maximum_ge i).trans coeff)
  · exact native_perCopy menu addr active board prior start ports

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI

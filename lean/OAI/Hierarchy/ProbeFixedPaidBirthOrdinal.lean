import OAI.Hierarchy.ProbeFixedPriorPaidPair
import OAI.Hierarchy.ProbePaidNativeSelectors
import OAI.Hierarchy.ProtocolRAMCatalystStripDates
import OAI.Hierarchy.ProtocolRAMStripParentFlag

namespace OAI
/-! # The birth date of an acquisition hit by a printed debit -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "f" => v.nativeFormats P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "page" => v.wideSignedPage h width stock
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "banks" => TerminalLayout.settlement page stock
local notation "es" => events v.mesh
local notation "until" => fun e=>(A).base v.mesh e+(A).stride

open StripChart StripDirectory BoughtSockets
open ProbeStage.Native ThreeFlat.RAM.DescriptorExpr
local notation "gs" => v.stamp P h width r banks (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) owners
local notation "tr" => v.nativeTrees P h width
local notation "floor" => (A).endAddress v.mesh
local notation "b" => (P).catalogue
local notation "bs" => v.nativeBoards P h width
local notation "site" => v.located (v.seed P h width) P width
local notation "ported" => withPorts site v.mesh b (P).routes

local notation "ports" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "H" => StripChart.header F bs
local notation "head" => (P).routes.directory.header h D k v.sampler.degree v.depth

private theorem payload_raw_cases {z₀ bits₀ k₀ quotes₀ depth₀ word₀ : ℕ}
    (boards : StripChart.Boards z₀ (2^bits₀) k₀ quotes₀ depth₀) (mesh₀ : Mesh)
    (board : CatalogueRows.Board) (routes : StripChart.PortBanks ((mesh₀.inject+mesh₀.cool)*mesh₀.outerFuel))
    (phase₀ trial₀ : ℕ)
    (field : Fin (max (Fintype.card (PayloadRole (Stages z₀ (2^bits₀)) k₀)) (Fintype.card (PurchasedRole depth₀ k₀))))
    (mem : Memory word₀) (row : Word word₀) (room : board.rows<2^word₀) :
    board.CoreOrPad ((StripChart.rawEdge (StripChart.withPorts boards mesh₀ board routes) board.rows
      (.outer phase₀ trial₀) field).eval mem row) := by
  let sockets := StripChart.payloadPortsAt boards mesh₀ routes
  change board.CoreOrPad ((PortPadding.extend (CatalogueRows.payloadEdge sockets board) (.lit board.rows) field).eval mem row)
  by_cases live : field.val<Fintype.card (PayloadRole (Stages z₀ (2^bits₀)) k₀)
  · simp only [PortPadding.extend,dite_eq_left live]
    let idx : Fin (Fintype.card (PayloadRole (Stages z₀ (2^bits₀)) k₀)) := ⟨field.val,live⟩
    exact (sockets.primary_cases board ((Fintype.equivFin (PayloadRole (Stages z₀ (2^bits₀)) k₀)).symm idx)
      mem row room).elim (fun core=>core) (fun ⟨empty,_⟩=>nomatch empty)
  · rw [PortPadding.extend_tail _ _ _ (Nat.le_of_not_gt live)]
    exact Or.inr (Fin.val_cast_of_lt room)

private theorem purchased_raw_cases {z₀ bits₀ k₀ quotes₀ depth₀ word₀ : ℕ}
    (boards : StripChart.Boards z₀ (2^bits₀) k₀ quotes₀ depth₀) (mesh₀ : Mesh)
    (board : CatalogueRows.Board) (routes : StripChart.PortBanks ((mesh₀.inject+mesh₀.cool)*mesh₀.outerFuel))
    (phase₀ trial₀ slice₀ step₀ : ℕ)
    (field : Fin (max (Fintype.card (PayloadRole (Stages z₀ (2^bits₀)) k₀)) (Fintype.card (PurchasedRole depth₀ k₀))))
    (mem : Memory word₀) (row : Word word₀) (room : board.rows<2^word₀) :
    let observed := (StripChart.rawEdge (StripChart.withPorts boards mesh₀ board routes) board.rows
      (.inner phase₀ trial₀ slice₀ step₀) field).eval mem row
    board.CoreOrPad observed ∨ observed=(board.originalProbe
      (routes.directory.header z₀ (2^bits₀) k₀ boards.sampler.degree depth₀).ports (StripChart.birth mesh₀ phase₀ trial₀) .row).eval mem row := by
  let sockets := StripChart.boughtPortsAt boards mesh₀ board routes phase₀ trial₀
  let words := CatalogueRows.purchaseEdge sockets board
  change board.CoreOrPad ((PortPadding.extend words (.lit board.rows) field).eval mem row) ∨
    (PortPadding.extend words (.lit board.rows) field).eval mem row=_
  by_cases live : field.val<Fintype.card (PurchasedRole depth₀ k₀)
  · simp only [PortPadding.extend,dite_eq_left live]
    let idx : Fin (Fintype.card (PurchasedRole depth₀ k₀)) := ⟨field.val,live⟩
    rcases sockets.primary_cases board ((Fintype.equivFin (PurchasedRole depth₀ k₀)).symm idx) mem row room with core|⟨origin,_,hit⟩
    · exact Or.inl core
    · exact Or.inr hit
  · left
    rw [PortPadding.extend_tail _ _ _ (Nat.le_of_not_gt live)]
    exact Or.inr (Fin.val_cast_of_lt room)


private theorem outside_core {W : ℕ} (board : Board) (y : Word W) (j : Fin board.boughtRows)
    (hit : y.val=(board.boughtIndex j).val) (core : board.CoreOrPad y) : False := by
  have extent:=(board.boughtIndex j).isLt
  change board.coreRows+j.val<board.rows at extent
  change y.val=board.coreRows+j.val at hit
  change y.val<board.coreRows ∨ y.val=board.rows at core
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2800000 in
private theorem paid_field_birth (a : Attempt) (scheduled : Event.attempt a∈es) (m : Memory w)
    (row : Fin (H a).rows) (field : Fin ports)
    (raw : Fin (b).boughtRows) (room : (b).rows<2^w)
    (value' : ((rawEdge ported (b).rows a field).eval m (row.val:Word w)).val=((b).boughtIndex raw).val) :
    ∃ (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
      (slice inner : ℕ) (candidate : Fin (head).ports),
      a=.inner phase.val trial.val slice inner ∧
      (head).enum ⟨finProdFinEquiv (phase,trial),candidate⟩=raw ∧
      position v.mesh (.attempt (.outer phase.val trial.val))<position v.mesh (.attempt a) := by
  cases a with
  | outer p₀ t₀ =>
    exact (outside_core b _ raw value' (payload_raw_cases site v.mesh b (P).routes p₀ t₀ field m (row.val:Word w) room)).elim
  | inner p₀ t₀ j u =>
    obtain ⟨hp,ht,_,_⟩:=scheduled_inner v.mesh p₀ t₀ j u scheduled
    let phase : Fin (v.mesh.inject+v.mesh.cool):=⟨p₀,hp⟩
    let trial : Fin v.mesh.outerFuel:=⟨t₀,ht⟩
    let cand : Fin (head).ports:=⟨row.val,row.isLt⟩
    let old:=(head).enum ⟨finProdFinEquiv (phase,trial),cand⟩
    refine ⟨phase,trial,j,u,cand,rfl,?_,?_⟩
    · rcases purchased_raw_cases site v.mesh b (P).routes p₀ t₀ j u field m (row.val:Word w) room with core|actual
      · exact (outside_core b _ raw value' core).elim
      · have offset : old.val=birth v.mesh phase trial*(head).ports+cand.val:=by
          change cand.val+(head).ports*(finProdFinEquiv (phase,trial)).val=_
          rw [birth_ordinal,Nat.mul_comm (head).ports,Nat.add_comm]
        have got:= (b).originalProbe_read (head).ports (birth v.mesh phase trial) .row m
          (row.val:Word w) cand rfl
        have literal : ((rawEdge ported (b).rows (.inner p₀ t₀ j u) field).eval m (row.val:Word w))=
            (((b).boughtIndex old).val:Word w) := by
          change _=(((b).coreRows+old.val:ℕ):Word w)
          rw [offset]
          exact actual.trans got
        rw [literal,Fin.val_cast_of_lt (((b).boughtIndex old).isLt.trans room)] at value'
        apply Fin.ext
        change (b).coreRows+old.val=(b).coreRows+raw.val at value'
        exact Nat.add_left_cancel value'
    · change trialBase v.mesh p₀ t₀<trialBase v.mesh p₀ t₀+1+j*sliceSize v.mesh+u
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2800000 in
/-- The paid packet's own original field and ball locate the exact birth. This
includes committed, uncommitted, and padded packet rows. -/
theorem paid_direct_birth (a : Attempt) (scheduled : Event.attempt a∈es) (m : Memory w)
    (hdr : (H a).Loaded m) (fields : ports≤2^w) (room : (b).rows<2^w)
    (i : Fin (f a).pricedArea.occurrences) (raw : Fin (b).boughtRows)
    (hit : ((gs a).edge.eval m (i.val:Word w)).val=((b).boughtIndex raw).val) :
    ∃ (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
      (slice inner : ℕ) (candidate : Fin (head).ports),
      a=.inner phase.val trial.val slice inner ∧
      (head).enum ⟨finProdFinEquiv (phase,trial),candidate⟩=raw ∧
      position v.mesh (.attempt (.outer phase.val trial.val))<position v.mesh (.attempt a) := by
  let en:=finCongr (v.occurrence_count P h width a) i
  let pair:=(H a).enum.symm en
  have index : v.roleOccurrence P h width a pair.1 pair.2=i := by
    simp [roleOccurrence,pair,en]
  have hit':=((congrArg (fun t : Fin (f a).pricedArea.occurrences=>
    ((gs a).edge.eval m (t.val:Word w)).val) index).trans hit)
  have value:=v.original_direct P h width a pair.1 pair.2 m hdr fields room ((b).boughtIndex raw) hit'
  have reading : rawEdge bs (b).rows a pair.2 = rawEdge ported (b).rows a pair.2 := by
    cases a <;> rfl
  exact v.paid_field_birth h width a scheduled m pair.1 pair.2 raw room
    ((congrArg (fun expr : Expr => (expr.eval m (pair.1.val:Word w)).val) reading).symm.trans value)

theorem paid_direct_birth_resident (a : Attempt) (scheduled : Event.attempt a∈es) (m : Memory w)
    (resident : (v.publicHeader P h width).Resident m) (fields : ports≤2^w) (room : (b).rows<2^w)
    (i : Fin (f a).pricedArea.occurrences) (raw : Fin (b).boughtRows)
    (hit : ((gs a).edge.eval m (i.val:Word w)).val=((b).boughtIndex raw).val) :
    ∃ (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
      (slice inner : ℕ) (candidate : Fin (head).ports),
      a=.inner phase.val trial.val slice inner ∧
      (head).enum ⟨finProdFinEquiv (phase,trial),candidate⟩=raw ∧
      position v.mesh (.attempt (.outer phase.val trial.val))<position v.mesh (.attempt a) := by
  have eq : H a=(v.publicHeader P h width).ports.header 0 := by
    cases a <;> simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero] <;> rfl
  have hdr : (H a).Loaded m:=by rw [eq];exact resident.ports 0
  exact v.paid_direct_birth h width a scheduled m hdr fields room i raw hit

/-- A nonzero native column has a particular contributing packet occurrence. -/
theorem paid_occurrence_of_load {W edges : ℕ} (slice : PaidWidths.Slice) (m : Memory W)
    (edge : Fin edges) (positive : 0<slice.load m edge) : Nonempty (slice.Positive m edge) := by
  classical
  by_contra empty
  have zero : slice.load m edge=0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases same : (slice.edge.eval m (i.val:Word W)).val=edge.val
    · rw [ite_eq_left same]
      exact Nat.eq_zero_of_not_pos (fun paid=>empty ⟨⟨i,same,paid⟩⟩)
    · rw [ite_eq_right same]
  omega

theorem paid_direct_birth_of_load (a : Attempt) (scheduled : Event.attempt a∈es) (m : Memory w)
    (resident : (v.publicHeader P h width).Resident m) (fields : ports≤2^w) (room : (b).rows<2^w)
    (raw : Fin (b).boughtRows)
    (positive : 0<(PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (gs a)).load m ((b).boughtIndex raw)) :
    ∃ (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
      (slice inner : ℕ) (candidate : Fin (head).ports),
      a=.inner phase.val trial.val slice inner ∧
      (head).enum ⟨finProdFinEquiv (phase,trial),candidate⟩=raw ∧
      position v.mesh (.attempt (.outer phase.val trial.val))<position v.mesh (.attempt a) := by
  obtain ⟨i⟩:=paid_occurrence_of_load _ m _ positive
  exact v.paid_direct_birth_resident h width a scheduled m resident fields room i.1 raw i.2.1

/-- At a secondary endpoint the original chart never charges an acquired edge. -/
theorem paid_mate_bought_zero (a : Attempt) (scheduled : Event.attempt a∈es)
    (word : floor<2^w) (room : (b).rows<2^w) (mask mate : Expr)
    (issued : (tr a).catalystMate=some (mask,mate)) (m : Memory w) (raw : Fin (b).boughtRows) :
    (PaidWidths.paidMate (f a).pricedArea (f a).stockSource mask mate).load m ((b).boughtIndex raw)=0 := by
  apply Nat.eq_zero_of_not_pos
  intro positive
  obtain ⟨i⟩:=paid_occurrence_of_load _ m _ positive
  exact outside_core b _ raw i.2.1 (v.prior_mate_range h width a scheduled word room mask mate issued m (i.1.val:Word w))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

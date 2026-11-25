import OAI.Hierarchy.ProbeFixedWideSpillDates
import OAI.Hierarchy.ProbeFixedWideSpillOffsets
import OAI.Hierarchy.TaggedWideControlResident
import OAI.Hierarchy.ProtocolRAMRowChoiceFits
import OAI.Hierarchy.ProbeFixedWideDatedSheetFits
import OAI.Hierarchy.ProbeFixedWideTerminalFloors

namespace OAI
/-! # Bounds on every native lookup in the two spill-only chord scans -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles
open ThreeFlat.RAM DescriptorExpr

theorem from_sector_fits {W D cut : ℕ} (n original sites full only bits : ℕ) (stride site role : Bank)
    (ordinal : Expr) (op : ordinal.Fits W cut) (st : stride.Fits W cut) (here : site.Fits W cut)
    (tag : role.Fits W cut) (fullPages : ∀f,(DatedRoleSheets.bank original full (sites*D) bits f).Fits W cut)
    (onlyPages : ∀f,(DatedRoleSheets.bank original only (sites*D) bits f).Fits W cut) :
    (Side.fromSector (D:=D) n original sites full only bits stride site role ordinal).prefix.Fits W cut := by
  have rows (start : ℕ) (pg : ∀f,(DatedRoleSheets.bank original start (sites*D) bits f).Fits W cut)
      (q : Fin D) : SiteControls.RowFits (W:=W) (cut:=cut) (SiteControls.columns original start sites bits stride (.lookup site .row) q) := by
    constructor <;> apply page_fits <;> first | exact pg _ | exact st | exact ⟨here,trivial⟩
  have peer:=BoughtSockets.choose_fits_bound (w:=W) (out:=cut) (2*D) 0
    (fun j=>(SiteControls.columns original full sites bits stride (.lookup site .row) (untagRole j)).opposite)
    (.lookup role .row) (fun j=>(rows full fullPages (untagRole j)).opposite) ⟨tag,trivial⟩
  apply SiteControls.total_fits
  intro j
  exact ⟨(rows only onlyPages j).ordinal,op,
    ⟨(rows only onlyPages j).opposite,peer,(rows only onlyPages j).width,trivial⟩,trivial⟩

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets

namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical BigOperators

/-- A masked read of a role column can extend past its last real site. The two
charged control tables after the final role page supply the dyadic padding. -/
theorem SpillDates.offset_pages {T : ℕ} (z : SpillDates T) (oldWork start : ℕ) (j : Fin T)
    (prior : oldWork≤ start)
    (count : ∀i,z.original.controlColumns i=SiteControls.fieldCount z.original.roleCount) :
    let g:=z.original
    ∀a∈[z.preClip oldWork start j,g.roleStart oldWork j.succ,z.dateRole start j 1,z.dateRole start j 2],
      ∀f : Fin 3,DatedRoleSheets.sheet a g.roleWords g.physical f+ProtocolRAMPurchaseSampler.span g.roleWords≤z.endAt start := by
  intro g
  let fees:=fun i=>(g.control i).span g.sites
  have degree : g.roleCount≤SiteControls.fieldCount g.roleCount := by
    let put (i : Fin g.roleCount) : SiteControls.Field g.roleCount:=.inl (false,.inr (.inr i))
    have inj : Function.Injective put:=by intro a b eqn;simpa only [put,Sum.inl.injEq,Prod.mk.injEq,Sum.inr.injEq,true_and] using eqn
    simpa only [SiteControls.fieldCount,Fintype.card_fin] using Fintype.card_le_of_injective put inj
  have one : 1+g.roleWords≤fees j := by
    have ge : g.sites*g.roleCount ≤ g.sites*g.controlColumns j :=
      Nat.mul_le_mul_left g.sites (degree.trans_eq (count j).symm)
    change 1+g.sites*g.roleCount≤1+g.sites*g.controlColumns j+_
    omega
  have single : fees j≤∑i,fees i:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  have allFees : 1+g.roleWords≤T*stride fees:=one.trans (single.trans (Nat.le_mul_of_pos_left _ ((Nat.zero_le j.val).trans_lt j.isLt)))
  let top:=g.rolesEnd (z.roleRoot start 2)
  have guard : top+ProtocolRAMPurchaseSampler.span g.roleWords≤z.endAt start := by
    have amount:=ProtocolRAMPurchaseSampler.span_le g.roleWords
    change top+_≤top+T*stride (fun i=>(g.ballot i).span g.sites)+T*stride fees+T*stride fees
    omega
  have whole (a : ℕ) (i : Fin (T+1)) (bound : a≤z.roleRoot start 2) :=
    calc g.roleStart a i+3*g.roleSpan = a+(i.val+1)*(3*g.roleSpan) := by unfold Dated.roleStart;ring
         _ ≤ z.roleRoot start 2+(T+1)*(3*g.roleSpan) := Nat.add_le_add bound (Nat.mul_le_mul_right _ i.isLt)
  have stage (u : Fin 3) : z.roleRoot start u≤z.roleRoot start 2 := by
    change start+u.val*((T+1)*(3*g.roleSpan))≤ start+2*((T+1)*(3*g.roleSpan))
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : u.val≤2)) _
  have old : oldWork≤z.roleRoot start 2:=prior.trans (Nat.le_add_right ..)
  have phase (a : ℕ) (ha : a∈[z.preClip oldWork start j,g.roleStart oldWork j.succ,z.dateRole start j 1,z.dateRole start j 2]) :
      a+3*g.roleSpan≤top := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl
    · unfold SpillDates.preClip
      split <;> first | exact whole _ _ (stage _) | exact whole _ _ old
    · exact whole _ _ old
    · exact whole _ _ (stage _)
    · exact whole _ _ (stage _)
  intro a ha f
  have within := phase a ha
  have positive : 0<g.roleSpan:=by change 0<1+_+_;omega
  have col : f.val*g.roleSpan≤2*g.roleSpan:=Nat.mul_le_mul_right _ (by omega : f.val ≤ 2)
  change a+f.val*g.roleSpan+1+ProtocolRAMPurchaseSampler.span g.roleWords≤z.endAt start
  omega

end Hierarchy.ProtocolRAM.Calendar.WideCPU

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets HistoryRoles RoleProgram
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
open scoped Classical
local notation "native" => Native.copies

theorem wide_spill_offset_fits (h width datedROM terminalROM terminalWork oldStart newStart leftOnly rightOnly cut : ℕ)
    (size : cut<2^(Native.wordBits h (2^v.W) native)) (stock : v.wideFundedSize h width v.maxBits≤cut)
    (terminal : v.wideTerminalWorkEnd h width v.maxBits terminalWork≤cut)
    (stride : datedROM+ProtocolRAMPurchaseSampler.span (siteLast h (2^v.W) k+1)≤cut)
    (fields : let T:=v.wideTerminal h width v.maxBits terminalROM terminalWork
      let L:=(siteLast h (2^v.W) k+1)*v.widePacketDegree
      ∀s∈[oldStart,newStart,leftOnly,rightOnly],∀f : Fin 3,
        DatedRoleSheets.sheet s L T.board.old f+ProtocolRAMPurchaseSampler.span L≤cut) :
    let x:=v.wideSpillOffsetSides h width v.maxBits datedROM terminalROM terminalWork oldStart newStart leftOnly rightOnly
    x.1.prefix.Fits (Native.wordBits h (2^v.W) native) cut ∧ x.2.prefix.Fits (Native.wordBits h (2^v.W) native) cut := by
  intro x
  let b:=v.wideTerminalBoard h width v.maxBits terminalWork
  let L:=(siteLast h (2^v.W) k+1)*v.widePacketDegree
  let lo:=v.wideTerminalRankStart h width v.maxBits terminalWork
  let win:=v.wideTurnWindow h width v.maxBits terminalWork
  obtain ⟨_,rawEnd,rankEnd,winEnd,_,_⟩:=v.wide_terminal_role_floors h width v.maxBits terminalWork (terminal.trans size.le)
  have apex : lo≤cut:=rankEnd.trans (winEnd.trans terminal)
  have alloc : lo=b.endAt+3*b.old+ProtocolRAMPurchaseSampler.span b.old+ProtocolRAMPurchaseSampler.span b.edges:=rfl
  have terminalEnd : b.endAt=b.base+4*b.old+4*b.edges:=rfl
  have sized (cell : Bank) (bound : cell.base+cell.size≤cut) : cell.Fits (Native.wordBits h (2^v.W) native) cut :=
    ⟨Nat.two_pow_pos _,by omega,bound⟩
  have oldSite : (b.oldSite false).Fits (Native.wordBits h (2^v.W) native) cut := sized _ (by change b.base+0*b.old+ProtocolRAMPurchaseSampler.span b.old≤cut;omega)
  have oldRole : (b.oldRole false).Fits (Native.wordBits h (2^v.W) native) cut := by
    apply sized
    change b.base+2*b.old+ProtocolRAMPurchaseSampler.span b.old≤cut
    omega
  have newSite : (b.newSite false).Fits (Native.wordBits h (2^v.W) native) cut := by
    apply sized
    change b.base+4*b.old+0*b.edges+ProtocolRAMPurchaseSampler.span b.edges≤cut
    omega
  have newRole : (b.newRole false).Fits (Native.wordBits h (2^v.W) native) cut := by
    apply sized
    change b.base+4*b.old+2*b.edges+ProtocolRAMPurchaseSampler.span b.edges≤cut
    omega
  have table:=sized (RoleROM.bank datedROM (siteLast h (2^v.W) k+1)) stride
  have ids:=(v.wide_dated_operand_fits h width cut stock size).2
  have lookup (s : ℕ) (mem : s∈[oldStart,newStart,leftOnly,rightOnly]) (f : Fin 3) :=
    sized (DatedRoleSheets.bank b.old s L (ProtocolRAMPurchaseSampler.bits L) f) (fields s mem f)
  exact ⟨DatedSpillOffsets.from_sector_fits _ _ _ _ _ _ _ _ _ _ ids table oldSite oldRole
      (lookup _ (by simp)) (lookup _ (by simp)),
    DatedSpillOffsets.from_sector_fits _ _ _ _ _ _ _ _ _ _ trivial table newSite newRole
      (lookup _ (by simp)) (lookup _ (by simp))⟩

theorem wide_spill_offset_stage_fits (h width ell unitCost datedROM datedWork terminalROM terminalWork first : ℕ)
    (j : Fin (events v.mesh).length)
    (prior : datedWork≤v.wideSpillRankEnd h width v.maxBits first)
    (size : v.wideSpillDateEnd h width ell unitCost v.maxBits first<2^(Native.wordBits h (2^v.W) native))
    (stock : v.wideFundedSize h width v.maxBits≤v.wideSpillDateEnd h width ell unitCost v.maxBits first)
    (terminal : v.wideTerminalWorkEnd h width v.maxBits terminalWork≤v.wideSpillDateEnd h width ell unitCost v.maxBits first)
    (stride : datedROM+ProtocolRAMPurchaseSampler.span (siteLast h (2^v.W) k+1)≤
      v.wideSpillDateEnd h width ell unitCost v.maxBits first) :
    let z:=v.wideSpillDates h width ell unitCost v.maxBits first
    let r:=v.wideSpillRankEnd h width v.maxBits first
    let x:=v.wideSpillOffsetSides h width v.maxBits datedROM terminalROM terminalWork
      (z.preClip datedWork r j) (z.original.roleStart datedWork j.succ) (z.dateRole r j 1) (z.dateRole r j 2)
    x.1.prefix.Fits (Native.wordBits h (2^v.W) native) (z.endAt r) ∧
      x.2.prefix.Fits (Native.wordBits h (2^v.W) native) (z.endAt r) := by
  intro z r x
  apply v.wide_spill_offset_fits h width datedROM terminalROM terminalWork _ _ _ _ _ size stock terminal stride
  exact z.offset_pages datedWork r j prior (v.wide_spill_columns h width ell unitCost)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI

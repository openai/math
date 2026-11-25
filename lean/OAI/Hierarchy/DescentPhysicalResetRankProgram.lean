import OAI.Hierarchy.DescentResetRankFunctions
import OAI.Hierarchy.DescentDatedWholeOperands
import OAI.Hierarchy.DescentResetRankedWindows
import OAI.Hierarchy.DescentResetControlRegisterRun
import OAI.Hierarchy.DescentPhysicalRankPortPhase

namespace OAI
/-! # The reset suffix from genuine prior candidate rows to all seven operand fields -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (v : ResetOutput)
local notation "A" => v.receiver

structure RankInputs where
  ports : Ports 4
  before : ℕ→ℕ→Bool
  sourceSlot : Fin (A).candidates→ℕ→ℕ
  header : Fin (A).blocks→Fin (A).candidates→Expr
  original : Fin (A).blocks→Fin (A).candidates→Expr

/-- The printed rank controller depends only on the calendar and the earlier register
and cable banks. Every unclaimed local cable slot runs these same two lookups. -/
def calendarRankInputs (degree k n height common cap programSize : ℕ)
    (ports : Ports 4) (header original : Fin (A).blocks→Fin (A).candidates→Expr) : v.RankInputs :=
  ⟨ports,DescentResetLocalRoster.publicBefore degree k n height common cap programSize,
    fun j=>DescentResetLocalRoster.publicSourceSlot degree k n height cap programSize (A).candidates j.val,
    header,original⟩

def rankBook (u : v.RankInputs) (base : ℕ) :
    DescentResetRankedWindows.Layout (A).blocks (A).candidates :=
  ⟨v.rankPortEnd base,v.assemblerBits,v.ticketBits,(A).lanes,(A).hosts,(A).groups,
    v.rankPorts base,u.before,u.sourceSlot,u.header,u.original⟩

variable (u : v.RankInputs) (s : v.OperandInputs) (base degree : ℕ)
local notation "L" => v.rankBook u base
def renderFromRanks : v.RenderInputs :=⟨u.header,(L).finalRank⟩
local notation "r₀" => v.renderFromRanks u base

theorem rank_boundaries : (L).ticketBase=v.pairEnd base ∧ (L).seekBase=v.ticketEnd base ∧
    (L).rankBase=v.seekEnd base ∧ (L).endAddress=v.rankEnd base := ⟨rfl,rfl,rfl,rfl⟩

variable (bank : v.setup.Sources) (laws : v.setup.Laws)

def controlPhase (w : ℕ) :=
  v.controlRegisters.phase (v.controlFloor base) (v.actor.scene (v.middle.stop base)) bank.count bank.inverse w

def ControlRoom (w : ℕ) : Prop :=
  DescentVenueQuantityPlanes.Room v.controlRegisters.dims
    (DescentVenueQuantityPlanes.State.layout v.controlRegisters.dims (v.controlFloor base)
      (v.actor.scene (v.middle.stop base)) bank.count bank.inverse) 0 w

/-- The dated actor bank and the two measured directory banks supply the control scan. -/
theorem control_room {w : ℕ}
    (scene : (v.actor.scene (v.middle.stop base)).Fits w (v.controlFloor base))
    (count : bank.count.Fits w (v.controlFloor base)) (inv : bank.inverse.Fits w (v.controlFloor base))
    (oldRows : v.controlRegisters.dims.shapes*(v.controlRegisters.dims.oldHosts*
      DescentSIMDLookup.chunks (v.controlRegisters.dims.groups*v.controlRegisters.dims.blocks)
        v.controlRegisters.dims.oldLanes) ≤ (v.actor.scene (v.middle.stop base)).size)
    (host : v.controlRegisters.dims.hosts≤2^w) (lanes : 0<v.controlRegisters.dims.lanes)
    (blocks : 0<v.controlRegisters.dims.blocks) (roof : v.operandFloor base<2^w) :
    v.ControlRoom base bank w := by
  change v.controlRegisters.endAddress (v.controlFloor base)<2^w at roof
  have afterOutput := v.controlRegisters.size (v.controlFloor base)
  exact DescentVenueQuantityPlanes.State.room v.controlRegisters.dims (v.controlFloor base)
    (v.actor.scene (v.middle.stop base)) bank.count bank.inverse scene count inv
    (by simpa only [Nat.mul_assoc] using oldRows) (Nat.zero_le _) (Nat.two_pow_pos _)
    host lanes blocks (by change v.controlRegisters.first (v.controlFloor base)<2^w; omega)

/-- Earlier signed rows and their selected expressions remain readable after the actor controls run. -/
theorem control_source {w H G M d : ℕ} (m : Memory w) (e : Expr)
    (value : Fin H→Fin G→DescentSIMDLookup.Cell d) (read : DescentPackedZip.Source e value M m)
    (fit : e.Fits w (v.controlFloor base)) (bounds : v.ControlRoom base bank w)
    (space : v.operandFloor base<2^w) :
    DescentPackedZip.Source e value M ((v.controlPhase base bank w).image m) := by
  have frame:=(v.controlRegisters.any (v.controlFloor base) (v.actor.scene (v.middle.stop base))
    bank.count bank.inverse m bounds space).2
  intro p
  exact (ProtocolRAM.eval_below e _ m _ fit (fun i hi=>frame i (.inl hi))).trans (read p)

def rankedReturn (w : ℕ) :=
  (v.rankPortPhase base w).program.seq (((L).program w).seq ((v.renderProgram r₀ base degree w).seq
    ((v.controlPhase base bank w).program.seq (v.wholeOperandProgram s r₀ base w bank laws))))
def rankedTime (w : ℕ) := (v.rankPortPhase base w).ticks+((L).time+(v.renderTicks r₀ base degree+
    ((v.controlPhase base bank w).ticks+v.wholeOperandTicks s r₀ base w bank laws)))
def rankedMemory {w : ℕ} (m : Memory w) :=
  v.wholeOperandMemory s r₀ base bank laws
    ((v.controlPhase base bank w).image (v.renderMemory r₀ base degree ((L).memory ((v.rankPortPhase base w).image m))))

private theorem five_phases {w : ℕ}
    {p q r s t : Procedure w} {tp tq tr ts tt lo a b c d hi : ℕ}
    {m m₁ m₂ m₃ m₄ m₅ : Memory w}
    (pq : lo ≤ a) (qr : a ≤ b) (rs : b ≤ c) (st : c ≤ d) (hi₀ : d ≤ hi)
    (ep : p.Exec m m₁ tp) (eq : q.Exec m₁ m₂ tq) (er : r.Exec m₂ m₃ tr)
    (es : s.Exec m₃ m₄ ts) (et : t.Exec m₄ m₅ tt)
    (fp : ∀ i, i < lo ∨ a ≤ i → m₁ i = m i) (fq : ∀ i, i < a ∨ b ≤ i → m₂ i = m₁ i)
    (fr : ∀ i, i < b ∨ c ≤ i → m₃ i = m₂ i) (fs : ∀ i, i < c ∨ d ≤ i → m₄ i = m₃ i)
    (ft : ∀ i, i < d ∨ hi ≤ i → m₅ i = m₄ i)
    (cp : CheapCode p) (cq : CheapCode q) (cr : CheapCode r) (cs : CheapCode s) (ct : CheapCode t) :
    (p.seq (q.seq (r.seq (s.seq t)))).Exec m m₅ (tp+(tq+(tr+(ts+tt)))) ∧
    (∀ i, i < lo ∨ hi ≤ i → m₅ i = m i) ∧ CheapCode (p.seq (q.seq (r.seq (s.seq t)))) := by
  refine ⟨?_, ?_, @cheap_seq _ _ _ cp (@cheap_seq _ _ _ cq (@cheap_seq _ _ _ cr (@cheap_seq _ _ _ cs ct)))⟩
  · exact Procedure.Exec.then ep (Procedure.Exec.then eq (Procedure.Exec.then er (Procedure.Exec.then es et)))
  intro i outside
  exact (ft i (by omega)).trans ((fs i (by omega)).trans ((fr i (by omega)).trans
    ((fq i (by omega)).trans (fp i (by omega)))))

set_option maxHeartbeats 500000 in
theorem ranked_any {w : ℕ} (m : Memory w) (width : (A).signedBits=v.assemblerBits)
    (portInputs : v.RankPortRoom base w) (reads : (L).Previous w) (controls : v.ControlRoom base bank w) (placed : v.setup.Ready bank w (v.operandFloor base))
    (issued : v.OperandEarly s r₀ w base) (room : v.endAddress base<2^w) :
    (v.rankedReturn u s base degree bank laws w).Exec m (v.rankedMemory u s base degree bank laws m) (v.rankedTime u s base degree bank laws w) ∧
    (∀i,i<v.candidateEnd base ∨ v.endAddress base≤ i → v.rankedMemory u s base degree bank laws m i=m i) ∧
    CheapCode (v.rankedReturn u s base degree bank laws w) := by
  let low:=v.rankEnd base
  let mid:=(A).rendered (v.fieldsEnd base)
  have room₀ : low ≤ mid :=
    ((Nat.le_add_right (v.rankEnd base) _).trans (Nat.le_add_right (v.fieldsEnd base) _)).trans
      (Nat.le_add_right _ _)
  have start : mid≤v.operandFloor base := by
    change mid≤v.controlRegisters.endAddress mid
    rw [v.controlRegisters.translated mid]
    exact Nat.le_add_right ..
  have beforeSetup : v.operandFloor base≤v.operandStart base := by
    refine le_trans ?_ (v.keep_before base)
    change v.operandFloor base≤v.setup.endAddress (v.operandFloor base)
    rw [v.setup.affine]
    exact Nat.le_add_right ..
  obtain ⟨afterSetup,afterLookup⟩:=v.operand_order base
  have endFits : v.operandFloor base≤v.endAddress base := beforeSetup.trans (afterSetup.trans afterLookup)
  have room₁ := start.trans endFits
  have rfit : (L).endAddress<2^w:=(room₀.trans room₁).trans_lt room
  have rankStart : v.rankPortEnd base≤low:=by
    obtain ⟨a,b,c,d⟩:=(L).ordered
    exact ((a.trans b).trans c).trans d
  obtain ⟨portRun,portFrame⟩:=v.rankPort_any base w m portInputs
  let portMemory:=(v.rankPortPhase base w).image m
  have lstage:=(L).any portMemory reads rfit
  have fit₀ : ∀x j,(u.header x j).Fits w (v.rankEnd base) := by
    intro x j
    obtain ⟨h,i,k,o⟩:=(L).ordered
    exact ProtocolRAMGeneratedWrite.fits_mono _ (((h.trans i).trans k).trans o) (reads.header x j)
  have middle:=v.render_any r₀ base degree ((L).memory portMemory) width fit₀ ((L).finalRank_fits reads rfit) (room₁.trans_lt room)
  let rendered:=v.renderMemory r₀ base degree ((L).memory portMemory)
  let registers:=v.controlPhase base bank w
  obtain ⟨regRun,regFrame⟩:=v.controlRegisters.any (v.controlFloor base) (v.actor.scene (v.middle.stop base))
    bank.count bank.inverse rendered controls (endFits.trans_lt room)
  have last:=v.wholeOperand_any s r₀ base (registers.image rendered) bank laws placed issued room
  let finish := v.wholeOperands s r₀ base w bank laws
  have complete := @five_phases w (v.rankPortPhase base w).program ((L).program w)
    (v.renderProgram r₀ base degree w) registers.program finish.program
    (v.rankPortPhase base w).ticks (L).time (v.renderTicks r₀ base degree) registers.ticks
    finish.time (v.candidateEnd base) (v.rankPortEnd base) low mid (v.operandFloor base) (v.endAddress base)
    m portMemory ((L).memory portMemory) rendered (registers.image rendered) (finish.image (registers.image rendered))
    (v.rankPort_after base) rankStart room₀ start endFits
    (@portRun) (@lstage.1) (@middle.1) (@regRun) (@last.1)
    portFrame lstage.2.1 middle.2.1 regFrame last.2.1
    (@(v.rankPortPhase base w).cheap) (@lstage.2.2) (@middle.2.2) (@registers.cheap) (@last.2.2)
  dsimp only [rankedReturn,rankedTime,rankedMemory]
  exact complete

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

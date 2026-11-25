import OAI.Hierarchy.DescentResetPrivateMaskVolume
import OAI.Hierarchy.DescentResetEvidenceCoefficient
import OAI.Hierarchy.DescentResetSelectedRootRooms
import OAI.Hierarchy.DescentResetClippedDatePrice

namespace OAI
/-! Charge the private mask period at the selected root operand width of this reset date. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler TerminalScale DescentSixParty DescentSIMDLookup DescentResetLocalRoster
open DescentDenseHostOrder DescentHostDegree
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
  {n d : ℕ} (board : NonlinearExpanders.Graph n d) (k tail i p f g drift degree h e prev nextM C packet : ℕ)
  (prior : Prior) (base : ℕ)
local notation "v" => fromBoard G S board k tail i p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "A" => (v).privateShape
local notation "K" => 2^k
local notation "height" => GroupStage.depthBound prior.venue.degree n f g

def privateMaskLead (n d ht cables : ℕ) :=
  50000*(cables+1)*(12*(2^n+2)*cables+1)*(2*CandidateFront.rosterFactor n d ht+1)*3

theorem private_mask_factor (J rate : ℕ) (bounded : K ≤ scale J rate) :
    (A).volumeFactor ≤ privateMaskLead n d height (DescentResetCableSlots.cableCap board height)*scale J (3*rate) :=by
  let U:=scale J rate
  let wires:=DescentResetCableSlots.cableCap board height
  let sh:=CandidateFront.rosterFactor n d height
  have positive : 1 ≤ U:=Nat.two_pow_pos _
  have roots : rootSlots k (2^n)≤(2*(2^n+2))*U:=by
    unfold rootSlots
    rw [pow_succ]
    calc 2^k*2+2^k*2*(2^n+1) = (2*(2^n+2))*2^k :=by ring
         _ ≤ _:=Nat.mul_le_mul_left _ bounded
  have fieldCount : (A).fields+1≤(12*(2^n+2)*wires+1)*U:=by
    change 2*(rootSlots k (2^n)*wires)*3+1 ≤ _
    calc _≤2*((2*(2^n+2)*U)*wires)*3+U:=by gcongr
         _=_:=by ring
  have shapes : (A).shapes+1≤(2*sh+1)*U:=by
    have bound:=roster_bound board k height
    change (roster board k height).card ≤ sh*2^(k+1) at bound
    change (roster board k height).card+1 ≤ _
    rw [pow_succ] at bound
    calc _ ≤ sh*(U*2)+U:=Nat.add_le_add (bound.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ bounded))) positive
         _=_:=by ring
  have blocks : (A).blocks+2≤3*U:=by change 2^k+2≤3*U;omega
  have cube : U^3=scale J (3*rate):=by
    dsimp [U,scale];rw [←pow_mul];congr 1;ring
  change 50000*(wires+1)*((A).fields+1)*((A).shapes+1)*((A).blocks+2) ≤ _
  calc _≤50000*(wires+1)*((12*(2^n+2)*wires+1)*U)*((2*sh+1)*U)*(3*U):=by gcongr
       _=privateMaskLead n d height wires*U^3:=by unfold privateMaskLead;dsimp [sh];ring
       _=_:=by rw [cube]

theorem private_mask_volume (rate : ℕ) (live : i < S.length) (radix : S.radix=2^k)
    (blocks : K ≤ scale S.height rate)
    (room : ∀t,t∈(v).rootUnits ∨ t∈(v).receiverUnits→t*2^e ≤ h/2) :
    (A).periodPrice≤(privateMaskLead n d height (DescentResetCableSlots.cableCap board height)*scale S.height (3*rate))*
      receiptArea h (S.hostSize i) (chunks (S.groupCount i) (2^e)):=by
  have one:=room ((v).front.stemField+2) (.inl (by simp [rootUnits]))
  have small : 2^e ≤ h:=((Nat.le_mul_of_pos_left _ (by omega : 0<(v).front.stemField+2)).trans one).trans (Nat.div_le_self ..)
  have panel:=room ((v).front.privateBits*((v).front.wireCap*5)) (.inl (by simp [rootUnits]))
  have old:=room (v).sheets.metaBits (.inl (by simp [rootUnits]))
  have fresh:=room ((v).sheets.metaBits*(v).sheets.blocks) (.inr (by simp [receiverUnits]))
  have volume:=(A).period_volume h rfl (Nat.two_pow_pos e) (Nat.two_pow_pos k) small panel old fresh
  have count : S.groupCount (i+1)*2^k=S.groupCount i:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits live radix)).symm
  change (A).periodPrice≤(A).volumeFactor*receiptArea h (S.hostSize i) (chunks (S.groupCount (i+1)*2^k) (2^e)) at volume
  rw [count] at volume
  exact volume.trans (Nat.mul_le_mul_right _ (private_mask_factor G S board k tail i p f g drift degree h e prev nextM C packet prior base S.height rate blocks))
end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentPackedWalsh
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false

private theorem equal_group_width {x y : ResetOutput} (roots : x.rootUnits = y.rootUnits)
    (receivers : x.receiverUnits = y.receiverUnits) : x.groupWidth = y.groupWidth := by
  unfold ResetOutput.groupWidth; rw [roots,receivers]

theorem selected_private_mask_invoice {F : Type} [Field F] (G : PoweredGadget F)
    {n d : ℕ} (board : NonlinearExpanders.Graph n d) (D f g localRate receiver ratio saving : ℕ) :
    ∃lead exponent : ℕ,∀ᶠ h : ℕ in atTop,∀ (S : AtomSchedule) (k tail i p drift degree nextM C packet
      oldLanes primitiveLanes printedBits w : ℕ) (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ),
      let prev:=resetCut S k tail p f h i
      let date:=PhysicalReset.selected G S board k tail i p f g drift degree h prev nextM C packet
        oldLanes primitiveLanes printedBits old io.wire io.roster floor
      let v:=date.successor
      let b:=S.localWalshBits p (S.groupWidth k tail i+k) f (quota S.rounds)
      S.baseGroups=2^tail→S.radix=2^k→i < S.length→ old.degree=D→
      8*b ≤ h→8*v.groupWidth ≤ h→2^k ≤ scale S.height localRate→b ≤ scale S.height localRate→
      v.groupWidth ≤ scale S.height receiver→S.height ≤ Nat.log 2 h→2^h ≤ S.initialSites→w ≤ ratio*h→
      v.privateShape.periodPrice*w ≤ S.hostSize i*h*(lead*scale S.height exponent)+
        S.hostSize i*(S.groupCount i*S.radix)*(lead*scale S.height exponent)+S.initialSites/(2^S.height)^saving :=by
  let ht:=GroupStage.depthBound D n f g
  let c:=ResetOutput.privateMaskLead n d ht (DescentResetCableSlots.cableCap board ht)
  obtain ⟨lead,ex,quoted⟩:=clipped_date_price c (3*localRate) 3 localRate receiver ratio saving
  refine ⟨lead,ex,?_⟩
  filter_upwards [quoted] with h pay
  intro S k tail i p drift degree nextM C packet oldLanes primitiveLanes printedBits w old io floor prev date v b
    baseGroups radix live degreeAt bRoom rootRoom blocks bits wide age ambient word
  let e:=PhysicalReset.receiverCut G S board k tail i p f g drift degree h prev nextM C packet
    oldLanes primitiveLanes printedBits old
  let pr:=ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old
  let at₀:=date.rebased (date.stageStart floor)
  have inv := PhysicalReset.selected_inventory G S board k tail i p f g drift degree h prev nextM C
    packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have width := equal_group_width inv.1 inv.2.1
  let out := ResetOutput.fromBoard G S board k tail i p f g drift degree h e prev (2^e) nextM C packet pr at₀
  have outputEq : v = out := PhysicalReset.named_successor G S board k tail i p f g drift degree h
    e prev (2^e) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have exp_eq : v.exponent prev prev (S.groupWidth k tail (i+1)) h = e := by
    unfold ResetOutput.exponent
    rw [show v.groupWidth = _ from width]; rfl
  have volume := ResetOutput.private_mask_volume G S board k tail i p f g drift degree h e prev nextM C
    packet pr at₀ localRate live radix blocks (fun x used => by
      change x∈out.rootUnits ∨ x∈out.receiverUnits at used
      rw [←outputEq] at used
      have read := v.operand_room prev prev (S.groupWidth k tail (i+1)) h rootRoom used
      rwa [exp_eq] at read)
  change out.privateShape.periodPrice ≤ _ at volume
  rw [←outputEq] at volume
  have volume' : v.privateShape.periodPrice ≤ c*TerminalScale.scale S.height (3*localRate)*
      ResetOutput.receiptArea h (S.hostSize i) (chunks (S.groupCount i) (2^e)):=by
    dsimp only [c,ht]
    rw [←degreeAt]
    exact volume
  let b₀:=S.groupWidth k tail i
  have next : S.groupWidth k tail (i+1)=b₀-k :=by
    have step:=ResetOutput.next_difference S k tail i live
    dsimp only [b₀];omega
  have bPos : 0 < b := by dsimp only [b,AtomSchedule.localWalshBits,DescentWalshPrecision.bits];omega
  have rows : chunks (2^b₀) (2^e)*h≤(2+2^k)*h+2^b₀*(32*2^k*b+16*v.groupWidth):=by
    rw [←exp_eq]
    rw [next]
    exact v.boundary_rows b₀ k h b bPos bRoom rootRoom
  rw [←S.group_power baseGroups radix i] at volume' ⊢
  exact pay S.height (S.hostSize i) (2^b₀) S.radix S.initialSites (c*TerminalScale.scale S.height (3*localRate))
    (2^k) b v.groupWidth (chunks (2^b₀) (2^e)) w v.privateShape.periodPrice age ambient le_rfl
    blocks bits wide word rows volume'
    (by rw [radix];exact Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI

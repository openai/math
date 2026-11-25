import OAI.Hierarchy.DescentDatedOperandSignedHeads
import OAI.Hierarchy.DescentDatedOperandHeadShape
import OAI.Hierarchy.DescentOrdinaryHeadRetile

namespace OAI
/-! # Read the five original signed source families at the ordinary resolver's pitch -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (floor : ℕ)
set_option hygiene false
local notation "W₀" => v.wideHeads
local notation "N₀" => v.narrowHeads
local notation "start₀" => v.operandHeaderEnd floor

set_option hygiene true

def wideHead (c : v.SignedChart) (key : v.WideHead) : Expr :=
  match key with
  | .inl (x,f,i) => v.oldSlotHead floor x f i
  | .inr (.inl (x,f,i)) => v.anchorHead floor x f i
  | .inr (.inr (x,f,i)) => v.signedRawHead floor c x f i

def narrowHead (key : v.NarrowHead) : Expr :=
  match key with
  | .inl i => v.previousPathHead floor i
  | .inr p => v.localRankHead floor p

def wideHeadSource (c : v.SignedChart) (i : Fin (W₀).n) :=v.wideHead floor c (v.wideHeadNumber.symm i)
def narrowHeadSource (i : Fin (N₀).n) :=v.narrowHead floor (v.narrowHeadNumber.symm i)

def headRankStart :=(W₀).endAddress start₀
def headTransferEnd :=(N₀).endAddress (v.headRankStart floor)
def headTransferPhase (c : v.SignedChart) (w : ℕ) :=
  ((W₀).phase start₀ (v.wideHeadSource floor c) w).seq
    ((N₀).phase (v.headRankStart floor) (v.narrowHeadSource floor) w)

theorem head_transfer_span : v.headTransferEnd floor=start₀+v.headTransferWords :=by
  rw [headTransferEnd,(N₀).translated,headRankStart,(W₀).translated,headTransferWords,Nat.add_assoc]

def wideWord (key : v.WideHead) : Expr:=.lookup ((W₀).bank start₀ (v.wideHeadNumber key)) .row
def narrowWord (key : v.NarrowHead) : Expr:=.lookup ((N₀).bank (v.headRankStart floor) (v.narrowHeadNumber key)) .row

def transferredOld (x f i) :=v.wideWord floor (.inl (x,f,i))
def transferredAnchor (x f i) :=v.wideWord floor (.inr (.inl (x,f,i)))
def transferredRaw (x f i) :=v.wideWord floor (.inr (.inr (x,f,i)))
def transferredPath (i) :=v.narrowWord floor (.inl i)
def transferredRank (p) :=v.narrowWord floor (.inr p)

variable (c : v.SignedChart) {w : ℕ} (m : Memory w)
  (wide : ∀key,(v.wideHead floor c key).Fits w start₀)
  (narrow : ∀key,(v.narrowHead floor key).Fits w start₀)
  (room : v.headTransferEnd floor<2^w)
set_option hygiene false
local notation "middle₀" => v.headRankStart floor
local notation "a₀" => (W₀).phase start₀ (v.wideHeadSource floor c) w
local notation "b₀" => (N₀).phase middle₀ (v.narrowHeadSource floor) w
local notation "done₀" => (v.headTransferPhase floor c w).image m

set_option hygiene true

include wide narrow room in
theorem head_transfer_any : (v.headTransferPhase floor c w).Runs m ∧
    ∀i,i< start₀ ∨ v.headTransferEnd floor≤ i → done₀ i=m i :=by
  have first:=(W₀).base_le start₀
  have last:=(N₀).base_le middle₀
  have a:=(W₀).any start₀ (v.wideHeadSource floor c) m (fun i=>wide _) (last.trans_lt room)
  have b:=(N₀).any middle₀ (v.narrowHeadSource floor) ((a₀).image m)
    (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ first (narrow _)) room
  refine ⟨NativePhase.seq_runs _ _ m a.1 b.1,?_⟩
  intro i apart
  exact (b.2 i (apart.imp_left (·.trans_le first))).trans (a.2 i (apart.imp_right (last.trans ·)))

include room in
theorem wide_word_fits (key : v.WideHead) : (v.wideWord floor key).Fits w (v.headTransferEnd floor) :=by
  have next:=(N₀).base_le middle₀
  have bank:=((W₀).placed start₀ (next.trans_lt room) (v.wideHeadNumber key)).1
  exact ⟨⟨bank.1,bank.2.1,bank.2.2.trans next⟩,trivial⟩

include room in
theorem narrow_word_fits (key : v.NarrowHead) : (v.narrowWord floor key).Fits w (v.headTransferEnd floor) :=
  ⟨((N₀).placed middle₀ room (v.narrowHeadNumber key)).1,trivial⟩

include wide narrow room in
theorem wide_word_source (key : v.WideHead)
    (value : Fin (W₀).hosts→Fin (W₀).groups→Cell (W₀).bits) (positive : 0<(W₀).before)
    (held : Source (v.wideHead floor c key) value (W₀).before m) {H : ℕ} (bound : H≤(W₀).hosts) :
    Source (v.wideWord floor key) ((W₀).restrict bound value) (W₀).after done₀ :=by
  have first:=(W₀).base_le start₀
  have cap:=((N₀).base_le middle₀).trans_lt room
  have direct : Source (v.wideHeadSource floor c (v.wideHeadNumber key)) value (W₀).before m :=by
    simpa only [wideHeadSource,Equiv.symm_apply_apply] using held
  have read:=(W₀).source start₀ (v.wideHeadSource floor c) m (fun i=>wide _) cap
    (v.wideHeadNumber key) value positive direct bound
  have next:=(N₀).any middle₀ (v.narrowHeadSource floor) ((a₀).image m)
    (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ first (narrow _)) room
  have early : (v.wideWord floor key).Fits w middle₀:=
    ⟨((W₀).placed start₀ cap (v.wideHeadNumber key)).1,trivial⟩
  intro row_
  exact (eval_below _ _ _ _ early (fun i hi=>next.2 i (.inl hi))).trans (read row_)

include wide narrow room in
theorem narrow_word_source (key : v.NarrowHead)
    (value : Fin (N₀).hosts→Fin (N₀).groups→Cell (N₀).bits) (positive : 0<(N₀).before)
    (held : Source (v.narrowHead floor key) value (N₀).before m) {H : ℕ} (bound : H≤(N₀).hosts) :
    Source (v.narrowWord floor key) ((N₀).restrict bound value) (N₀).after done₀ :=by
  have first:=(W₀).base_le start₀
  have cap:=((N₀).base_le middle₀).trans_lt room
  have previous:=(W₀).any start₀ (v.wideHeadSource floor c) m (fun i=>wide _) cap
  have direct : Source (v.narrowHeadSource floor (v.narrowHeadNumber key)) value (N₀).before ((a₀).image m) :=by
    simp only [narrowHeadSource,Equiv.symm_apply_apply]
    intro row_
    exact (eval_below _ _ _ _ (narrow key) (fun i hi=>previous.2 i (.inl hi))).trans (held row_)
  exact (N₀).source middle₀ (v.narrowHeadSource floor) ((a₀).image m)
    (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ first (narrow _)) room
    (v.narrowHeadNumber key) value positive direct bound
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

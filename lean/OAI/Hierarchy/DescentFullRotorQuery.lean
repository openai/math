import OAI.Hierarchy.DescentRotorReceiverOperand

namespace OAI
/-! # The zero-preserving full receiver query as an actual preceding-bank source -/
namespace Hierarchy.DescentFullRotorQuery
open DescentRotorOperandTicket DescentRotorCandidateIssue DescentResetHostSize DescentResetLocalRoster
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open DescentPacking.PackedMatch.Local.Gather DescentSharedCableNames
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {n h r H G M w field : ℕ} (board : NonlinearExpanders.Graph n h)
local notation "Q" => DescentCommonPalette.rotor board

def publicCount (Ht r Y oldCap : ℕ) :=
  2*(2^r*(2*oldCap))+1+2*(rootSlots r Y*(Y+2^Ht))

theorem publicCount_mono (Ht r Y : ℕ) {x y : ℕ} (h : x≤y) : publicCount Ht r Y x≤publicCount Ht r Y y := by
  unfold publicCount
  gcongr

def slots (Ht r Y field : ℕ) := publicCount Ht r Y (2^field)+bound board Ht r Y

def query (Ht packet f m address : ℕ) (s : Bool) (key : Code r) (e : (Q).Edge) (x : Fin 3→Cell field) :
    Cell (Packed.bits (slots board Ht r (2^n) field)) :=
  if (x 1).val=key.val.1+1 ∧ (x 2).val%2=0 ∧ address<DescentRecordedRotorLayers.layers n packet f (x 0).val*m then
    Packed.token (some ⟨publicCount Ht r (2^n) (x 0).val+(candidate board Ht r (2^n) s key e).val,
      Nat.add_lt_add_of_le_of_lt (publicCount_mono _ _ _ (x 0).isLt.le) (bounded board Ht r (2^n) s key e)⟩)
  else 0

theorem zero (Ht packet f m address : ℕ) (s : Bool) (key : Code r) (e : (Q).Edge) (x : Fin 3→Cell field)
    (miss : ¬((x 1).val=key.val.1+1 ∧ (x 2).val%2=0 ∧ address<DescentRecordedRotorLayers.layers n packet f (x 0).val*m)) :
    query board Ht packet f m address s key e x=0 := by simp [query,miss]

/-- One read of each of the three previous banks, then the mounted fixed table. The final
    expression feeds the bounded candidate lookup directly, even for padded receiver rows. -/
theorem issue (Ht packet f m address : ℕ) (s : Bool) (key : Code r) (e : (Q).Edge)
    (tables : Fin 3→Tables) (reads : Fin 3→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 3→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*3) (Packed.bits (slots board Ht r (2^n) field)) M H G w out.base)
    (rom : resident (query board Ht packet f m address s key e ∘ (encode field 3).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*3)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>query board Ht packet f m address s key e (x a g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words (query board Ht packet f m address s key e) tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentFullRotorQuery

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


open DescentResetLocalRoster DescentRotorOperandTicket
local notation "r" => (Z).k-(T).commonDepth
local notation "sz" => 2^(Z).n



theorem issued_local_query {p₀ field : ℕ} (proof : B.Recorded p₀) (u : Host) (s : Bool) (g₀ : (placement).Good)
    (e : (DescentCommonPalette.rotor (Z).graph).Edge) (m : ℕ) (x : Fin 3→DescentSIMDLookup.Cell field)
    (capRead : (x 0).val=input.placement.cap) (chosen : (x 1).val=((Z).goodLabel T g₀).val.1+1 ∧ (x 2).val%2=0)
    (active : DescentResetLocalRoster.active (blocks B) u (privateWire B (goodOccurrence B s g₀ e)))
    (layer : Fin ((Z).circuit s g₀).layers) (batch : Fin m) :
    (DescentFullRotorQuery.query (Z).graph height (Z).width f m (layer.val*m+batch.val) s ((Z).goodLabel T g₀) e x).val=
      (localRoster B u ⟨privateWire B (goodOccurrence B s g₀ e),active⟩).val+1 := by
  have levels:=(DescentRecordedRotorLayers.from_prior_cap B proof s g₀ _ capRead).1
  have room : layer.val*m+batch.val<DescentRecordedRotorLayers.layers (Z).n (Z).width f (x 0).val*m := by
    calc _<layer.val*m+m:=Nat.add_lt_add_left batch.isLt _
         _=(layer.val+1)*m:=by rw [Nat.add_mul,Nat.one_mul]
         _≤((Z).circuit s g₀).layers*m:=Nat.mul_le_mul_right m layer.isLt
         _=_:=by rw [levels]
  rw [DescentFullRotorQuery.query,ite_eq_left ⟨chosen.1,chosen.2,room⟩,rotor_receiver_row]
  change DescentFullRotorQuery.publicCount height r sz (x 0).val+_+1=_
  rw [capRead]
  simp only [DescentFullRotorQuery.publicCount,stemsCount,contactCount,B.keyWidth]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

import OAI.Hierarchy.DescentResetTrunkCompactProgram
import OAI.Hierarchy.DescentResetTrunkCompactSheet
import OAI.Hierarchy.DescentResetTrunkOriginalHeaders
import OAI.Hierarchy.DescentResetTrunkCompactWindow
import OAI.Hierarchy.DescentResetTrunkCompactActors

namespace OAI
/-! # Authentic compact reset trunk on the preceding signed stem memory -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentResetTrunkCompactPointer DescentResetFieldAssembler DescentCommonHost DescentResetTrunkIssue DescentActorRaster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "radius₁" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph radius₁ Ht
local notation "used" => Fintype.card B.next.V
local notation "grp" => S.groupCount (i+1)
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*input.placement.cap)
variable {H0 H bw b : ℕ} (previous : Fintype.card input.V≤H0)
local notation "oldRank" => (vertex).trans (Fin.castLEEmb previous)
local notation "real" => (Z).rawHostRank T oldRank
local notation "dense" => (Z).denseHostRank T oldRank
local notation "rawSize" => H0*(pal).card


open DescentPackedZip DescentSixParty.Chronology DescentDyadicSpan
variable {M : ℕ}
local notation "L₀" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "cap₀" => input.placement.cap
local notation "slot" => Fin L₀×Fin (2*cap₀)
local notation "Q" => DescentResetStemPackedIssue.count L₀ cap₀
local notation "ord₀" => DescentResetStemPackedIssue.ordinal L₀ cap₀

open ThreeFlat.RAM PhysicalProcedure

theorem host_shape_room (v : B.next.V) (degree : B.next.placement.degree+1 < 2^b) :
    ∀j,digits (hostShape B v) j<2^b:=by
  let roster:=(B.next.placement.near v).map (((Z).rawHostRank T vertex).trans Fin.valEmbedding)
  have d0:=B.next.placement.degreeBound v
  have size:=(Finset.card_map (s:=B.next.placement.near v) (((Z).rawHostRank T vertex).trans Fin.valEmbedding))
  have count (t : ℕ) : stemOrdinal (((Z).rawHostRank T vertex) v).val roster t<2^b:=by
    apply (Finset.card_filter_le ..).trans_lt
    exact (Finset.card_insert_le _ _).trans_lt ((Nat.add_le_add_right (size.le.trans d0) 1).trans_lt degree)
  have one : 1<2^b:=by omega
  cases h:trunkLabels B v with
  | none=>intro j;fin_cases j <;> simp [hostShape,h,Meta.blank,digits]
  | some p=>
    intro j
    simp only [hostShape,h]
    fin_cases j <;> first | exact count _ | exact one | exact (Bool.toNat_le _).trans_lt one | exact Nat.two_pow_pos _

/-- The concrete output of the descriptor scan uses precisely the dense
enumeration used by every measured source of the next date. -/
theorem original_rack_order (bounded : used≤H) :
    (∀v,originalTrunkRack B ((dense v).castLE bounded)=some v) ∧
      ∀h v,originalTrunkRack B h=some v→(dense v).castLE bounded=h:=by
  have code (v : B.next.V) : dense v=denseOrder B v:=Fin.ext (dense_physical B previous v)
  constructor
  · intro v
    have yes : ((dense v).castLE bounded).val<used:=(dense v).isLt
    simp only [originalTrunkRack,dite_eq_left yes]
    exact congrArg some ((congrArg (denseOrder B).symm (code v)).trans ((denseOrder B).symm_apply_apply v))
  · intro h v same
    unfold originalTrunkRack at same
    split at same
    next live=>
      have atRow:=Option.some.inj same
      have id:=congrArg (denseOrder B) atRow
      apply Fin.ext
      simpa [code] using (congrArg Fin.val id).symm
    next=>simp at same

local notation "latch" => fun base => DescentResetTrunkCompactGather.endAddress base H grp M
local notation "rhsRows" => fun base => DescentResetTrunkCompactGather.rows base H grp M
local notation "compactProgram" => fun base banks => DescentResetTrunkCompactProgram.phase bw base H rawSize grp M b banks

theorem compact_trunk_suffix (bounded : used≤H)
    (banks : DescentResetTrunkCompactPointer.Banks) (base out scalar head : ℕ) (m : Memory bw)
    (order : Room banks used H rawSize bw base)
    (dates : Measured banks (compactActorName B previous) (compactTrunkPeer B previous) m)
    (early : out+(2^k*Q)*(H*chunks grp M)≤base)
    (room : DescentResetTrunkCompactProgram.endAddress base H grp M b<2^bw)
    (degree : B.next.placement.degree+1 < 2^b) (cap : B.next.placement.cap<2^b)
    (bitsFit : b*7*M≤bw) (headFits : scalar+H+span H≤head)
    (header : DescentResetStemHeaders.outputBase H grp M (b*7) head+H*chunks grp M≤base)
    (tables : DescentResetStemHeaders.TablesOK H grp M (b*7) head m)
    (shape : ∀r : Fin H,m (scalar+r.val)=((DescentResetFieldAssembler.raw b ((originalTrunkRack B r).elim .blank (hostShape B))).val:Word bw))
    (stems : ∀(x : Fin (2^k)) (p : slot) (u : Row H grp M),
      m (out+(finProdFinEquiv (x,ord₀ (true,p))).val*(H*chunks grp M)+(row H grp M u).val)=
        ((data (incomingWord B (originalTrunkRack B) b x p) u).val:Word bw)) :
    let q:=compactProgram base banks
    let n₀:=H*chunks grp M
    let seed:=DescentResetStemHeaders.body H grp M (b*7) scalar head 0
    let src:=fun (x : Fin (2^k)) (j : Fin half)=>
      DescentResetTrunkGather.issue n₀ (rhsRows base) (incomingBank B n₀ out x j)
    q.Runs m ∧
      (∀x,(DescentResetTrunkIssue.issue (latch base) b M seed (src x)).Fits bw
        (DescentResetTrunkCompactProgram.endAddress base H grp M b)) ∧
      (∀x,Source (DescentResetTrunkIssue.issue (latch base) b M seed (src x))
        (fun (h₀ : Fin H) g₀=>DescentResetFieldAssembler.raw b (actualMeta B (originalTrunkRack B) x (trunkCandidate B) h₀ g₀)) M (q.image m)) ∧
      (∀a,a<base ∨ DescentResetTrunkCompactProgram.endAddress base H grp M b≤a→q.image m a=m a):=by
  intro q n₀ seed src
  let gather:=DescentResetTrunkCompactGather.phase bw base H rawSize grp M banks
  let posted (r : Fin H):=(originalTrunkRack B r).elim .blank (hostShape B)
  let low:=DescentResetStemHeaders.outputBase H grp M (b*7) head
  have first : base≤latch base:=DescentResetTrunkCompactProgram.grow ..
  have last : latch base≤DescentResetTrunkCompactProgram.endAddress base H grp M b:=Nat.le_add_right ..
  have pre : low≤base:=(Nat.le_add_right ..).trans header
  have enough:=(first.trans last).trans_lt room
  have ptr:=original_rack_order B previous bounded
  have ready:=compact_trunk_emitted B previous bounded (originalTrunkRack B) ptr.1 ptr.2 banks base out m order dates
    early (last.trans_lt room) stems
  have book:=DescentResetStemHeaders.runtime_word (fun (_ : Fin 1) (r : Fin H)=>DescentResetFieldAssembler.raw b (posted r))
    m (fun i r=>by fin_cases i;simpa using shape r) tables (by simpa using headFits)
    (by simpa using header.trans_lt enough) bitsFit 0
  have ins : Source seed (fun r (_ : Fin grp)=>DescentResetFieldAssembler.raw b (posted r)) M (gather.image m):=by
    intro j
    exact (eval_below seed _ m _ book.1 (fun a small=>ready.2.1 a (.inl (small.trans_le pre)))).trans (book.2 j)
  have word (v : Fin H) (j : Fin 7):digits (posted v) j<2^b:=by
    cases present : originalTrunkRack B v with
    | none=>simp only [posted,present,Option.elim_none];fin_cases j <;> exact Nat.two_pow_pos _
    | some t=>simpa only [posted,present,Option.elim_some] using host_shape_room B t degree j
  have replay:=compact_sheet B (originalTrunkRack B) posted
    (fun r v atRow=>by simp only [posted,atRow,Option.elim_some]) word (latch base) seed src (gather.image m)
    (ProtocolRAMGeneratedWrite.fits_mono _ (pre.trans first) book.1)
    (fun x j=>(ready.2.2.2 x j).1) ins (fun x j=>(ready.2.2.2 x j).2) degree cap room
  exact ⟨Procedure.Exec.then (A:=gather.program) (B:=DescentResetTrunkIssue.program (latch base) b M bw) ready.1 replay.1,replay.2.1,replay.2.2.1,
    (DescentResetTrunkCompactProgram.any base banks m order room).2⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

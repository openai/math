import OAI.Hierarchy.DescentResetTrunkCompactGather
import OAI.Hierarchy.DescentResetTrunkCompactActors

namespace OAI
/-! # The compact stem emitter and compact trunk share the original actor enumeration -/
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
local notation "r" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph r Ht
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

/-- Any later bank, including the source ticket of an incoming stem, uses
this same compact relay when sampled at a genuine emitted host. -/
theorem compact_peer_at (bounded : used≤H) (v : B.next.V) :
    pointer bounded (compactTrunkPeer B previous) ((dense v).castLE bounded)=
      (trunkLabels B v).map (fun p=>(dense p.right).castLE bounded) := by
  have real_ : ((dense v).castLE bounded).val<used:=(dense v).isLt
  have same : (⟨((dense v).castLE bounded).val,real_⟩ : Fin used)=compactActorOrder B previous v:=rfl
  simp only [pointer,dite_eq_left real_,same,compactTrunkPeer,Equiv.symm_apply_apply,Option.map_map]
  rfl

/-- The true inverse bank is required only through the last occupied compact
row, even when the outer physical pitch is larger than its reservation. -/
theorem compact_trunk_space (store : Store) (paletteBase base : ℕ)
    (inverse : store.inverse.Fits bw base) (number : store.ranks.Fits bw base)
    (usedRows : used≤ store.inverse.size) (rawRows : rawSize≤ store.ranks.size)
    (lastRank : store.ranks.base+rawSize<base)
    (turnEnd : paletteBase+3*rawSize+1≤base) (wide : H<2^bw) (room : base<2^bw) :
    Room (compactTrunkBanks (B:=B) (H0:=H0) store paletteBase) used H rawSize bw base := by
  have range:=span_ge rawSize
  have bounded:=span_le rawSize
  have end_ : paletteBase+rawSize+span rawSize≤base:=by omega
  have tableSize : span rawSize<2^bw:=(Nat.le_add_left ..).trans_lt (end_.trans_lt room)
  have one : 1<2^bw:=by omega
  refine ⟨inverse,⟨DescentDyadicSpan.span_pos _,tableSize,end_⟩,number,?_,usedRows,range,rawRows,wide,range.trans_lt tableSize⟩
  change 0<2^0 ∧ 2^0<2^bw ∧ store.ranks.base+rawSize+2^0≤base
  simpa only [pow_zero] using (show 0<1 ∧ 1<2^bw ∧ store.ranks.base+rawSize+1≤base from
    ⟨by decide,one,lastRank⟩)

theorem compact_trunk_emitted (bounded : used≤H) (rack : Fin H→Option B.next.V)
    (present : ∀v,rack ((dense v).castLE bounded)=some v)
    (named : ∀h v,rack h=some v→(dense v).castLE bounded=h)
    (banks : DescentResetTrunkCompactPointer.Banks) (base out : ℕ) (m : Memory bw) (space : Room banks used H rawSize bw base)
    (recorded : Measured banks (compactActorName B previous) (compactTrunkPeer B previous) m)
    (early : out+(2^k*Q)*(H*chunks grp M)≤base)
    (room : DescentResetTrunkCompactGather.endAddress base H grp M<2^bw)
    (emitted : ∀(x : Fin (2^k)) (p : slot) (u : Row H grp M),
      m (out+(finProdFinEquiv (x,ord₀ (true,p))).val*(H*chunks grp M)+(row H grp M u).val)=
        ((data (incomingWord B rack b x p) u).val:Word bw)) :
    let n₀:=H*chunks grp M
    let end_:=DescentResetTrunkCompactGather.endAddress base H grp M
    let rows_:=DescentResetTrunkCompactGather.rows base H grp M
    let q:=DescentResetTrunkCompactGather.phase bw base H rawSize grp M banks
    let right:=pointer bounded (compactTrunkPeer B previous)
    q.Runs m ∧ (∀a,a<base ∨ end_≤a→q.image m a=m a) ∧
      (∀u : Row H grp M,q.image m (rows_+(row H grp M u).val)=
        ((right u.1).elim n₀ (fun v=>(row H grp M (v,u.2)).val):Word bw)) ∧
      ∀(x : Fin (2^k)) (j : Fin half),
        let input:=DescentResetTrunkGather.issue n₀ rows_ (incomingBank B n₀ out x j)
        input.Fits bw end_ ∧
          Source input (fun h₀ g₀=>DescentResetFieldAssembler.raw b ((rack h₀).elim .blank (fun v=>hostStem B ((g₀,v),x) j))) M (q.image m) := by
  intro n₀ end_ rows_ q right
  have got:=DescentResetTrunkCompactGather.publish (b:=b*7) (G:=grp) (M:=M) base banks
    (compactActorName B previous) (compactTrunkPeer B previous) bounded m space recorded room
  have low : base≤DescentResetTrunkCompactGather.geometry base H:=Nat.le_add_right ..
  have before : base≤rows_:=low.trans (Nat.le_add_right ..)
  refine ⟨got.1,got.2.1,got.2.2.1,?_⟩
  intro x j
  let bank:=incomingBank B n₀ out x j
  let p : slot:=finProdFinEquiv.symm j
  let idx:=finProdFinEquiv (x,ord₀ (true,p))
  have stop : bank.base+n₀≤base:=by
    change out+idx.val*n₀+n₀≤base
    rw [Nat.add_assoc,←Nat.succ_mul]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right n₀ idx.isLt) _).trans early
  have small : bank.base≤base:=(Nat.le_add_right ..).trans stop
  have enough : bank.base+span n₀≤end_:=Nat.add_le_add_right (small.trans before) _
  have fits : bank.Fits bw end_:=⟨DescentDyadicSpan.span_pos _,(Nat.le_add_left ..).trans_lt (enough.trans_lt room),enough⟩
  have input:=got.2.2.2 bank (incomingWord B rack b x p) fits stop (span_ge n₀) (emitted x p)
  refine ⟨input.1,?_⟩
  have eqn : (fun h₀ g₀=>(right h₀).elim 0 (fun v=>incomingWord B rack b x p v g₀))=
      (fun h₀ g₀=>DescentResetFieldAssembler.raw b ((rack h₀).elim .blank (fun v=>hostStem B ((g₀,v),x) j))) :=
    funext (fun h₀=>funext (compact_trunk_gather B previous bounded rack present named x j h₀))
  exact eqn ▸ input.2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

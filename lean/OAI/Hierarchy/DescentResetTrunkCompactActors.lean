import OAI.Hierarchy.DescentResetPeerActorChart
import OAI.Hierarchy.DescentResetTrunkCompactPointer
import OAI.Hierarchy.DescentResetTrunkGathered
import OAI.Hierarchy.DescentResetActorRasterRun

namespace OAI
/-! # The compact trunk pointer on the actual reset actor directory -/
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

def compactTrunkPeer (i : Fin used) : Option (Fin used):=
  (trunkLabels B ((compactActorOrder B previous).symm i)).map (fun p=>(compactActorOrder B previous) p.right)

private def widen (v : Fin (Fintype.card input.V*(pal).card)) : Fin rawSize:=
  let t:=finProdFinEquiv.symm v
  finProdFinEquiv (t.1.castLE previous,t.2)

theorem trunk_pointer_wide (v : B.next.V) :
    DescentResetTrunkPalette.pointer (Z).graph r Ht true (real v)=(trunkLabels B v).map (fun p=>real p.right):=by
  have comm (n : Fin (Fintype.card input.V*(pal).card)) :
      DescentResetTrunkPalette.pointer (Z).graph r Ht true (widen B previous n)=
        (DescentResetTrunkPalette.pointer (Z).graph r Ht true n).map (widen B previous):=by
    obtain ⟨⟨x,y⟩,rfl⟩:=finProdFinEquiv.surjective n
    let shape:=((DescentResetTrunkPalette.order (Z).graph r Ht).symm y).val
    cases found : DescentResetTrunkPalette.flip (Z).graph true shape with
    | none=>dsimp only [shape] at found;simp [DescentResetTrunkPalette.pointer,widen,found]
    | some v=>
      dsimp only [shape] at found
      by_cases ok : v∈pal <;>simp [DescentResetTrunkPalette.pointer,widen,found,ok]
  have extend_ (v : B.next.V) : widen B previous ((Z).rawHostRank T vertex v)=real v:=by
    let pair := (Z).hostFields T vertex v
    change finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv pair)).1.castLE previous,
      (finProdFinEquiv.symm (finProdFinEquiv pair)).2) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [←extend_,comm,trunk_pointer B v true]
  cases hit : trunkLabels B v with
  | none=>rfl
  | some t=>simp [extend_]

theorem measured_trunk_actors (banks : DescentResetTrunkCompactPointer.Banks) (m : Memory bw)
    (count : m banks.total.base=(used:Word bw))
    (inverse : ∀v:B.next.V,m (banks.here.base+(dense v).val)=((real v).val:Word bw))
    (forward_ : ∀v:B.next.V,m (banks.number.base+(real v).val)=((dense v).val:Word bw))
    (table : ∀j : Fin rawSize,m (banks.turn.base+j.val)=
      (((DescentResetTrunkPalette.pointer (Z).graph r Ht true j).elim rawSize Fin.val : ℕ) : Word bw)) :
    Measured banks (compactActorName B previous) (compactTrunkPeer B previous) m:=by
  let e:=compactActorOrder B previous
  refine ⟨count,?_,?_,?_⟩
  · intro i
    have read:=inverse (e.symm i)
    change m (banks.here.base+(e (e.symm i)).val)=_ at read
    rw [e.apply_symm_apply] at read
    exact read
  · intro i
    rw [table]
    unfold compactActorName compactTrunkPeer
    rw [trunk_pointer_wide]
    cases sel : trunkLabels B (e.symm i) with
    | none=>simp [e] at *
    | some t=>simp [e] at *
  · intro i
    have read:=forward_ (e.symm i)
    change m (banks.number.base+(real (e.symm i)).val)=((e (e.symm i)).val:Word bw) at read
    rw [e.apply_symm_apply] at read
    exact read

def compactTrunkBanks (store : Store) (base : ℕ) : DescentResetTrunkCompactPointer.Banks:=
  ⟨store.inverse,⟨base+rawSize,Nat.clog 2 rawSize⟩,store.ranks,store.count rawSize⟩

/-- Mount the genuine common rotor/fall/trunk palette after the returned actor directory.
The chronological issuer retains its two opposite ordinal maps and its count. -/
theorem compact_trunk_mounted (store : Store) (base : ℕ) (m : Memory bw)
    (count : m (store.ranks.base+rawSize)=(used:Word bw))
    (inverse : ∀v:B.next.V,m (store.inverse.base+(dense v).val)=((real v).val:Word bw))
    (forward_ : ∀v:B.next.V,m (store.ranks.base+(real v).val)=((dense v).val:Word bw))
    (keepInv : store.inverse.base+used≤base) (keepRank : store.ranks.base+rawSize<base) (space : base+3*rawSize<2^bw) :
    let dst:=DescentResetTrunkPalette.memory (Z).graph r Ht base H0 m
    (DescentResetTrunkPalette.program (Z).graph r Ht bw base H0).Exec m dst (4+10*(3*rawSize)) ∧
      Measured (compactTrunkBanks (B:=B) (H0:=H0) store base) (compactActorName B previous) (compactTrunkPeer B previous) dst:=by
  intro dst
  obtain ⟨runs,columns,ret,_,_⟩:=DescentResetTrunkPalette.run (Z).graph r Ht base H0 m space
  refine ⟨runs,measured_trunk_actors B previous _ _ ((ret _ (.inl keepRank)).trans count) ?_ ?_ ?_⟩
  · intro v
    have below : store.inverse.base+(dense v).val<base :=
      (Nat.add_lt_add_left (show (dense v).val<used from (dense v).isLt) _).trans_le keepInv
    exact (ret _ (.inl below)).trans (inverse v)
  · intro v
    have below : store.ranks.base+(real v).val<base :=
      (Nat.add_lt_add_left (real v).isLt _).trans keepRank
    exact (ret _ (.inl below)).trans (forward_ v)
  · intro i
    simpa [compactTrunkBanks,DescentResetTrunkPalette.value] using columns (1:Fin 3) i

/-- Ghost rows stop at the native count guard. All live rows gather their true signed host stem. -/
theorem compact_trunk_gather (bounded : used≤H) (rack : Fin H→Option B.next.V)
    (present : ∀v,rack ((dense v).castLE bounded)=some v)
    (named : ∀h v,rack h=some v→(dense v).castLE bounded=h)
    (x : Fin (2^k)) (j : Fin half) (v : Fin H) (g : Fin grp) :
    (pointer bounded (compactTrunkPeer B previous) v).elim 0
      (fun h=>incomingWord B rack b x (finProdFinEquiv.symm j) h g)=
      DescentResetFieldAssembler.raw b ((rack v).elim .blank (fun a=>hostStem B ((g,a),x) j)):=by
  cases here : rack v with
  | none=>
    have missing : ¬v.val<used:=by
      intro live
      let e:=compactActorOrder B previous
      let a:=e.symm ⟨v.val,live⟩
      have rank : (dense a).castLE bounded=v:=by
        apply Fin.ext
        change (e (e.symm ⟨v.val,live⟩)).val = v.val
        exact congrArg (fun t : Fin used => t.val) (e.apply_symm_apply ⟨v.val,live⟩)
      have hit:=present a
      rw [rank,here] at hit
      cases hit
    simp [pointer,missing,zero_raw]
  | some a=>
    have eqn:=named v a here
    subst v
    have fit : ((dense a).castLE bounded).val<used:=(dense a).isLt
    have same : (⟨((dense a).castLE bounded).val,fit⟩ : Fin used)=compactActorOrder B previous a:=rfl
    simp only [pointer,dite_eq_left fit,same,compactTrunkPeer,Equiv.symm_apply_apply,Option.elim_some]
    cases hits : trunkLabels B a with
    | none=>simp [hits,hostStem,zero_raw]
    | some p=>
      simp [hits,hostStem,incomingWord,compactActorOrder]
      let readAt (who : B.next.V) (n : Fin (totalLocal B)) :=
        DescentResetFieldAssembler.raw b («meta» B ((g,who),x) (localOrigin B ((g,who),x) n))
      let stem := stemIndex B true (finProdFinEquiv.symm j)
      calc
        _ = readAt p.right stem :=
          congrArg (fun o : Option B.next.V => o.elim 0 (fun who => readAt who stem)) (present p.right)
        _ = _ := congrArg (readAt p.right) (incoming_candidate_index B j)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

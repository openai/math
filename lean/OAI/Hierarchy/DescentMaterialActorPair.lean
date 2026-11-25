import OAI.Hierarchy.DescentMaterialActorInputs

namespace OAI
/-! An occupied-raster and its retained physical donor panel produce both earlier venue sockets together. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.ActorInputs
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedCableNames DescentHaloWalkRAM
open DescentSixParty.Chronology DescentScalarVenueMask ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) {H G M w : ℕ}
def jointBase (_H _G M base : ℕ) :=RegisterJoin.dataBase (totalBits s) (1*s.blocks) M base
def routeStart (H G M base : ℕ):=jointBase s H G M base+2^Nat.clog 2 (H*chunks G M+1)
def keyStart (H G M base : ℕ):=afterSide s H G M (routeStart s H G M base)
def roof (H G M base : ℕ):=afterSide s H G M (keyStart s H G M base)+2^Nat.clog 2 (H*chunks G M+1)
theorem translates (H G M base : ℕ) : roof s H G M base=base+roof s H G M 0 :=by
  simp [roof,keyStart,afterSide,RoleScans.limit,RoleScans.home,routeStart,jointBase,RegisterJoin.dataBase,Nat.add_assoc]

variable (profile slots raw base : ℕ) (old act : Bank) (m : Memory w)
set_option quotPrecheck false
local notation "rows" => H*chunks G M
local notation "joined" => RegisterJoin.phase (totalBits s) (1*s.blocks) H G M w base (.lookup old .row) (.lookup act .row)
local notation "joint" => RegisterJoin.bank (totalBits s) (1*s.blocks) H G M base
local notation "first" => routeStart s H G M base
local notation "second" => keyStart s H G M base
local notation "paths" => issued s profile slots raw H G M w first joint 0
local notation "keys" => issued s profile slots raw H G M w second joint 1
def paired (H G M w : ℕ) : NativePhase w :=
  let j:=RegisterJoin.phase (totalBits s) (1*s.blocks) H G M w base (.lookup old .row) (.lookup act .row)
  let b:=RegisterJoin.bank (totalBits s) (1*s.blocks) H G M base
  let path:=issued s profile slots raw H G M w (routeStart s H G M base) b 0
  let key:=issued s profile slots raw H G M w (keyStart s H G M base) b 1
  (j.seq path).seq key

structure Room (base H G M w raw : ℕ) (old act : Bank) : Prop where
  oldFits : old.Fits w base
  oldSize : H*chunks G M≤old.size
  actFits : act.Fits w base
  actSize : H*chunks G M≤act.size
  pathsFit : M*max (bits s) (Packed.bits (breadth s.degree))≤w/2
  keysFit : M*max (bits s) (Packed.bits raw)≤w/2
  enough : roof s H G M base<2^w

private theorem prices (ok : Room s base H G M w raw old act) :
    rows≤(joint).size ∧ (joint).base+(joint).size≤first ∧ first≤ second ∧
    afterSide s H G M second<2^w ∧ second<2^w ∧ (joint).base+rows<2^w :=by
  have n:rows≤2^Nat.clog 2 (rows+1):=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have end₀:=ok.enough
  change _+_ < _ at end₀
  have step (j : ℕ) : j≤afterSide s H G M j:=by unfold afterSide RoleScans.limit RoleScans.home;omega
  have end₁:=step second
  have middle:=step first
  refine ⟨n,le_rfl,middle,by omega,by omega,?_⟩
  change jointBase s H G M base+rows<2^w
  have boundRows : jointBase s H G M base + rows ≤ first := Nat.add_le_add_left n _
  have hi : afterSide s H G M second < 2^w := (Nat.le_add_right ..).trans_lt end₀
  exact boundRows.trans_lt ((show first ≤ second from middle).trans_lt (end₁.trans_lt hi))

theorem all_runs (ok : Room s base H G M w raw old act) :
    (paired s profile slots raw base old act H G M w).Runs m ∧
    (∀z,z<base ∨ roof s H G M base≤z→(paired s profile slots raw base old act H G M w).image m z=m z) :=by
  obtain ⟨n,bound,near,end_,upper,previous⟩:=prices s raw base old act ok
  have join:=RegisterJoin.any (totalBits s) (1*s.blocks) base (.lookup old .row) (.lookup act .row) m (by exact ⟨ok.oldFits,trivial⟩)
    (by exact ⟨ok.actFits,trivial⟩) previous
  have left:=any s profile slots raw first joint ((joined).image m) 0 bound n (by simpa using ok.pathsFit) upper
  have right:=any s profile slots raw second joint ((paths).image ((joined).image m)) 1 (bound.trans near) n
    (by simpa using ok.keysFit) end_
  refine ⟨NativePhase.seq_runs _ _ _ (NativePhase.seq_runs _ _ _ join.1 left.1) right.1,?_⟩
  have fromBase:base≤first:=(Nat.le_add_right base _).trans (Nat.le_add_right ..)
  have roofRight:afterSide s H G M second≤roof s H G M base:=Nat.le_add_right ..
  have last:second≤afterSide s H G M second:=by unfold afterSide RoleScans.limit RoleScans.home;omega
  have placed:(joint).base+rows≤first:= (Nat.add_le_add_left n _).trans bound
  intro z away
  exact (right.2 z (by omega)).trans ((left.2 z (by change z<first ∨ second≤z;omega)).trans
    (join.2 z (by change z < base ∨ (joint).base + rows ≤ z; omega)))

theorem columns (ok : Room s base H G M w raw old act) (v : Fin H→Fin G→Parts s)
    (active : Fin H→Fin G→Cell (1*s.blocks)) (src : Reads old (fun h g=>combine s (v h g)) M m)
    (actors : Reads act active M m) (l : Label s) :
    let done:=(paired s profile slots raw base old act H G M w).image m
    Reads (bank s H G M first l) (fun h g=>pathCode (token s profile slots raw (v h g) (active h g) l)) M done ∧
    Reads (bank s H G M second l) (fun h g=>localCode (token s profile slots raw (v h g) (active h g) l)) M done :=by
  intro done
  obtain ⟨n,bound,near,end_,upper,previous⟩:=prices s raw base old act ok
  have jointRead:=RegisterJoin.physical (totalBits s) (1*s.blocks) base (.lookup old .row) (.lookup act .row) m
    (by exact ⟨ok.oldFits,trivial⟩) (by exact ⟨ok.actFits,trivial⟩) previous _ _
    (source_column old base ok.oldFits m _ ok.oldSize src) (source_column act base ok.actFits m _ ok.actSize actors)
  have left:=any s profile slots raw first joint ((joined).image m) 0 bound n (by simpa using ok.pathsFit) upper
  have right:=any s profile slots raw second joint ((paths).image ((joined).image m)) 1 (bound.trans near) n (by simpa using ok.keysFit) end_
  have kept:Reads joint (fun h g=>RegisterJoin.joined (combine s (v h g)) (active h g)) M ((paths).image ((joined).image m)):=by
    intro p;exact (left.2 _ (Or.inl ((Nat.add_lt_add_left ((row H G M p).isLt.trans_le n) _).trans_le bound))).trans (jointRead p)
  have path:=chip s profile slots raw first joint ((joined).image m) 0 bound n (by simpa using ok.pathsFit) upper v active jointRead l
  have label:=chip s profile slots raw second joint ((paths).image ((joined).image m)) 1 (bound.trans near) n
    (by simpa using ok.keysFit) end_ v active kept l
  constructor
  · intro p
    have lim:(bank s H G M first l).base+(row H G M p).val<second:=by
      let a:=(finProdFinEquiv l).val
      have hi:a<count s:=(finProdFinEquiv l).isLt
      have bound₀:=Nat.mul_le_mul_right rows (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at bound₀
      have pos:=(row H G M p).isLt
      change RoleScans.home (bits s) H G M (count s) first+a*rows+_<
        RoleScans.home (bits s) H G M (count s) first+count s*rows
      omega
    exact (right.2 _ (Or.inl lim)).trans (by simpa [Publisher.projection] using path p)
  · intro p
    exact label p

end
end Hierarchy.DescentRawCablePanel.DepotRAM.ActorInputs

end OAI

import OAI.Hierarchy.DescentDatedSortedBroadcast

namespace OAI
/-! # Read the translated donor path from the original two rosters on the resolver's own lane pitch -/
namespace Hierarchy.DescentDatedOperandReadPipeline.SortedInput.Broadcast
open DescentDatedSourcePathDirectory DescentSortedRoster DescentHaloWalkRAM DescentSIMDLookup DescentPackedZip
open DescentSharedLeafLookup DescentRawCablePanel DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (g : Geometry)
local notation "K" => g.hosts
local notation "G" => g.groups
local notation "M" => g.lanes
local notation "P" => g.paths
local notation "a" => g.digitBits

theorem placed {w base : ℕ} (vis : Bank) (room : finish g base<2^w) :
    let B:=layout g base vis
    B.start.Fits w (finish g base) ∧ B.cut.Fits w (finish g base) ∧ B.broadcast.Fits w (finish g base) :=by
  intro B
  have fit (b : Bank) (stop : b.base+b.size≤finish g base) :
      b.Fits w (finish g base):=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (stop.trans_lt room),stop⟩
  let pad:=Public.stride K G M
  let rep:=2^(Nat.clog 2 (Public.words a M))
  have below : base+2*pad≤finish g base:=Nat.le_add_right _ rep
  refine ⟨fit _ ?_,fit _ ?_,fit _ ?_⟩
  · change base+pad≤finish g base
    exact (Nat.add_le_add_left (Nat.le_mul_of_pos_left pad (by decide : 0<2)) base).trans below
  · change base+pad+pad≤finish g base
    simpa only [two_mul,Nat.add_assoc] using below
  · exact le_rfl

theorem port_fits {w base H : ℕ} (vis srt : Bank)
    (vfit : vis.Fits w base) (sfit : srt.Fits w base) (room : finish g base<2^w) (s : Fin P) :
    (port g base H vis srt s).Fits w (finish g base) :=by
  let B:=layout g base vis
  obtain ⟨one,two,three⟩:=placed g vis room
  have order : base≤finish g base:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have recv : (Expr.lookup B.start .row).Fits w (finish g base):=⟨one,trivial⟩
  have derived:=(Sorted.expr_fits (H:=H) vis srt vfit sfit s)
  have sub (x y : Expr) (hx : x.Fits w (finish g base)) (hy : y.Fits w (finish g base)) :
      (x.atRow y).Fits w (finish g base):=by induction x <;> simp_all only [Expr.Fits,Expr.atRow] <;> tauto
  exact ⟨three,⟨two,trivial⟩,recv,trivial,trivial,sub _ _ (ProtocolRAMGeneratedWrite.fits_mono _ order derived) recv⟩

theorem read_port {w base H pitch : ℕ} (vis srt : Bank) (reach : Fin H→Fin P→Option (Fin H)) (s : Fin P)
    (m : Memory w) (room : finish g base<2^w) (high : H<2^w) (paths : P≤2^a)
    (vfit : vis.Fits w base) (sfit : srt.Fits w base) (nv : H*P≤vis.size) (ns : H*P≤ srt.size)
    (raw : ∀h p,m (vis.base+(Ranks.id h p).val)=(number (Gather.select reach h p):Word w))
    (sorted : ∀h t,m (srt.base+(Ranks.id h t).val)=(number (indexed reach h t):Word w))
    (ready : Issued g base H pitch vis m) :
    Held g (finish g base) m (port g base H vis srt s) (value g pitch reach s) :=by
  let B:=layout g base vis
  obtain ⟨one,two,three⟩:=placed g vis room
  refine ⟨port_fits g vis srt vfit sfit room s,?_⟩
  intro row_
  let x : Word w:=((row K G M row_).val:Word w)
  let valAt : Fin K→Cell a:=fun h=>(DepotRAM.Material.Route.receiver H pitch h).elim 0 (fun z=>(Sorted.rawAtOrdinal reach z s:Cell a))
  have limit : K*chunks G M≤B.start.size:=Nat.le_pow_clog (by decide) _
  have cutLimit : K*chunks G M≤B.cut.size:=limit
  have hread:=(DescentIssuedTerminalId.lookup_nat B.start m x .row _ rfl
    ((row K G M row_).isLt.trans_le limit) one.2.1).trans (ready.host row_)
  have cread:=(DescentIssuedTerminalId.lookup_nat B.cut m x .row _ rfl
    ((row K G M row_).isLt.trans_le cutLimit) two.2.1).trans (ready.cut row_)
  let receptor:=Expr.lookup B.start .row
  let numberAt:=Expr.branch .eq receptor (.lit H) (.lit 0) ((Sorted.expr vis srt H s).atRow receptor)
  have chosen : numberAt.eval m x=((valAt row_.1).val:Word w):=by
    change (if DescriptorExpr.Comparison.eq.test (receptor.eval m x) (H:Word w) then (0:Word w)
      else ((Sorted.expr vis srt H s).atRow receptor).eval m x)=_
    rw [eval_atRow]
    cases found : DepotRAM.Material.Route.receiver H pitch row_.1 with
    | none=>
      have empty : receptor.eval m x=(H:Word w):=by
        simpa only [receptor,found,number,Option.elim_none] using hread
      simp [empty,valAt,found,DescriptorExpr.Comparison.test]
    | some z=>
      have r : receptor.eval m x=(z.val:Word w):=by
        simpa only [receptor,found,number,Option.elim_some] using hread
      have ne : (z.val:Word w)≠(H:Word w):=by
        intro eqn
        have h:=congrArg Fin.val eqn
        exact z.isLt.ne (by simpa only [Fin.val_natCast,Nat.mod_eq_of_lt high,Nat.mod_eq_of_lt (z.isLt.trans high)] using h)
      have small : Sorted.rawAtOrdinal reach z s<2^a:=by
        cases seen : indexed reach z s with
        | none=>simp [Sorted.rawAtOrdinal,seen]
        | some t=>obtain ⟨p,hp,_⟩:=Sorted.raw_at reach z t s seen;exact hp.2.symm ▸ p.isLt.trans_le paths
      have result:=Sorted.expr_read vis srt base m reach vfit sfit nv ns high raw sorted z s
      simpa only [r,DescriptorExpr.Comparison.test,beq_iff_eq,ite_eq_right ne,
        valAt,found,Option.elim_some,Fin.val_natCast,Nat.mod_eq_of_lt small] using result
  have size : Public.words a M≤B.broadcast.size:=Nat.le_pow_clog (by decide) _
  let idx:=finProdFinEquiv (usedRow row_,valAt row_.1)
  have n : idx.val=repeatAddr (usedRow row_) (valAt row_.1):=by simp [idx,repeatAddr,Nat.add_comm,Nat.mul_comm]
  have bound : repeatAddr (usedRow row_) (valAt row_.1)<B.broadcast.size:=by rw [←n];exact idx.isLt.trans_le size
  have target:=ready.repeatWord (usedRow row_) (valAt row_.1)
  rw [repeater valAt] at target
  change (Expr.lookup B.broadcast (.op .add (.lookup B.cut .row) numberAt)).eval m x=
    ((data (fun h (_ : Fin G)=>valAt h) row_).val:Word w)
  refine (DescentIssuedTerminalId.lookup_nat B.broadcast m x (.op .add (.lookup B.cut .row) numberAt)
    (repeatAddr (usedRow row_) (valAt row_.1)) ?_ bound three.2.1).trans target
  change (Expr.lookup B.cut .row).eval m x+numberAt.eval m x=
    (repeatAddr (usedRow row_) (valAt row_.1):Word w)
  rw [cread,chosen,repeatAddr,Nat.cast_add]
end
end Hierarchy.DescentDatedOperandReadPipeline.SortedInput.Broadcast

end OAI

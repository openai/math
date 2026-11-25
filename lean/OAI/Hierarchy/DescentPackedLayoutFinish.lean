import OAI.Hierarchy.DescentPackedLayoutPlan
import OAI.Hierarchy.DescentPackedSixBirthTables

namespace OAI
/-! # Six births and the shared layout choice on the same matching pages -/
namespace Hierarchy.DescentPacking.PackedMatch.LayoutSum.Finish
open DescentSixParty DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] (s : Shape) (M : ℕ) (top : Bank) (out n : ℕ)
local notation "tape" => SixBirths.tapeBank out n
def first := SixBirths.tableStart top tape
def births := SixBirths.outputBase s M top tape
def bank := SixBirths.tapeBank (births s M top out n) n
def base := (bank s M top out n).base+(bank s M top out n).size
def chart := LayoutSum.plan s M (bank s M top out n) (base s M top out n) n
def stop := (chart s M top out n).out+1
local notation "rom" => first top out n
local notation "dest" => births s M top out n
local notation "b" => bank s M top out n
local notation "start" => base s M top out n
local notation "B" => chart s M top out n
local notation "g" => SixBirths.mountedBanks s M rom top tape

def program (G : PoweredGadget F) (w : ℕ) : Procedure w := ((SixBirths.mount s M rom w).seq (SixBirths.program g n dest w)).seq
    ((LayoutSum.install s B M w G).seq (DescentPackedLayoutCPU.program B w n))
def ticks := ((4+10*SixBirths.entries s M)+(4+54*n))+LayoutSum.clocks s M n

private theorem rooms (w : ℕ) (rows : n≤top.size) (width : SixBirths.width s M≤w)
    (ends : stop s M top out n<2^w) :
    SixBirths.Room s M n dest w g ∧ (top.base+n≤rom ∧ out+n≤rom) ∧
      DescentPackedLayoutCPU.Space B w n ∧ LayoutSum.ROMSpace s M n w B := by
  have len : n≤(b).size := Nat.le_pow_clog (by decide) _
  have limit : start+2*2^(SixBirths.width s M)+4*n+3<2^w := by
    simpa only [stop,chart,LayoutSum.plan,Nat.add_assoc] using ends
  have last : start<2^w := by omega
  have allocate : dest+n≤ start := Nat.add_le_add_left len _
  have bankFit : (b).Fits w start := ⟨Nat.two_pow_pos _,(Nat.le_add_left (b).size (b).base).trans_lt last,le_rfl⟩
  have both:=LayoutSum.space s M b start n w bankFit len limit
  obtain ⟨birth,oldEnd,dataEnd⟩:=SixBirths.placed s M n w top tape rows (Nat.le_pow_clog (by decide) _) width
    (allocate.trans_lt last)
  exact ⟨birth,⟨oldEnd,dataEnd⟩,both⟩

private theorem layout_frame (G : PoweredGadget F) {w : ℕ} (m : Memory w) (fee : Bool→Fin n→ℕ)
    (room : DescentPackedLayoutCPU.Space B w n) (tables : LayoutSum.ROMSpace s M n w B)
    (x : ℕ) (away : x<start ∨ (B).out<x) :
    DescentPackedLayoutCPU.after B (LayoutSum.mounted s B M G m) fee x=m x := by
  let prev:=LayoutSum.mounted s B M G m
  have kept:= (LayoutSum.mount (G:=G) s B m tables).2.2
  rcases away with lo|hi
  · have left : x<(B).counts false := by change x<start+2*_ ;omega
    have right : x<(B).counts true := by change x<start+2*_+2*n+1;omega
    have atEnd : x<(B).out := by change x<start+2*_+4*n+2;omega
    exact (ProtocolRAMGeneratedWrite.frame_image (B).out 1 _ _ x (.inl atEnd)).trans
      ((DescentPackedLayoutCPU.side_frame B true _ _ room x (.inl right)).trans
      ((DescentPackedLayoutCPU.side_frame B false prev _ room x (.inl left)).trans (kept x (.inl lo))))
  · apply (DescentPackedLayoutCPU.above B _ _ room x hi).trans
    apply kept x (.inr ?_)
    change start+2^(SixBirths.width s M)+2^(SixBirths.width s M)≤x
    change start+2*2^(SixBirths.width s M)+4*n+2<x at hi
    omega

variable {C : Type} [Fintype C] {I : C→Type} [∀c,Fintype (I c)] {w : ℕ}

/-- Produce the six roles and the global common layout on the original physical
matcher's pages. The table is populated once and all six roles share a profile. -/
theorem run (G : PoweredGadget F) (z : ℕ) (pos : 0<z) (profile : (Σc,I c)→Profile G.C)
    (seat : C↪Fin n×Fin M) (item : ∀c,I c≃Fin (Fintype.card (I c)))
    (keys : Fin n→Cell (SixBirths.topology s M))
    (counts : Chronology.Counts seat (fun c=>Fintype.card (I c)) (fun i=>laneCounts s M (keys i)))
    (m : Memory w) (rows : n≤top.size) (width : SixBirths.width s M≤w)
    (ends : stop s M top out n<2^w) (budget : Fintype.card (Σc,I c)*(G.C+8+8*G.k)<2^w)
    (issued : ∀i : Fin n,m (top.base+i.val)=((keys i).val:Word w))
    (read : ∀c e,∃v : Fin s.pairs,v.val=(item c e).val ∧
      digit s.digit (finProdFinEquiv ((seat c).2,v)).val (m (out+(seat c).1.val)).val=
        DescentTerminalEpochFlags.encode (profile ⟨c,e⟩)) :
    ∃done,(program s M top out n G w).Exec m done (ticks s M n) ∧
      done (B).out=(if bestLayout (branchWidth G (fun _=>z) profile) then (1:Word w) else 0) ∧
      (∀x,x<rom ∨ (B).out<x → done x=m x) ∧
      ∀ (i : Fin n) (a : Fin M) (j : Fin s.pairs) (q : Fin 6),
        digit (s.digit+1) (SixBirths.slot a j q).val (done (dest+i.val)).val=
          if j.val<(laneCounts s M (keys i) a).val then
            digit s.digit (finProdFinEquiv (a,j)).val (m (out+i.val)).val+1 else 0 := by
  obtain ⟨fit,early,space,static⟩:=rooms s M top out n w rows width ends
  let middle:=SixBirths.after g n dest (SixBirths.mounted s M rom m)
  obtain ⟨make,records,_⟩:=SixBirths.fresh s M n rom dest w top tape fit early m keys issued
  have small:=SixBirths.fresh_bound s M n rom dest w top tape fit early m keys issued
  let board (i : Fin n) : Cell (SixBirths.width s M):=⟨(middle (dest+i.val)).val,small i⟩
  let ctr (i : Fin n):=laneCounts s M (keys i)
  let spot:=LayoutSum.spot s seat item ctr counts
  have real (c : C) (e : I c) : digit (s.digit+1)
      (SixBirths.slot (seat c).2 (spot ⟨c,e⟩).2.2 (0:Fin 6)).val (board (seat c).1).val=
      DescentTerminalEpochFlags.encode (profile ⟨c,e⟩)+1 := by
    obtain ⟨v,ordinal,prof⟩:=read c e
    have same : (spot ⟨c,e⟩).2.2=v:=Fin.ext ordinal.symm
    have on_ : v.val<(ctr (seat c).1 (seat c).2).val:=by rw [ordinal,counts.live c];exact (item c e).isLt
    dsimp only [board]
    rw [same,records,ite_eq_left on_]
    exact congrArg (· + 1) prof
  have ghosts (i : Fin n) (a : Fin M) (j : Fin s.pairs) (off : (ctr i a).val≤j.val) :
      digit (s.digit+1) (SixBirths.slot a j (0:Fin 6)).val (board i).val=0 := by
    dsimp only [board];rw [records,ite_eq_right (Nat.not_lt.mpr off)]
  have input (i : Fin n) : middle ((B).pairs.base+i.val)=((board i).val:Word w) := by
    change middle (dest+i.val)=((middle (dest+i.val)).val:Word w)
    exact Fin.ext (by rw [Fin.val_cast_of_lt (middle (dest+i.val)).isLt])
  let fee (which : Bool) (i : Fin n):=LayoutSum.score (G:=G) s (LayoutSum.profileCode G.C) M which (board i).val
  obtain ⟨decide_,flag⟩:=LayoutSum.packed_layout s B seat item ctr counts profile z pos middle space static width
    board input real ghosts budget
  have before (x : ℕ) (away : x<rom ∨ dest+n≤x) : middle x=m x := by
    have equality : rom+SixBirths.entries s M=dest:=rfl
    exact (ProtocolRAMGeneratedWrite.frame_image dest n (SixBirths.expr g) _ x
      (by rcases away with lo|hi;exact .inl (by omega);exact .inr hi)).trans
      (DescentStaticWordColumn.frame rom (SixBirths.entries s M) (SixBirths.literal s M) m x
        (by rcases away with lo|hi;exact .inl lo;exact .inr (by omega)))
  have after (x : ℕ) (away : x<start ∨ (B).out<x) := layout_frame s M top out n G middle fee space static x away
  have left : rom≤dest := Nat.le_add_right ..
  have rowsFit : dest+n≤ start := Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  have last : start≤(B).out:=by change start≤ start+2*_+4*n+2;omega
  refine ⟨_,?_,flag,?_,?_⟩
  · unfold ticks
    rw [←LayoutSum.clock_eq s M B n]
    exact make.then decide_
  · intro x where_
    rcases where_ with lo|hi
    · exact (after x (.inl (lo.trans_le (left.trans ((Nat.le_add_right ..).trans rowsFit))))).trans (before x (.inl lo))
    · exact (after x (.inr hi)).trans (before x (.inr ((rowsFit.trans last).trans (Nat.le_of_lt hi))))
  · intro i a j q
    rw [after _ (.inl ((Nat.add_lt_add_left i.isLt dest).trans_le rowsFit))]
    exact records i a j q

set_option maxHeartbeats 800000 in
/-- All bit assignments execute exactly the same suffix. -/
theorem any_framed (G : PoweredGadget F) (m : Memory w) (rows : n≤top.size)
    (width : SixBirths.width s M≤w) (ends : stop s M top out n<2^w) :
    ∃done,(program s M top out n G w).Exec m done (ticks s M n) ∧ (∀x,x<rom ∨ (B).out<x → done x=m x) ∧ CheapCode (program s M top out n G w) := by
  obtain ⟨fit,_,space,tables⟩:=rooms s M top out n w rows width ends
  have pre : rom+SixBirths.entries s M<2^w :=
    (Nat.le_add_right dest n).trans_lt fit.output
  obtain ⟨mount,_,_,fixed⟩:=SixBirths.mount_read s M rom w top tape m pre
  obtain ⟨stamp,cheapStamp⟩:=SixBirths.run s M n dest w g fit (SixBirths.mounted s M rom m)
  let middle:=SixBirths.after g n dest (SixBirths.mounted s M rom m)
  obtain ⟨paid,_,_⟩:=LayoutSum.mount (G:=G) s B middle tables
  obtain ⟨fee,elect⟩:=DescentPackedLayoutCPU.total_run B (LayoutSum.mounted s B M G middle) space
  let birth := (SixBirths.mount s M rom w).seq (SixBirths.program g n dest w)
  let decideLayout := (LayoutSum.install s B M w G).seq (DescentPackedLayoutCPU.program B w n)
  have cheapBirth : CheapCode birth := @cheap_seq w (SixBirths.mount s M rom w) (SixBirths.program g n dest w) fixed cheapStamp
  have cheapLayout : CheapCode decideLayout := LayoutSum.cheap (M:=M) (w:=w) (n:=n) s B G
  refine ⟨DescentPackedLayoutCPU.after B (LayoutSum.mounted s B M G middle) fee,?_,?_,
    @cheap_seq w birth decideLayout cheapBirth cheapLayout⟩
  · unfold ticks
    rw [←LayoutSum.clock_eq s M B n]
    exact @Procedure.Exec.then w birth decideLayout m middle _ _ _
      (Procedure.Exec.then mount stamp) (Procedure.Exec.then paid elect)
  · intro x away
    have left : rom≤dest:=Nat.le_add_right ..
    have rowsFit : dest+n≤ start:=Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
    have last : start≤(B).out:=by change start≤ start+2*_+4*n+2;omega
    have before_ := layout_frame s M top out n G middle fee space tables x
      (away.imp_left (fun hx=>hx.trans_le (left.trans ((Nat.le_add_right ..).trans rowsFit))))
    have change_:=ProtocolRAMGeneratedWrite.frame_image dest n (SixBirths.expr g) (SixBirths.mounted s M rom m) x
      (by rcases away with lo|hi;exact Or.inl (lo.trans_le left);exact Or.inr ((rowsFit.trans last).trans hi.le))
    have endTable : rom+SixBirths.entries s M=dest:=rfl
    exact before_.trans (change_.trans (DescentStaticWordColumn.frame rom (SixBirths.entries s M)
      (SixBirths.literal s M) m x (by rcases away with lo|hi;exact .inl lo;exact .inr (by omega))))

private theorem forget_frame {α : Type*} (ran kept : α → Prop) (cheap : Prop)
    (witness : ∃ x, ran x ∧ kept x ∧ cheap) : ∃ x, ran x ∧ cheap := by
  obtain ⟨x, r, _, c⟩ := witness
  exact ⟨x, r, c⟩

theorem any (G : PoweredGadget F) (m : Memory w) (rows : n≤top.size)
    (width : SixBirths.width s M≤w) (ends : stop s M top out n<2^w) :
    ∃done,(program s M top out n G w).Exec m done (ticks s M n) ∧ CheapCode (program s M top out n G w) := by
  exact forget_frame (fun done => (program s M top out n G w).Exec m done (ticks s M n))
    (fun done => ∀ x, x < rom ∨ (B).out < x → done x = m x)
    (CheapCode (program s M top out n G w)) (any_framed s M top out n G m rows width ends)

theorem width_le (s : Shape) (M unit p : ℕ) (cost : SixBirths.unit s≤unit)
    (fit : unit*M≤p/2) : SixBirths.width s M≤p/2 := by
  have width : (s.digit+1)*(s.pairs*6)≤unit:=(le_max_right ..).trans cost
  calc
    SixBirths.width s M=((s.digit+1)*(s.pairs*6))*M:=by unfold SixBirths.width;ring
    _≤p/2 := (Nat.mul_le_mul_right M width).trans fit

/-- Both lookup tables and the six-birth table fit the same public half word. -/
theorem tick_bound (unit p : ℕ) (cost : SixBirths.unit s≤unit) (fit : unit*M≤p/2) :
    ticks s M n≤88+40*2^(p/2)+134*n := by
  have sum_ : SixBirths.profiles s M+SixBirths.topology s M≤p/2 := by
    have a : s.digit*s.pairs+s.outputBits≤unit := (le_max_left ..).trans cost
    have batchBound := (Nat.mul_le_mul_right M a).trans fit
    unfold SixBirths.profiles SixBirths.topology
    simpa only [Nat.add_mul,Nat.mul_assoc,Nat.mul_comm s.pairs M] using batchBound
  have t:=SixBirths.mount_size s M p sum_
  have bound:=Nat.pow_le_pow_right (by decide : 0<2) (width_le s M unit p cost fit)
  unfold ticks LayoutSum.clocks
  omega

/-- The complete allocation adds two tables of the common half-word size and
four linear work areas to the already produced matcher profile pages. -/
theorem extent (unit payload : ℕ) (cost : SixBirths.unit s≤unit) (packed : unit*M≤payload/2)
    (ordered : top.base+top.size≤out) :
    stop s M top out n≤out+8*n+4*2^(payload/2)+5 := by
  have a : s.digit*s.pairs+s.outputBits≤unit := (le_max_left ..).trans cost
  have key : SixBirths.profiles s M+SixBirths.topology s M≤payload/2 := by
    unfold SixBirths.profiles SixBirths.topology
    simpa only [Nat.add_mul,Nat.mul_assoc,Nat.mul_comm s.pairs M] using (Nat.mul_le_mul_right M a).trans packed
  have firstPage:=SixBirths.mount_size s M payload key
  have lastPage:=Nat.pow_le_pow_right (by decide : 0<2) (width_le s M unit payload cost packed)
  have bankSize : (SixBirths.tapeBank out n).size≤2*n+1 := by
    change 2^Nat.clog 2 n≤2*n+1
    rcases n with _|n
    · decide
    · by_cases one : n=0
      · subst n;decide
      · have available:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n+1 by omega)
        have log : 0<Nat.clog 2 (n+1):=Nat.clog_pos (by decide) (by omega)
        have eqpow : 2^Nat.clog 2 (n+1)=2^(Nat.clog 2 (n+1)-1)*2 := by
          rw [←pow_succ, Nat.sub_add_cancel log]
        rw [eqpow]
        change 2^(Nat.clog 2 (n+1)-1)<n+1 at available
        omega
  have topFit : top.base+top.size≤out+(tape).size := ordered.trans (Nat.le_add_right ..)
  have origin : rom=out+(tape).size:=max_eq_right topFit
  have next : dest=rom+SixBirths.entries s M:=rfl
  have calcEnd : stop s M top out n=dest+(tape).size+2*2^(SixBirths.width s M)+4*n+3 := by
    unfold stop chart LayoutSum.plan base bank SixBirths.tapeBank Bank.size
    simp only [Nat.add_assoc]
  omega

theorem hardware (G : PoweredGadget F) (w : ℕ) :
    DescentStaticWordColumn.names (program s M top out n G w)=
      (126+15*SixBirths.entries s M)+(30*(2^(SixBirths.width s M)+1)+265) := by
  rw [program,DescentStaticWordColumn.names_seq]
  exact congrArg₂ Nat.add (SixBirths.control s M rom n dest w g) (LayoutSum.hardware s M G B w n)

end
end Hierarchy.DescentPacking.PackedMatch.LayoutSum.Finish

end OAI

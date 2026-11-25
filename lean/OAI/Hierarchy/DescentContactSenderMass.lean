import OAI.Hierarchy.DescentContactSenderPrice

namespace OAI
/-! # One shared count table for all directed contact sockets on the old high-block raster -/
namespace Hierarchy.DescentContactSenderMass
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOldContactSender DescentOrdinaryAtomFieldRAM
open DescentPacking.PackedMatch.Local.Gather DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D L cap n r Ht b w : ℕ}
local notation "senderCount" => L*(2*cap)
local notation "J" => DescentResetLocalRoster.rootSlots r (2^n)*((2^n)+2^Ht)
local notation "Q" => 2*J
local notation "inputs" => senderCount+1

def price {N b : ℕ} (wanted : ℕ) (xs : Fin N→Cell b) := Fintype.card {j : Fin N // (xs j).val=wanted}
def tally (a : Fin inputs→Cell b) : Cell b := price (a 0).val (fun j=>a j.succ)

theorem bounded {N b : ℕ} (wanted : ℕ) (xs : Fin N→Cell b) : price wanted xs≤N:=
  (Fintype.card_le_of_injective (fun j : {j : Fin N // (xs j).val=wanted}=>j.val) Subtype.val_injective).trans_eq (Fintype.card_fin N)

/-- The page index is the same directed slot as `Window.donor_query`. A real socket's
query is strictly positive, which excludes all vacant old signed positions. -/
def query (j : Fin Q) : Bool×ℕ :=
  let p : Fin 2×Fin J:=finProdFinEquiv.symm j
  (finTwoEquiv p.1,p.2.val+1)

namespace Date
variable (A : DescentContactSenderDate.Layout D L cap n r Ht b) (base : ℕ)
local notation "H" => A.hosts
local notation "G" => A.groups
local notation "M" => A.batch
def width := A.localShape.rowBits
def span := 2^(width A)
def keyPage (j : Fin Q) : ROM.Page:=⟨width A,fun p=>
  if fit : p.val<A.localShape.rows then
    (data («M» :=M) (fun (_ : Fin H) (_ : Fin G)=>((query j).2:Cell b))
      ((row H G M).symm ⟨_,fit⟩)).val
  else 0⟩
def keyBank (j : Fin Q) := ROM.bank (keyPage A) (width A) base j
def issueAt := base+Q*span A
def calendar : DescentResetCandidateDate.Shape:=⟨issueAt A base,Q,M,H,G⟩
def reads (j : ℕ) : Fin inputs→Expr :=
  if real : j<Q then let slot : Fin Q:=⟨_,real⟩
    Fin.cases (.lookup (keyBank A base slot) .row) (fun t=>.lookup (A.senderBank (query slot).1 (finProdFinEquiv.symm t) 0) .row)
  else fun _=>.lit 0
def bank (j : Fin Q) := (calendar A base).output inputs b j.val
def endAddress := (calendar A base).endAddress inputs b
def mounted (m : Memory w) := ROM.after (keyPage A) (width A) base m
def output (m : Memory w) := (calendar A base).image (tally (L:=L) (cap:=cap) (b:=b)) (reads A base) (mounted A base m)
def program (w : ℕ) := (ROM.mount (keyPage A) (width A) w base).seq
  ((calendar A base).code (tally (L:=L) (cap:=cap) (b:=b)) (reads A base) w)
def ticks := (4+10*(Q*span A))+(calendar A base).ticks (tally (L:=L) (cap:=cap) (b:=b)) (reads A base)
def clockBound := (4+10*(Q*span A))+(calendar A base).costBound inputs b (1+inputs*18)
def nameBound := 15*(Q*span A+1)+(calendar A base).nameBound inputs b (1+inputs*18)

private theorem key_end : issueAt A base≤endAddress A base:=by
  obtain ⟨a,b,c⟩:=(calendar A base).ordered inputs b
  exact a.trans ((Nat.le_add_right ..).trans (b.trans c))

theorem keyFits (j : Fin Q) (room : endAddress A base<2^w) : (keyBank A base j).Fits w (issueAt A base) := by
  have bytes : (keyBank A base j).base+(keyBank A base j).size≤ issueAt A base:=by
    change base+j.val*span A+span A≤base+Q*span A
    rw [Nat.add_assoc,←Nat.succ_mul];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bytes.trans_lt ((key_end A base).trans_lt room)),bytes⟩

variable (prior : ∀s t,(A.senderBank s t 0).Fits w base)

include prior in
theorem readFits (room : endAddress A base<2^w) (j : ℕ) (real : j<Q) (i : Fin inputs) :
    (reads A base j i).Fits w (issueAt A base) := by
  simp only [reads,dite_eq_left real]
  refine Fin.cases ?_ (fun t=>?_) i
  · exact ⟨keyFits A base _ room,trivial⟩
  · have earlier:=prior (query ⟨_,real⟩).1 (finProdFinEquiv.symm t)
    exact ⟨⟨earlier.1,earlier.2.1,earlier.2.2.trans (Nat.le_add_right ..)⟩,trivial⟩

include prior in
theorem any (m : Memory w) (room : endAddress A base<2^w) :
    (program A base w).Exec m (output A base m) (ticks A base) ∧ CheapCode (program A base w) ∧
    ∀a,a<base ∨ endAddress A base≤a→ output A base m a=m a := by
  have fixed:=ROM.run (keyPage A) (width A) base m ((key_end A base).trans_lt room)
  have stage:=(calendar A base).any (tally (L:=L) (cap:=cap) (b:=b)) (reads A base) (mounted A base m)
    (readFits A base prior room) room
  exact ⟨Procedure.Exec.then (@fixed.1) (@stage.1),cheap_seq (ROM.cheap _ _ _ _) stage.2.1,
    fun a away=>(stage.2.2 a (away.imp (fun h=>h.trans_le (Nat.le_add_right ..)) id)).trans
    (ROM.frame _ _ _ m a (away.imp id (fun h=>(key_end A base).trans h)))⟩

def values (labels : Bool→Fin senderCount→Fin H→Fin G→Cell b) (j : Fin Q) (h : Fin H) (g : Fin G) : Cell b :=
  price (query j).2 (fun t=>labels (query j).1 t h g)

include prior in
theorem published (m : Memory w) (room : endAddress A base<2^w) (positive : 0<M)
    (packing : M*max (b*inputs) b≤w/2) (keysFit : J<2^b)
    (labels : Bool→Fin senderCount→Fin H→Fin G→Cell b)
    (seen : ∀s t,Reads (A.senderBank s (finProdFinEquiv.symm t) 0) (labels s t) M m) (j : Fin Q) :
    Reads (bank A base j) (values A labels j) M (output A base m) := by
  let field (z : ℕ) (h : Fin H) (g : Fin G) := if ok : z<Q then let a : Fin Q:=⟨_,ok⟩
    Fin.cases ((query a).2:Cell b) (fun t=>labels (query a).1 t h g)
    else fun _ : Fin inputs=>(0:Cell b)
  have inputsAt (z : ℕ) (ok : z<Q) (i : Fin inputs) :
    Source (reads A base z i) (fun h g=>field z h g i) M (mounted A base m) := by
    let a : Fin Q:=⟨_,ok⟩
    simp only [reads,field,dite_eq_left ok]
    refine Fin.cases ?_ (fun p=>?_) i
    · apply source_column _ _ (keyFits A base a room) _ _ A.localShape.rows_fit
      intro t
      have small : (row H G M t).val < A.localShape.rows := (row H G M t).isLt
      let at_ : Cell (width A):=⟨_,small.trans_le A.localShape.rows_fit⟩
      have read:=ROM.read (keyPage A) (width A) base m a (le_refl _) at_
      simp only [keyPage,at_,dite_eq_left small] at read
      have back : (row H G M).symm ⟨(row H G M t).val,small⟩ = t :=
        (row H G M).symm_apply_apply t
      rw [back] at read
      exact read
    · let home:=A.senderBank (query a).1 (finProdFinEquiv.symm p) 0
      have fit:=prior (query a).1 (finProdFinEquiv.symm p)
      apply source_column home base fit _ _ A.splitShape.rows_fit
      intro t
      exact (ROM.frame _ _ _ m _ (.inl ((Nat.add_lt_add_left ((row H G M t).isLt.trans_le A.splitShape.rows_fit) _).trans_le fit.2.2))).trans (seen _ p t)
  have words:=(calendar A base).words (tally (L:=L) (cap:=cap) (b:=b)) (reads A base) (mounted A base m)
    (readFits A base prior room) room positive packing field inputsAt j.val j.isLt
  have eqn (h : Fin H) (g : Fin G) : tally (field j.val h g)=values A labels j h g := by
    have keyOk : (query j).2<2^b:=Nat.lt_of_le_of_lt ((finProdFinEquiv.symm j : Fin 2×Fin J).2.isLt) keysFit
    simp [field,j.isLt,tally,values,Fin.val_cast_of_lt keyOk]
  have same : (fun h g => tally (field j.val h g)) = values A labels j :=
    funext fun h => funext fun g => eqn h g
  have countRead : Source (.lookup (bank A base j) .row)
      (fun (h : Fin H) (g : Fin G) => tally (field j.val h g)) M (output A base m) := words
  rw [same] at countRead
  intro t
  have small : (row H G M t).val < (bank A base j).size :=
    (row H G M t).isLt.trans_le (calendar A base).rows_fit
  have stored := bank_read (bank A base j) (output A base m) small
    ((calendar A base).output_fits (N:=inputs) (field:=b) j.val j.isLt room)
  exact stored.symm.trans (countRead t)

theorem priced :
    ticks A base≤clockBound A base ∧ names (program A base w)≤nameBound A base := by
  have lim (z : ℕ) (i : Fin inputs) : (reads A base z i).work≤7:=by
    unfold reads
    split
    · refine Fin.cases ?_ (fun p=>?_) i <;> change 7 ≤ 7 <;> exact Nat.le_refl 7
    · change 1 ≤ 7
      decide
  have work (z : ℕ) (is : List (Fin inputs)) :
      (collect ((calendar A base).tables (tally (L:=L) (cap:=cap) (b:=b))) (reads A base z) is).work≤
        1+is.length*18:=by
    induction is with
    | nil=>exact Nat.le_refl _
    | cons i is ih=>have h:=lim z i;simp only [collect,DescentPackedZip.work,List.length_cons,Nat.succ_mul] at *;omega
  have main:=(calendar A base).priced (w:=w) (tally (L:=L) (cap:=cap) (b:=b)) (reads A base) (1+inputs*18)
    (fun z _=>by simpa only [DescentResetCandidateDate.Shape.op,assembly,List.length_finRange] using work z (List.finRange inputs))
  have mountedCost : names (ROM.mount (keyPage A) (width A) w base)=15*(Q*span A+1):=names_mount ..
  exact ⟨Nat.add_le_add_left main.1 _,by simpa only [program,nameBound,names_seq,mountedCost] using Nat.add_le_add_left main.2 (15*(Q*span A+1))⟩

end Date
end
end Hierarchy.DescentContactSenderMass

end OAI

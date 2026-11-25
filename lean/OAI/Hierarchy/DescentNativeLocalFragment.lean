import OAI.Hierarchy.DescentTicketFragment
import OAI.Hierarchy.DescentPriorOperandFragment
import OAI.Hierarchy.DescentPackedRawTicket
import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentPackedOperandROM
import OAI.Hierarchy.DescentColonySplitRAM

namespace OAI
/-! Replace the two changed local handle columns at an ordinary payment date.
The old operand header determines which lanes are cable occurrences. -/
namespace Hierarchy.DescentOrdinaryLocalFragment
open DescentPackedOperand DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open DescentOrdinaryAtomFieldRAM.ROM DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {k H G M w a : ℕ}

def mask (cable : Bool) (tag value : Cell a) : Cell a :=
  if (decide (tag.val=1))=cable then value else 0

theorem mask_zero (cable : Bool) : mask (a:=a) cable 0 0=0 :=by simp [mask]

private theorem digits {a m : ℕ} (v : Fin m→Cell a) :
    (encode a m v).val=∑i,(v i).val*(2^a)^i.val :=finFunctionFinEquiv_apply v

theorem combine_data (tag prior fresh : Fin H→Fin G→Cell a) (p : Row H G M) :
    (data (fun h g=>if (tag h g).val=1 then fresh h g else prior h g) p).val=
      (data (fun h g=>mask false (tag h g) (prior h g)) p).val+
      (data (fun h g=>mask true (tag h g) (fresh h g)) p).val :=by
  simp only [data,digits,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases alive:p.2.val*M+j.val<G
  · simp only [dite_eq_left alive]
    by_cases paid:(tag p.1 ⟨p.2.val*M+j.val,alive⟩).val=1 <;> simp [mask,paid]
  · simp [alive]

def gate (t : Bool→Tables) (tag prior fresh : Expr) : Expr:=
  .op .add ((t false).read tag prior) ((t true).read tag fresh)

theorem gate_source (t : Bool→Tables) (tag prior fresh : Expr) (out : ℕ) (m : Memory w)
    (ready : ∀c,DescentPackedZip.Fits (t c) tag (if c then fresh else prior) a a M out w)
    (static_ : ∀c,Static (t c) (mask (a:=a) c) M m)
    (class_ old new_ : Fin H→Fin G→Cell a) (kind : Source tag class_ M m)
    (original : Source prior old M m) (next : Source fresh new_ M m) :
    Source (gate t tag prior fresh) (fun h g=>if (class_ h g).val=1 then new_ h g else old h g) M m :=by
  have left:=read_data (t false) tag prior out (ready false) (mask false) (mask_zero false) m (static_ false) class_ old kind original
  have right:=read_data (t true) tag fresh out (ready true) (mask true) (mask_zero true) m (static_ true) class_ new_ kind next
  intro p
  rw [combine_data]
  simp only [gate,Expr.eval,RowOp.opcode,BinaryOp.eval,left p,right p,Nat.cast_add]

def pages (a M : ℕ) (i : Fin 4) : Page :=
  let j : Fin 2 × Fin 2 := finProdFinEquiv.symm i
  binary (mask (a:=a) (decide (j.1.val=1))) M j.2

def atPage (c : Bool) (s : Fin 2) : Fin 4:=finProdFinEquiv ((if c then 1 else 0 : Fin 2),s)
theorem table_at (c : Bool) (s : Fin 2) : pages a M (atPage c s)=binary (mask (a:=a) c) M s :=by
  cases c <;> simp [pages,atPage]

def width (a M : ℕ):=(a+a)*M
def specEnd (base a M : ℕ):=base+4*2^(width a M)
def tables (a M base : ℕ) (c : Bool):=joined (pages a M) (width a M) base (atPage c)
theorem page_room (i : Fin 4) : (pages a M i).bits≤width a M :=by
  fin_cases i <;> first | exact le_rfl | exact Nat.mul_le_mul_right M (Nat.le_add_right a a)

def rhs (peer old role : Expr) (j : Fin 2) : Expr:=
  if j.val=0 then peer else DescentPackedRawTicket.ticket old role

def index (j : Fin 2) : Fin 10:=⟨2+j.val,by omega⟩
def expression (a M base : ℕ) (prior : Fin 10→Expr) (peer old role : Expr) (j : Fin 2) :=
  gate (tables a M base) (prior 0) (prior (index j)) (rhs peer old role j)

theorem field_at (x : Fragment k) (peer ticket : Cell (k+2)) (j : Fin 2) :
    sourceFields (route x peer ticket) (index j)=
      (if (sourceFields x 0).val=1 then (if j.val=0 then peer else ticket) else sourceFields x (index j)) :=by
  rcases x with ⟨tag,d,v,n,c,f,s,m,l,g⟩
  cases tag <;> fin_cases j <;> rfl

theorem other_field (x : Fragment k) (peer ticket : Cell (k+2)) (j : Fin 10)
    (other : j.val≠2 ∧ j.val≠3) : sourceFields (route x peer ticket) j=sourceFields x j :=by
  fin_cases j <;> first
    | rfl
    | exact (other.1 rfl).elim
    | exact (other.2 rfl).elim

def input (banks : Fin 10→Bank) (f : Fin 10) : Expr:=.lookup (banks f) .row
def sweep (base k M rows : ℕ) (banks : Fin 10→Bank) (peer old role : Expr) :=
  DescentPackedFlowBatch.passes (specEnd base (k+2) M) rows (span rows)
    (fun j=>expression (k+2) M base (input banks) peer old role (j:Fin 2)) 0 2

def program (base k M rows w : ℕ) (banks : Fin 10→Bank) (peer old role : Expr) :=
  (mount (pages (k+2) M) (width (k+2) M) w base).seq
    (ProtocolRAM.program w (sweep base k M rows banks peer old role))

def memory (base k M rows : ℕ) (banks : Fin 10→Bank) (peer old role : Expr) (m : Memory w) :=
  result (sweep base k M rows banks peer old role) (after (pages (k+2) M) (width (k+2) M) base m)
def column (base k M rows : ℕ) (j : Fin 2) : Bank :=
  ⟨specEnd base (k+2) M+j.val*span rows,Nat.clog 2 rows⟩
def fields (base k M rows : ℕ) (banks : Fin 10→Bank) (i : Fin 10) : Bank :=
  if i.val=2 then column base k M rows 0 else if i.val=3 then column base k M rows 1 else banks i

def finish (base k M rows : ℕ):=specEnd base (k+2) M+2*span rows
def cost (base k M rows : ℕ) (banks : Fin 10→Bank) (peer old role : Expr):=
  4+10*(4*2^(width (k+2) M))+clock (sweep base k M rows banks peer old role)

variable (base : ℕ) (banks : Fin 10→Bank) (peer old role : Expr)
local notation "N" => H*chunks G M
local notation "u" => k+2
local notation "start" => specEnd base u M
local notation "ts" => tables u M base
local notation "P" => pages u M

def maxField (peer old role : Expr):=44+max peer.work (11*old.work+role.work+11)

theorem operation_work (j : Fin 2) :
    (expression u M base (input banks) peer old role j).work≤ maxField peer old role :=by
  have physical : (DescentPackedRawTicket.ticket old role).work=11*old.work+role.work+11:=by
    simp only [DescentPackedRawTicket.ticket,DescentPackedRawTicket.double,Expr.work];omega
  change ((ts false).read (input banks 0) (input banks (index j))).work+
    ((ts true).read (input banks 0) (rhs peer old role j)).work+1≤_
  simp only [DescentPackedZip.work,input,Expr.work,maxField]
  by_cases first:j.val=0
  · rw [rhs,ite_eq_left first];have:=le_max_left peer.work (11*old.work+role.work+11);omega
  · rw [rhs,ite_eq_right first,physical];have:=le_max_right peer.work (11*old.work+role.work+11);omega

theorem clock_bound (rows : ℕ) :
    cost base k M rows banks peer old role≤
      4+40*2^(width u M)+(4+2*(4+rows*(2*maxField peer old role+4))) :=by
  have per:=DescentPackedFlowBatch.tariff (specEnd base u M) rows (span rows) 2
    (fun i:ℕ=>expression u M base (input banks) peer old role (i:Fin 2)) (maxField peer old role)
    (fun i _=>operation_work base banks peer old role (i:Fin 2))
  unfold cost sweep
  omega

theorem text_bound (rows : ℕ) :
    DescentStaticWordColumn.names (program base k M rows w banks peer old role)≤
      15*(4*2^(width u M)+1)+15+2*(11+4*maxField peer old role) :=by
  have one:=(operation_work (k:=k) (M:=M) base banks peer old role 0)
  have two:=(operation_work (k:=k) (M:=M) base banks peer old role 1)
  rw [program,DescentStaticWordColumn.names_seq]
  have fixed : DescentStaticWordColumn.names (mount P (width u M) w base)=15*(4*2^(width u M)+1) :=
    DescentStaticWordColumn.names_mount w base _ _
  rw [fixed]
  change _+DescentStaticWordColumn.names ((scan w _ rows _).seq ((scan w _ rows _).seq (scan w 0 0 (.lit 0))))≤_
  simp only [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan]
  change 15*(4*2^(width u M)+1)+(11+4*(expression u M base (input banks) peer old role 0).work+
    ((11+4*(expression u M base (input banks) peer old role 1).work)+(11+4*1)))≤_
  omega

theorem run (x : Fin H→Fin G→Fragment k) (peerAt oldAt roleAt : Fin H→Fin G→Cell u) (m : Memory w)
    (within : ∀h g,11*(oldAt h g).val+(roleAt h g).val<2^u)
    (bankFit : ∀i,(banks i).Fits w base) (capacity : ∀i,N≤(banks i).size)
    (priorRead : ∀i,Reads (banks i) (fun h g=>sourceFields (x h g) i) M m)
    (peerFit : peer.Fits w base) (oldFit : old.Fits w base) (roleFit : role.Fits w base)
    (peerRead : Source peer peerAt M m) (oldRead : Source old oldAt M m) (roleRead : Source role roleAt M m)
    (room : finish base k M N<2^w) :
    let next_:=fun h g=>route (x h g) (peerAt h g) (DescentPackedRawTicket.payload oldAt roleAt within h g)
    let after_:=memory base k M N banks peer old role m
    (program base k M N w banks peer old role).Exec m after_ (cost base k M N banks peer old role) ∧
      (∀i,Reads (fields base k M N banks i) (fun h g=>sourceFields (next_ h g) i) M after_) ∧
      (∀i,i<base ∨ finish base k M N≤ i→after_ i=m i) ∧ CheapCode (program base k M N w banks peer old role) :=by
  intro next_ after_
  let loaded:=after P (width u M) base m
  let fn:=fun i:ℕ=>expression u M base (input banks) peer old role (i:Fin 2)
  have bb:base≤ start:=Nat.le_add_right ..
  have near : start<2^w:=(Nat.le_add_right ..).trans_lt room
  have saved (i:ℕ) (hi:i<base) : loaded i=m i:=frame P _ base m i (.inl hi)
  have lift {a':ℕ} (e:Expr) (vals: Fin H→Fin G→Cell a') (fits:e.Fits w base) (read_:Source e vals M m) :
      Source e vals M loaded:=fun p=>(eval_below e _ m loaded fits saved).trans (read_ p)
  have oldColumn (i : Fin 10) : Source (input banks i) (fun h g=>sourceFields (x h g) i) M loaded:=
    lift _ _ (show (input banks i).Fits w base from ⟨bankFit i,True.intro⟩)
      (source_column (banks i) base (bankFit i) m _ (capacity i) (priorRead i))
  let newTicket:=DescentPackedRawTicket.payload oldAt roleAt within
  have parent : Source (DescentPackedRawTicket.ticket old role) newTicket M loaded:=
    DescentPackedRawTicket.ticket_source old role oldAt roleAt loaded (lift _ _ oldFit oldRead) (lift _ _ roleFit roleRead) within
  have masks (c : Bool) : Static (ts c) (mask (a:=u) c) M loaded:=
    binary_mounted (mask (a:=u) c) M P (width u M) base m page_room (atPage c) (table_at c)
  have native (j : Fin 2) :
      (fn j.val).Fits w start ∧ Source (fn j.val) (fun h g=>sourceFields (next_ h g) (index j)) M loaded:=by
    let fresh:=fun h g=>if j.val=0 then peerAt h g else newTicket h g
    have fr : Source (rhs peer old role j) fresh M loaded:=by
      by_cases yes:j.val=0
      · simpa [rhs,fresh,yes] using lift _ _ peerFit peerRead
      · simpa [rhs,fresh,yes] using parent
    have ff : (rhs peer old role j).Fits w base:=by
      by_cases yes:j.val=0 <;> simp [rhs,yes,DescentPackedRawTicket.ticket,DescentPackedRawTicket.double,Expr.Fits,peerFit,oldFit,roleFit]
    have pf (i : Fin 10) : (input banks i).Fits w base:=⟨bankFit i,True.intro⟩
    let left:=input banks 0
    let prev:=input banks (index j)
    let right:=rhs peer old role j
    have bounds (c : Bool) : DescentPackedZip.Fits (ts c) left (if c then right else prev) u u M start w:=by
      refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ bb (pf 0),?_,
        bank_room P _ _ _ _ (page_room _) le_rfl near,bank_room P _ _ _ _ (page_room _) le_rfl near,
        congrArg Page.bits (table_at c 0),congrArg Page.bits (table_at c 1)⟩
      cases c
      · exact ProtocolRAMGeneratedWrite.fits_mono _ bb (pf _)
      · exact ProtocolRAMGeneratedWrite.fits_mono _ bb ff
    have cf (c : Bool) : ((ts c).read left (if c then right else prev)).Fits w start := by
      have z:=bounds c;simp [Tables.read,Expr.Fits,z.left,z.right,z.apply,z.shift]
    have src:=gate_source ts left prev right start loaded bounds masks
      (fun h g=>sourceFields (x h g) 0) (fun h g=>sourceFields (x h g) (index j)) fresh (oldColumn 0) (oldColumn _) fr
    have id_ : (j.val:Fin 2)=j:=Fin.ext (Nat.mod_eq_of_lt j.isLt)
    dsimp only [fn];rw [id_]
    change (gate ts left prev right).Fits w start ∧ _
    constructor
    · exact ⟨cf false,cf true⟩
    · simpa only [expression, left, prev, right, next_, field_at, fresh, newTicket] using src
  have swept:=DescentPackedFlowBatch.execute start N (span N) 2 fn loaded
    (fun i hi=>by
      have h: (⟨i,hi⟩:Fin 2).val=i:=rfl
      exact (native ⟨i,hi⟩).1) room (span_ge N)
  have static_:=DescentOrdinaryAtomFieldRAM.ROM.run P (width u M) base m near
  have before (i : ℕ) (hi : i<base) : after_ i=m i:=
    (swept.2.2 i (hi.trans_le bb)).trans (saved i hi)
  have changed (j : Fin 2) : Reads (column base k M N j) (fun h g=>sourceFields (next_ h g) (index j)) M after_:=
    fun p=>(swept.2.1 j (row H G M p)).trans ((native j).2 p)
  refine ⟨Procedure.Exec.then static_.1 swept.1,?_,?_,cheap_seq (cheap P _ w base) (program_cheap w _)⟩
  · intro i
    by_cases two:i.val=2
    · have z:i=index 0:=Fin.ext two
      subst i;exact changed 0
    by_cases three:i.val=3
    · have z:i=index 1:=Fin.ext three
      subst i;exact changed 1
    simp only [fields,ite_eq_right two,ite_eq_right three]
    intro p
    have read_:=priorRead i p
    have safe : (banks i).base+(row H G M p).val<base :=
      (Nat.add_lt_add_left ((row H G M p).isLt.trans_le (capacity i)) _).trans_le (bankFit i).2.2
    rw [before _ safe]
    simpa only [next_,other_field _ _ _ i ⟨two,three⟩] using read_
  · intro a away
    rcases away with low|high
    · exact before a low
    · exact (DescentPackedFlowBatch.above start N (span N) fn loaded 0 2 a (span_ge N) high).trans
        (frame P _ base m a (.inr ((Nat.le_add_right ..).trans high)))

theorem ready_fields (i : Fin 10) (rows : ℕ) (oldRoom : ∀i,(banks i).Fits w base)
    (oldRows : ∀i,rows≤(banks i).size) (wide : finish base k M rows<2^w) :
    (fields base k M rows banks i).Fits w (finish base k M rows) ∧ rows≤(fields base k M rows banks i).size :=by
  have next (j : Fin 2) : (column base k M rows j).Fits w (finish base k M rows) ∧ rows≤(column base k M rows j).size :=by
    have valid : (column base k M rows j).base+(column base k M rows j).size≤finish base k M rows:=by
      change specEnd base u M+j.val*span rows+span rows≤ specEnd base u M+2*span rows
      have z:=Nat.mul_le_mul_right (span rows) j.isLt
      rw [Nat.succ_mul] at z
      omega
    exact ⟨⟨span_pos _,(Nat.le_add_left ..).trans_lt (valid.trans_lt wide),valid⟩,span_ge _⟩
  have sep : base≤finish base k M rows:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  by_cases two:i.val=2
  · simpa [fields,two] using next 0
  by_cases three:i.val=3
  · simpa [fields,two,three] using next 1
  simp only [fields,ite_eq_right two,ite_eq_right three]
  exact ⟨⟨(oldRoom i).1,(oldRoom i).2.1,(oldRoom i).2.2.trans sep⟩,oldRows i⟩

theorem execute (x : Fin H→Fin G→Fragment k) (peerAt oldAt roleAt : Fin H→Fin G→Cell u) (m : Memory w)
    (within : ∀h g,11*(oldAt h g).val+(roleAt h g).val<2^u)
    (bankFit : ∀i,(banks i).Fits w base) (capacity : ∀i,N≤(banks i).size)
    (priorRead : ∀i,Reads (banks i) (fun h g=>sourceFields (x h g) i) M m)
    (peerFit : peer.Fits w base) (oldFit : old.Fits w base) (roleFit : role.Fits w base)
    (peerRead : Source peer peerAt M m) (oldRead : Source old oldAt M m) (roleRead : Source role roleAt M m)
    (room : finish base k M N<2^w) (word : M*unit k≤w/2) (lanes : 0<M)
    (space : ROM.maskBase (finish base k M N) k M+3*ROM.rows H G M<2^w) :
    let next_:=fun h g=>route (x h g) (peerAt h g) (DescentPackedRawTicket.payload oldAt roleAt within h g)
    let last_:=finish base k M N
    let resolver:=ROM.run last_ k H G M w (fields base k M N banks)
    let machine:=(program base k M N w banks peer old role).seq resolver
    machine.Spec (·=m) (fun _ done=>∀h g (f : Fin 5),
      digit (k+4) f.val (digit (outputWidth k) (lane g lanes).val
        (done (ROM.output last_ k H G M+(row H G M (position h g lanes)).val)).val)=(resolve (next_ h g)).fields f)
      (cost base k M N banks peer old role+(12+120*ROM.page k M+420*N)) ∧ CheapCode machine :=by
  intro next_ last_ resolver machine
  let mid:=memory base k M N banks peer old role m
  have compiled:=run base banks peer old role x peerAt oldAt roleAt m within bankFit capacity priorRead
    peerFit oldFit roleFit peerRead oldRead roleRead room
  have verified:=ROM.execute last_ k H G M w (fields base k M N banks) next_
    (fun j=>(ready_fields base banks j N bankFit capacity room).1)
    (fun j=>(ready_fields base banks j N bankFit capacity room).2) word lanes space mid compiled.2.1
  have stage : (program base k M N w banks peer old role).Spec (·=m) (fun _ after_=>after_=mid)
      (cost base k M N banks peer old role):=by
    apply Procedure.spec_of_exec (f:=fun _=>mid)
    · intro before_ eqn;subst before_;exact compiled.1
    · intro _ _;rfl
  refine ⟨?_,cheap_seq compiled.2.2.2 verified.2⟩
  exact Procedure.Spec.mono (Procedure.Spec.seq stage verified.1 (fun _ _ eqn=>eqn))
    (fun _ ok=>ok) (fun _ _ witnessed=>witnessed.choose_spec.2) le_rfl

end
end Hierarchy.DescentOrdinaryLocalFragment

end OAI

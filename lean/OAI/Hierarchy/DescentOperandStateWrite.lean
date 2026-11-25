import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Four shared name lookups and the three adjacent span pages of a dated operand shelf -/
namespace Hierarchy.DescentOperandStateBanks.Write
open DescentSIMDLookup DescentPackedOperand DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescentOrdinaryAtomFieldRAM.ROM
open scoped Classical Fin.CommRing
noncomputable section

/-- The inputs are physical columns of packed words. The array of aliases uses
the one-based convention of the private first-use instruction. -/
structure Sources (slots : ℕ) where
  keys : Fin slots → Bank
  aliases : Fin slots → Bank
  ranges : Fin slots → Fin 3 → Bank

def pageROM (k b coeff M : ℕ) (i : Fin (4*2)) : Page :=
  let j:=finProdFinEquiv.symm i
  binary (stateTable k b coeff j.1) M j.2

def index (field : Fin 4) (ticket : Fin 2) : Fin (4*2) := finProdFinEquiv (field,ticket)

def aperture (k b M : ℕ) := (outputWidth k+b)*M

def router (k b coeff M base : ℕ) (field : Fin 4) :=
  joined (pageROM k b coeff M) (aperture k b M) base (index field)

theorem page_eq (k b coeff M : ℕ) (field : Fin 4) (j : Fin 2) :
    pageROM k b coeff M (index field j) = binary (stateTable k b coeff field) M j := by
  simp [pageROM,index]

theorem bits (k b coeff M : ℕ) (i : Fin (4*2)) : (pageROM k b coeff M i).bits ≤ aperture k b M := by
  obtain ⟨⟨f,j⟩,rfl⟩:=finProdFinEquiv.surjective i
  rw [show pageROM k b coeff M (finProdFinEquiv (f,j))=binary (stateTable k b coeff f) M j from page_eq ..]
  fin_cases j
  · exact Nat.mul_le_mul_right M (Nat.le_add_right _ _)
  · exact le_rfl

def step {slots : ℕ} (k b coeff M base : ℕ) (B : Sources slots) (pageId : Pages slots) : Expr :=
  let t:=finProdFinEquiv.symm pageId
  if active : t.1.val<4 then
    (router k b coeff M base ⟨t.1.val,active⟩).read (.lookup (B.keys t.2) .row) (.lookup (B.aliases t.2) .row)
  else .lookup (B.ranges t.2 ⟨t.1.val-4,by have:=t.1.isLt;omega⟩) .row

def total {slots : ℕ} (k b coeff M base : ℕ) (B : Sources slots) (j : ℕ) : Expr :=
  if good : j<7*slots then step k b coeff M base B ⟨j,good⟩ else .lit 0

def batch {slots : ℕ} (k b coeff H G M base out : ℕ) (B : Sources slots) :=
  DescentPackedFlowBatch.passes out (pageSize H G M) (pageSize H G M)
    (total k b coeff M base B) 0 (7*slots)

def issue {slots : ℕ} (k b coeff H G M base out w : ℕ) (B : Sources slots) :=
  (mount (pageROM k b coeff M) (aperture k b M) w base).seq
    (program w (batch k b coeff H G M base out B))

def imageAt {slots w : ℕ} (k b coeff H G M base out : ℕ) (B : Sources slots) (m : Memory w) :=
  result (batch k b coeff H G M base out B) (after (pageROM k b coeff M) (aperture k b M) base m)

def work {slots : ℕ} (k b coeff H G M base out : ℕ) (B : Sources slots) :=
  4+10*(8*2^(aperture k b M))+clock (batch k b coeff H G M base out B)

theorem upper {slots : ℕ} (k b coeff H G M base out : ℕ) (B : Sources slots) :
    work k b coeff H G M base out B ≤ 4+10*(8*2^(aperture k b M))+
      (4+(7*slots)*(4+54*pageSize H G M)) := by
  have limited (j : ℕ) (within : j<7*slots) : (total k b coeff M base B j).work≤25 := by
    simp only [total,dite_eq_left within,step]
    split
    · exact le_rfl
    · exact (by decide : 7≤25)
  have billed:=DescentPackedFlowBatch.tariff out (pageSize H G M) (pageSize H G M)
    (7*slots) (total k b coeff M base B) 25 limited
  apply Nat.add_le_add_left
  apply billed.trans_eq
  ring

variable {k b coeff H G M base out w slots : ℕ} (B : Sources slots)
local notation "rows" => pageSize H G M
local notation "book" => pageROM k b coeff M
local notation "wid" => aperture k b M
local notation "tab" f:arg => router k b coeff M base f

structure Early (B : Sources slots) (w base : ℕ) : Prop where
  key : ∀i,(B.keys i).Fits w base
  «alias» : ∀i,(B.aliases i).Fits w base
  span : ∀i j,(B.ranges i j).Fits w base

/-- Each original input column is preserved across the literal ROM printer and
every native output read uses only previously reached cells. -/
theorem run (m : Memory w) (early : Early B w base)
    (apart : base+8*2^wid ≤ out) (room : out+(7*slots)*rows<2^w) :
    let done := imageAt k b coeff H G M base out B m
    let mounted := after book wid base m
    (issue k b coeff H G M base out w B).Exec m done (work k b coeff H G M base out B) ∧
      (∀j : Pages slots,∀i : Fin rows,done (address out rows j i)=
        (step k b coeff M base B j).eval mounted (i.val:Word w)) ∧
      (∀n,n<base ∨ (base+8*2^wid≤n ∧ n<out) ∨ out+(7*slots)*rows≤n → done n=m n) ∧
      (∀f,Static (tab f) (stateTable k b coeff f) M mounted) ∧ CheapCode (issue k b coeff H G M base out w B) := by
  intro done mounted
  have stop : out<2^w := by omega
  have first := DescentOrdinaryAtomFieldRAM.ROM.run book wid base m (apart.trans_lt stop)
  have keep := DescentOrdinaryAtomFieldRAM.ROM.frame book wid base m
  have pause : base≤out := by omega
  have valid (j : ℕ) (live : j<7*slots) : (total k b coeff M base B j).Fits w out := by
    simp only [total,dite_eq_left live,step]
    split
    · next pos =>
      let t:=finProdFinEquiv.symm (⟨j,live⟩ : Pages slots)
      let f : Fin 4:=⟨t.1.val,pos⟩
      have tableFit (i : Fin 2) := bank_room book wid base out (index f i) (bits k b coeff M _) apart stop
      have kFit := early.key t.2
      have aFit := early.«alias» t.2
      exact ⟨tableFit 1,⟨⟨aFit.1,aFit.2.1,aFit.2.2.trans pause⟩,trivial⟩,tableFit 0,
        ⟨kFit.1,kFit.2.1,kFit.2.2.trans pause⟩,trivial⟩
    · next neg =>
      let t := finProdFinEquiv.symm (⟨j,live⟩ : Pages slots)
      let rangeId : Fin 3 := ⟨t.1.val-4,by have bound := t.1.isLt; omega⟩
      have here := early.span t.2 rangeId
      exact ⟨⟨here.1,here.2.1,here.2.2.trans pause⟩,trivial⟩
  obtain ⟨issued,read,below⟩ := DescentPackedFlowBatch.execute out rows rows (7*slots)
    (total k b coeff M base B) mounted valid room le_rfl
  refine ⟨Procedure.Exec.then first.1 issued,?_,?_,fun f=>binary_mounted _ _ book wid base m
    (bits k b coeff M) (index f) (page_eq k b coeff M f),cheap_seq (cheap book wid w base) (program_cheap w _)⟩
  · intro ⟨j,live⟩ i
    simpa only [done,imageAt,batch,mounted,address,bankBase,total,dite_eq_left live] using
      read ⟨j,live⟩ i
  · intro n away
    rcases away with lo|gap|hi
    · exact (below _ (lo.trans_le pause)).trans (keep n (.inl lo))
    · exact (below _ gap.2).trans (keep n (.inr gap.1))
    · have unchanged:=DescentPackedFlowBatch.above out rows rows (total k b coeff M base B) mounted 0 (7*slots) n le_rfl (by simpa using hi)
      exact unchanged.trans (keep n (.inr (by omega)))

/-- The four name fields and three range fields share one fixed row order. -/
structure Values (k b coeff H G slots : ℕ) where
  key : Fin slots → Fin H → Fin G → Cell (outputWidth k)
  «alias» : Fin slots → Fin H → Fin G → Cell b
  span : Fin slots → Fin 3 → Fin H → Fin G → Cell coeff

def Values.field (v : Values k b coeff H G slots) (f : Field) (j : Fin slots) (h : Fin H) (g : Fin G) : Cell coeff :=
  if name : f.val<4 then stateTable k b coeff ⟨f.val,name⟩ (v.key j h g) (v.«alias» j h g)
  else v.span j ⟨f.val-4,by have:=f.isLt;omega⟩ h g

def Reads {d : ℕ} (bank : Bank) (values : Fin H → Fin G → Cell d) (M : ℕ) (m : Memory w) : Prop :=
  ∀p : Row H G M,m (bank.base+(row H G M p).val)=((data values p).val:Word w)

/-- Key and alias producers can be separate native passes. Original ranges can
also refer directly to earlier scalar pages. Only their actual memory readback
is passed between the procedures. -/
structure Input (B : Sources slots) (v : Values k b coeff H G slots) (M : ℕ) (m : Memory w) : Prop where
  key : ∀j,Reads (B.keys j) (v.key j) M m
  «alias» : ∀j,Reads (B.aliases j) (v.«alias» j) M m
  span : ∀j f,Reads (B.ranges j f) (v.span j f) M m
  keyCap : ∀j,pageSize H G M ≤ (B.keys j).size
  aliasCap : ∀j,pageSize H G M ≤ (B.aliases j).size
  spanCap : ∀j f,pageSize H G M ≤ (B.ranges j f).size

theorem published (v : Values k b coeff H G slots) (m : Memory w) (early : Early B w base)
    (apart : base+8*2^wid ≤ out) (room : out+(7*slots)*rows<2^w) (prior : Input B v M m) :
    let done := imageAt k b coeff H G M base out B m
    (issue k b coeff H G M base out w B).Exec m done (work k b coeff H G M base out B) ∧
      (∀f j r,done (address out rows (page f j) (row H G M r))=((data (v.field f j) r).val:Word w)) ∧
      (∀n,n<base ∨ (base+8*2^wid≤n ∧ n<out) ∨ out+(7*slots)*rows≤n → done n=m n) ∧
      CheapCode (issue k b coeff H G M base out w B) := by
  intro done
  let mounted:=after book wid base m
  obtain ⟨exec_,output,unchanged,dict,cheap_⟩:=run B m early apart room
  have same (z : ℕ) (low : z<base) : mounted z=m z := DescentOrdinaryAtomFieldRAM.ROM.frame book wid base m z (.inl low)
  have stop : out<2^w := by omega
  have old {a : ℕ} (bank : Bank) (u : Fin H → Fin G → Cell a) (fit : bank.Fits w base)
      (cap : rows≤bank.size) (read : Reads bank u M m) : Source (.lookup bank .row) u M mounted := by
    apply source_column bank base fit mounted u cap
    intro p
    have hi := (row H G M p).isLt.trans_le cap
    exact (same _ (by have:=fit.2.2;omega)).trans (read p)
  refine ⟨exec_,?_,unchanged,cheap_⟩
  intro f j r
  refine (output (page f j) (row H G M r)).trans ?_
  by_cases h : f.val<4
  · let n : Fin 4:=⟨f.val,h⟩
    have nameField : v.field f j = fun host group =>
        stateTable k b coeff n (v.key j host group) (v.«alias» j host group) := by
      funext host group
      simp only [Values.field,dite_eq_left h,n]
    rw [nameField]
    have up := Nat.le_trans (Nat.le_add_right base _) apart
    have keyFit:=early.key j
    have aliasFit:=early.«alias» j
    have keyUp : (B.keys j).Fits w out:=⟨keyFit.1,keyFit.2.1,keyFit.2.2.trans up⟩
    have aliasUp : (B.aliases j).Fits w out:=⟨aliasFit.1,aliasFit.2.1,aliasFit.2.2.trans up⟩
    have bin (i : Fin 2):=bank_room book wid base out (index n i) (bits k b coeff M _) apart stop
    have fits : DescentPackedZip.Fits (tab n) (.lookup (B.keys j) .row) (.lookup (B.aliases j) .row)
        (outputWidth k) b M out w := ⟨⟨keyUp,trivial⟩,⟨aliasUp,trivial⟩,bin 0,bin 1,
          congrArg Page.bits (page_eq k b coeff M n 0),congrArg Page.bits (page_eq k b coeff M n 1)⟩
    simpa only [step,page,Equiv.symm_apply_apply,dite_eq_left h] using
      DescentPackedZip.read_data (tab n) _ _ out fits (stateTable k b coeff n) (stateTable_zero k b coeff n) mounted
        (dict n) (v.key j) (v.«alias» j) (old _ _ keyFit (prior.keyCap j) (prior.key j))
        (old _ _ aliasFit (prior.aliasCap j) (prior.«alias» j)) r
  · let rangeId : Fin 3 := ⟨f.val-4,by have bound := f.isLt; omega⟩
    have rangeField : v.field f j = v.span j rangeId := by
      funext host group
      simp only [Values.field,dite_eq_right h,rangeId]
    rw [rangeField]
    simpa only [step,page,Equiv.symm_apply_apply,dite_eq_right h] using
      old _ _ (early.span j rangeId) (prior.spanCap j rangeId) (prior.span j rangeId) r

end
end Hierarchy.DescentOperandStateBanks.Write

end OAI

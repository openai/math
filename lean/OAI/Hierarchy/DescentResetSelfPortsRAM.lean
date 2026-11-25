import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentScalarHaloPortROM
import OAI.Hierarchy.DescentSortedRosterTariff
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Sorting the emitted three-neighbor reset output with its physical receiver -/
noncomputable section
namespace Hierarchy.DescentResetSelfPortsRAM
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSortedRoster
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
variable {w H G M : ℕ}

private def selfPeers (peers : Fin H → Fin 3 → Option (Fin H)) (v : Fin H) : Fin 4 → Option (Fin H) :=
  Fin.cases (some v) (peers v)

def pad (H : ℕ) := 2^Nat.clog 2 (H*4)
def localBase (base H : ℕ) := base+pad H
def portBase (base H : ℕ) := base+4*pad H
def rawBase (base H G M : ℕ) := DescentScalarHaloPortROM.stop H G M 4 (portBase base H)
def rankBase (base H G M : ℕ) := rawBase base H G M+pad H
def endAddress (base H G M : ℕ) := rankBase base H G M+pad H
theorem extent (base H G M : ℕ) :
    endAddress base H G M=base+endAddress 0 H G M := by
  simp [endAddress,rankBase,rawBase,portBase,DescentScalarHaloPortROM.stop,Nat.add_assoc]

theorem bounded {ι : ℕ→Type*} {H G M : ∀h,ι h→ℕ} (hi : DescentDatedAddressBook.Bounded H)
    (gi : DescentDatedAddressBook.Bounded G) (mi : DescentDatedAddressBook.Bounded M) :
    DescentDatedAddressBook.Bounded (fun h i=>endAddress 0 (H h i) (G h i) (M h i)) := by
  let num:=fun h i=>H h i*chunks (G h i) (M h i)
  have n : DescentDatedAddressBook.Bounded num:=
    hi.mul (DescentDatedAddressBook.Bounded.div (DescentDatedAddressBook.Bounded.sub (gi.add mi)))
  have four:=DescentDatedAddressBook.Bounded.const (ι:=ι) 4
  have many:=hi.mul four
  have p:=many.padded
  have sr:=(((many.max' (n.max' hi)).add (.const 1)).padded)
  have span:=(four.mul n).add (hi.add (n.add many))
  exact (((((DescentDatedAddressBook.Bounded.const 0).add (four.mul p)).add span).add sr).add p).add p

def «at» (base H : ℕ) : Bank := ⟨base,Nat.clog 2 (H*4)⟩
def ports (base H G M : ℕ) := DescentScalarHaloPortROM.chart H G M 4 (portBase base H) («at» (rankBase base H G M) H)
theorem roster_fits {w : ℕ} (base H G M : ℕ) (room : endAddress base H G M<2^w) :
    (ports base H G M).roster.Fits w (endAddress base H G M) ∧ H*4≤(ports base H G M).roster.size :=
  ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left (pad H) (rankBase base H G M)).trans_lt room,le_rfl⟩,
    Nat.le_pow_clog (by decide : 1 < 2) (H*4)⟩

def shape (H s j : ℕ) :=
  let v:=j/4
  if s=0 then v else if s=1 then v*4 else (j%4-1)*H+v
def literal (H j : ℕ) := shape H (j/pad H) (j%pad H)
def rawExpr (prior base H G M : ℕ) : Expr :=
  .branch .eq (.lookup (DescentScalarHaloPortROM.slot H G M 4 (portBase base H)) .row) (.lit 0)
    (.lookup («at» (localBase base H) H) .row)
    (.lookup («at» prior H) (.lookup («at» (localBase base H+2*pad H) H) .row))
def chart (base H G M : ℕ) : Chart := ⟨«at» (rawBase base H G M) H,
  «at» (localBase base H+pad H) H,DescentScalarHaloPortROM.slot H G M 4 (portBase base H)⟩

def program (prior base H G M w : ℕ) :=
  (((DescentStaticWordColumn.program w (localBase base H) (literal H) (3*pad H)).seq
    (DescentScalarHaloPortROM.program H G M 4 w (portBase base H))).seq
    (scan w (rawBase base H G M) (H*4) (rawExpr prior base H G M))).seq
    (scan w (rankBase base H G M) (H*4) (code (chart base H G M) 4 H))

private theorem cheapProgram (prior base H G M w : ℕ) : CheapCode (program prior base H G M w) := by
  let head := DescentStaticWordColumn.program w (localBase base H) (literal H) (3*pad H)
  let ports := DescentScalarHaloPortROM.program H G M 4 w (portBase base H)
  let raw := scan w (rawBase base H G M) (H*4) (rawExpr prior base H G M)
  let rank := scan w (rankBase base H G M) (H*4) (code (chart base H G M) 4 H)
  exact @cheap_seq w ((head.seq ports).seq raw) rank
    (@cheap_seq w (head.seq ports) raw
      (@cheap_seq w head ports
        (@DescentStaticWordColumn.cheap w (localBase base H) (literal H) (3*pad H))
        (@DescentStaticWordColumn.cheap w (portBase base H) (DescentScalarHaloPortROM.literal H G M 4)
          (DescentScalarHaloPortROM.length H G M 4)))
      (@scan_cheap w (rawBase base H G M) (H*4) (rawExpr prior base H G M)))
    (@scan_cheap w (rankBase base H G M) (H*4) (code (chart base H G M) 4 H))

def memory (prior base H G M : ℕ) (m : Memory w) :=
  let hdr:=DescentStaticWordColumn.image (localBase base H) (literal H) m (3*pad H)
  let stat:=DescentScalarHaloPortROM.image H G M 4 (portBase base H) hdr
  let raw:=image (rawBase base H G M) (H*4) (rawExpr prior base H G M) stat
  image (rankBase base H G M) (H*4) (code (chart base H G M) 4 H) raw

def ticks (prior base H G M : ℕ) := (((4+10*(3*pad H))+(4+10*DescentScalarHaloPortROM.length H G M 4))+
    (4+(H*4)*(2*(rawExpr prior base H G M).work+4)))+(4+(H*4)*(2*(code (chart base H G M) 4 H).work+4))

theorem tariff (prior base H G M w : ℕ) :
    ticks prior base H G M ≤ (((4+10*(3*pad H))+(4+10*DescentScalarHaloPortROM.length H G M 4))+
      (4+(H*4)*84))+(4+(H*4)*25004) ∧
    DescentStaticWordColumn.names (program prior base H G M w)≤
      15*(3*pad H+1)+15*(DescentScalarHaloPortROM.length H G M 4+1)+171+50011 := by
  have raw : (rawExpr prior base H G M).work≤40:=by simp [rawExpr,Expr.work]
  have ranked : (code (chart base H G M) 4 H).work≤12500:=code_work _ _ _
  constructor
  · exact Nat.add_le_add (Nat.add_le_add_left (Nat.add_le_add_left (Nat.mul_le_mul_left (H*4) (by omega)) 4) _)
      (Nat.add_le_add_left (Nat.mul_le_mul_left (H*4) (by omega)) 4)
  · simp only [program,DescentScalarHaloPortROM.program,DescentStaticWordColumn.names_seq,
      DescentStaticWordColumn.names_scan,DescentStaticWordColumn.names_mount]
    omega

private theorem idx (v : Fin H) (j : Fin 4) : v.val*4+j.val<H*4 :=
  (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)

private theorem headRead (base : ℕ) (m : Memory w) (v : Fin H) (j : Fin 4) (s : Fin 3) :
    DescentStaticWordColumn.image (localBase base H) (literal H) m (3*pad H)
      (localBase base H+s.val*pad H+(v.val*4+j.val))=
      ((if s.val=0 then v.val else if s.val=1 then v.val*4 else (j.val-1)*H+v.val:ℕ):Word w) := by
  let n:=v.val*4+j.val
  have bound : n<pad H:=(idx v j).trans_le (Nat.le_pow_clog (by decide) _)
  have fits : s.val*pad H+n<3*pad H:=(Nat.add_lt_add_left bound _).trans_le (by
    rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ s.isLt)
  have split_ (d k j : ℕ) (pos : 0<d) (lt : j<d) : (k*d+j)/d=k ∧ (k*d+j)%d=j := by
    rw [Nat.mul_comm k d,Nat.mul_add_div pos,Nat.div_eq_of_lt lt,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt lt,Nat.add_zero]
    exact ⟨rfl,rfl⟩
  have outer:=split_ (pad H) s.val n (Nat.two_pow_pos _) bound
  have inner : n/4 = v.val ∧ n%4 = j.val := split_ 4 v.val j.val (by decide : 0<4) j.isLt
  rw [Nat.add_assoc,DescentStaticWordColumn.read _ _ _ m fits]
  simp only [literal,shape,outer.1,outer.2,inner.1,inner.2]

/-- The prior issuer supplies three consecutive host columns. Their numeric
directory is sorted and deduplicated together with the receiver itself.
Each later field bank uses the same physical four-port chart. -/
theorem run (prior base H G M : ℕ) (m : Memory w) (peers : Fin H→Fin 3→Option (Fin H))
    (priorEnd : prior+3*H≤base) (smallH : H<2^w) (four : 4<2^w)
    (issued : ∀(v : Fin H) (j : Fin 3),m (prior+j.val*H+v.val)=(target (peers v j):Word w))
    (room : endAddress base H G M<2^w) :
    let o:=memory prior base H G M m
    (program prior base H G M w).Exec m o (ticks prior base H G M) ∧
      Mounted (ports base H G M) (indexed (selfPeers peers)) o G M ∧
      (∀src : Bank,src.Fits w (endAddress base H G M)→H*chunks G M≤ src.size→
        Accessible (ports base H G M) src H G M w (endAddress base H G M)) ∧
      (∀z,z<base ∨ endAddress base H G M≤z → o z=m z) ∧ CheapCode (program prior base H G M w) := by
  intro o
  let n:=H*4
  let slots:=DescentScalarHaloPortROM.slot H G M 4 (portBase base H)
  let old:=«at» prior H
  let header:=localBase base H
  let p:=pad H
  let pb:=portBase base H
  let rb:=rawBase base H G M
  let sb:=rankBase base H G M
  let stop:=endAddress base H G M
  let staticLen:=DescentScalarHaloPortROM.length H G M 4
  let sortedBank:=«at» sb H
  let hdr:=DescentStaticWordColumn.image header (literal H) m (3*p)
  let stat:=DescentScalarHaloPortROM.image H G M 4 pb hdr
  let raw:=image rb n (rawExpr prior base H G M) stat
  have cover : n≤p:=Nat.le_pow_clog (by decide : 1 < 2) n
  have before : header+3*p=pb:=by dsimp only [header,pb,localBase,portBase,p];omega
  have staticEnd : pb+staticLen≤rb:=Nat.le_add_right (pb+staticLen) (DescentScalarHaloPortROM.pad H G M 4)
  have hb : base≤header:=Nat.le_add_right ..
  have headerPb : header≤pb := (Nat.le_add_right header (3*p)).trans_eq before
  have pbRb : pb≤rb:=(Nat.le_add_right pb staticLen).trans staticEnd
  have rawEnd : rb+n≤ sb:=Nat.add_le_add_left cover _
  have sortEnd : sb+n≤ stop:=Nat.add_le_add_left cover _
  have rbSb : rb≤ sb:=Nat.le_add_right ..
  have sbStop : sb≤ stop:=Nat.le_add_right ..
  have allRoom : rb<2^w:=rbSb.trans_lt (sbStop.trans_lt room)
  have prep : (DescentStaticWordColumn.program w header (literal H) (3*p)).Exec m hdr (4+10*(3*p)) :=
    DescentStaticWordColumn.mount header (3*p) (literal H) m (before.trans_lt (pbRb.trans_lt allRoom))
  have shapeRun:=DescentScalarHaloPortROM.mount H G M 4 pb sortedBank hdr (staticEnd.trans_lt allRoom)
  have statics:=DescentScalarHaloPortROM.statics H G M 4 pb rb sortedBank le_rfl allRoom
  have cut (addr : ℕ) {dst : ℕ} (fits : addr+p≤dst) (end_ : dst<2^w) :
      («at» addr H).Fits w dst :=⟨Nat.two_pow_pos _,(Nat.le_add_left p addr).trans_lt (fits.trans_lt end_),fits⟩
  have priorLow : prior≤base:=(Nat.le_add_right prior (3*H)).trans priorEnd
  have firstBound : prior+p≤header:=Nat.add_le_add_right priorLow p
  have fOld : old.Fits w rb:=cut prior (firstBound.trans (headerPb.trans pbRb)) allRoom
  have fSelf : («at» header H).Fits w rb:=cut header (dst:=rb) (by omega) allRoom
  have fOrigin : («at» (header+p) H).Fits w rb:=cut (header+p) (dst:=rb) (by omega) allRoom
  have fInput : («at» (header+2*p) H).Fits w rb:=cut (header+2*p) (dst:=rb) (by omega) allRoom
  have rawFit : (rawExpr prior base H G M).Fits w rb :=
    ⟨⟨statics.2.2.2.1,trivial⟩,trivial,⟨fSelf,trivial⟩,⟨fOld,⟨fInput,trivial⟩⟩⟩
  have scanRaw : (scan w rb n (rawExpr prior base H G M)).Exec stat raw
      (4+n*(2*(rawExpr prior base H G M).work+4)) :=
    scan_exec rb n (rawExpr prior base H G M) stat rawFit (rawEnd.trans_lt (sbStop.trans_lt room))
  have head (v : Fin H) (j : Fin 4) (s : Fin 3) :
      stat (header+s.val*p+(v.val*4+j.val))=
        ((if s.val=0 then v.val else if s.val=1 then v.val*4 else (j.val-1)*H+v.val:ℕ):Word w) := by
    have low : header+s.val*p+(v.val*4+j.val)<pb := by
      have bounds:=Nat.mul_le_mul_right p s.isLt
      rw [Nat.succ_mul] at bounds
      have row:=(idx v j).trans_le cover
      omega
    exact (shapeRun.2.2.1 _ (.inl low)).trans (headRead base m v j s)
  have earlyRead (v : Fin H) (j : Fin 3) : stat (prior+j.val*H+v.val)=(target (peers v j):Word w) := by
    have low : prior+j.val*H+v.val<base := by
      have z:=Nat.mul_le_mul_right H j.isLt
      rw [Nat.succ_mul] at z
      have h:=v.isLt
      omega
    exact (shapeRun.2.2.1 _ (.inl (low.trans_le (hb.trans headerPb)))).trans
      ((DescentStaticWordColumn.frame header (3*p) (literal H) m _ (.inl (low.trans_le hb))).trans (issued v j))
  have rowWord (v : Fin H) (j : Fin 4) : raw (rb+(v.val*4+j.val))=(target (selfPeers peers v j):Word w) := by
    let ix := v.val*4+j.val
    let rowI : Fin n := ⟨ix,idx v j⟩
    have roomI : ix < p := (idx v j).trans_le cover
    have sl : slots.read stat (ix : Word w) = (j.val : Word w) :=
      (DescentPackedZip.bank_read slots stat ((idx v j).trans_le statics.2.2.2.2) statics.2.2.2.1).trans
        (shapeRun.2.1.slots v j)
    have h₀ : («at» header H).read stat (ix : Word w) = (v.val : Word w) :=
      (DescentPackedZip.bank_read («at» header H) stat roomI fSelf).trans
        (by simpa [ix, «at»] using head v j 0)
    have h₂ : («at» (header+2*p) H).read stat (ix : Word w) = (((j.val-1)*H+v.val : ℕ) : Word w) :=
      (DescentPackedZip.bank_read («at» (header+2*p) H) stat roomI fInput).trans
        (by simpa [ix, «at»] using head v j 2)
    have selectPeer (k : Fin 4) :
        (if (k.val : Word w) = 0 then (v.val : Word w)
         else old.read stat (((k.val-1)*H+v.val : ℕ) : Word w)) =
        (target (Fin.cases (some v) (peers v) k) : Word w) := by
      cases k using Fin.cases with
      | zero => simp [DescentPackedColony.target]
      | succ d =>
        have value : d.val*H+v.val < old.size := by
          have z := Nat.mul_le_mul_right H d.isLt
          rw [Nat.succ_mul] at z
          have hv := v.isLt
          change _ < p
          change H*4 ≤ p at cover
          omega
        have nz : (d.succ.val : Word w) ≠ 0 := by
          intro eqn
          have z := congrArg Fin.val eqn
          rw [Fin.val_cast_of_lt (d.succ.isLt.trans four),Fin.val_zero] at z
          exact Nat.succ_ne_zero _ z
        rw [ite_eq_right nz]
        change old.read stat ((d.val*H+v.val : ℕ) : Word w) = (target (peers v d) : Word w)
        exact (DescentPackedZip.bank_read old stat value fOld).trans
          (by simpa only [old, «at», Nat.add_assoc] using earlyRead v d)
    refine (ProtocolRAMGeneratedWrite.read_image rb n (rawExpr prior base H G M) stat rowI).trans ?_
    change (if (slots.read stat (ix : Word w) == (0 : Word w)) = true
      then («at» header H).read stat (ix : Word w)
      else old.read stat ((«at» (header+2*p) H).read stat (ix : Word w))) = _
    simp only [sl,h₀,h₂,beq_iff_eq]
    exact selectPeer j
  have sortedRoom : DescentSortedRoster.Room (chart base H G M) 4 H w sb := by
    refine ⟨?_,smallH,four,sortEnd.trans_lt room⟩
    intro b hb
    change b ∈ [«at» rb H,«at» (header+p) H,slots] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl
    · exact ⟨cut rb (dst:=sb) le_rfl (sbStop.trans_lt room),cover⟩
    · exact ⟨cut (header+p) (dst:=sb) (by omega) (sbStop.trans_lt room),cover⟩
    · exact ⟨⟨statics.2.2.2.1.1,statics.2.2.2.1.2.1,statics.2.2.2.1.2.2.trans rbSb⟩,statics.2.2.2.2⟩
  have rawFrame (z : ℕ) (away : z < rb ∨ rb+n ≤ z) : raw z = stat z :=
    ProtocolRAMGeneratedWrite.frame_image rb n (rawExpr prior base H G M) stat z away
  have sortedFrame (z : ℕ) (away : z < sb ∨ sb+n ≤ z) : o z = raw z :=
    ProtocolRAMGeneratedWrite.frame_image sb n (code (chart base H G M) 4 H) raw z away
  have fourRows : Raw (chart base H G M) (selfPeers peers) raw := by
    refine ⟨?_,?_,rowWord⟩
    · intro v j
      apply (rawFrame ((header+p)+(v.val*4+j.val))
        (.inl ((Nat.add_lt_add_left ((idx v j).trans_le cover) (header+p)).trans_le fOrigin.2.2))).trans
      simpa using head v j 1
    · intro v j
      exact (rawFrame (slots.base+(v.val*4+j.val))
        (.inl ((Nat.add_lt_add_left ((idx v j).trans_le statics.2.2.2.2) slots.base).trans_le
          statics.2.2.2.1.2.2))).trans (shapeRun.2.1.slots v j)
  have sorted:=DescentSortedRoster.issued (chart base H G M) (selfPeers peers) raw sb sortedRoom fourRows
  have lower (z : ℕ) (lt : z < rb) : o z=stat z :=
    (sortedFrame z (.inl (lt.trans_le rbSb))).trans (rawFrame z (.inl lt))
  refine ⟨?_,⟨?_,sorted.2.1,?_,?_⟩,
    fun src sf ss=>(DescentScalarHaloPortROM.geometry H G M 4 pb stop sortedBank src (rbSb.trans sbStop) room
      (cut sb le_rfl room) cover sf ss).1,?_,?_⟩
  · intro labels regs pubs machine
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (@prep) shapeRun.1) (@scanRaw)) sorted.1 machine
  · intro p i;exact (lower _ ((Nat.add_lt_add_left ((row H G M p).isLt.trans_le (statics.1 i).2) _).trans_le (statics.1 i).1.2.2)).trans (shapeRun.2.1.ids i p)
  · intro h;exact (lower _ ((Nat.add_lt_add_left (h.isLt.trans_le statics.2.1.2) _).trans_le statics.2.1.1.2.2)).trans (shapeRun.2.1.offsets h)
  · intro u;exact (lower _ ((Nat.add_lt_add_left ((row H G M u).isLt.trans_le statics.2.2.1.2) _).trans_le statics.2.2.1.1.2.2)).trans (shapeRun.2.1.chunks u)
  · intro z away
    rcases away with lo|hi
    · have l:=lo.trans_le hb
      have r:=l.trans_le headerPb
      exact (lower _ (r.trans_le pbRb)).trans ((shapeRun.2.2.1 z (.inl r)).trans (DescentStaticWordColumn.frame header (3*p) (literal H) m z (.inl l)))
    · exact (sortedFrame z (.inr (sortEnd.trans hi))).trans
        ((rawFrame z (.inr (rawEnd.trans (sbStop.trans hi)))).trans
        ((shapeRun.2.2.1 z (.inr (staticEnd.trans (rbSb.trans (sbStop.trans hi))))).trans
          (DescentStaticWordColumn.frame header (3*p) (literal H) m z
            (.inr (before.trans_le (pbRb.trans (rbSb.trans (sbStop.trans hi))))))))
  · exact @cheapProgram prior base H G M w

/-- Executability and the two-sided frame also hold on arbitrary memory. -/
theorem any (prior base H G M : ℕ) (m : Memory w) (priorEnd : prior+3*H≤base)
    (smallH : H<2^w) (four : 4<2^w) (room : endAddress base H G M<2^w) :
    let o:=memory prior base H G M m
    (program prior base H G M w).Exec m o (ticks prior base H G M) ∧
      (∀z,z<base ∨ endAddress base H G M≤z → o z=m z) ∧ CheapCode (program prior base H G M w) := by
  intro o
  let head_:=localBase base H
  let pb:=portBase base H
  let rb:=rawBase base H G M
  let sb:=rankBase base H G M
  let stop:=endAddress base H G M
  let p:=pad H
  let n:=H*4
  let hdr:=DescentStaticWordColumn.image head_ (literal H) m (3*p)
  let metadata:=DescentScalarHaloPortROM.image H G M 4 pb hdr
  let raw:=image rb n (rawExpr prior base H G M) metadata
  have cover : n≤p:=Nat.le_pow_clog (by decide) _
  have headerStart : base≤head_:=Nat.le_add_right ..
  have headEnd : head_+3*p=pb:=by dsimp only [head_,localBase,p,pb,portBase];omega
  have pe : pb+DescentScalarHaloPortROM.length H G M 4≤rb:=Nat.le_add_right ..
  have re : rb+n≤ sb:=Nat.add_le_add_left cover rb
  have se : sb+n≤ stop:=Nat.add_le_add_left cover sb
  have before : head_≤pb:=(Nat.le_add_right ..).trans_eq headEnd
  have pbRb : pb≤rb:=(Nat.le_add_right ..).trans pe
  have rbSb : rb≤ sb:=Nat.le_add_right ..
  have budget : sb<2^w:=(Nat.le_add_right ..).trans_lt room
  have rawBudget : rb<2^w:=rbSb.trans_lt budget
  have st:=DescentScalarHaloPortROM.statics H G M 4 pb rb («at» sb H) le_rfl rawBudget
  have ps:=DescentScalarHaloPortROM.mount H G M 4 pb («at» sb H) hdr (pe.trans_lt rawBudget)
  have good : ∀addr dst,addr+p≤dst→dst<2^w→(«at» addr H).Fits w dst:=
    fun addr dst lo hi=>⟨Nat.two_pow_pos _,(Nat.le_add_left p addr).trans_lt (lo.trans_lt hi),lo⟩
  have oldEnd : prior+p≤head_:=Nat.add_le_add_right ((Nat.le_add_right prior (3*H)).trans priorEnd) p
  have headRoom := good head_ rb (by omega) rawBudget
  have originRoom := good (head_+2*p) rb (by omega) rawBudget
  have priorRoom := good prior rb ((oldEnd.trans before).trans pbRb) rawBudget
  have fr : (rawExpr prior base H G M).Fits w rb:=
    ⟨⟨st.2.2.2.1,trivial⟩,trivial,⟨headRoom,trivial⟩,
      ⟨priorRoom,⟨originRoom,trivial⟩⟩⟩
  have sr : DescentSortedRoster.Room (chart base H G M) 4 H w sb:=by
    refine ⟨?_,smallH,four,se.trans_lt room⟩
    intro v hv
    change v ∈ [«at» rb H,«at» (head_+p) H,DescentScalarHaloPortROM.slot H G M 4 pb] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl
    · exact ⟨good rb sb le_rfl budget,cover⟩
    · exact ⟨good (head_+p) sb (by omega) budget,cover⟩
    · exact ⟨⟨st.2.2.2.1.1,st.2.2.2.1.2.1,st.2.2.2.1.2.2.trans rbSb⟩,st.2.2.2.2⟩
  have mh : (DescentStaticWordColumn.program w head_ (literal H) (3*p)).Exec m hdr (4+10*(3*p)) :=
    DescentStaticWordColumn.mount head_ (3*p) (literal H) m (headEnd.trans_lt (pbRb.trans_lt rawBudget))
  have rawRun : (scan w rb n (rawExpr prior base H G M)).Exec metadata raw
      (4+n*(2*(rawExpr prior base H G M).work+4)) :=
    scan_exec rb n (rawExpr prior base H G M) metadata fr (re.trans_lt budget)
  have sortRun : (scan w sb n (code (chart base H G M) 4 H)).Exec raw o
      (4+n*(2*(code (chart base H G M) 4 H).work+4)) :=
    scan_exec sb n (code (chart base H G M) 4 H) raw
      (built_fits (chart base H G M) sb sr) sr.endFit
  refine ⟨?_,?_,?_⟩
  · intro labels regs pubs machine
    exact Procedure.Exec.then
      (Procedure.Exec.then (Procedure.Exec.then (@mh) ps.1) (@rawRun)) (@sortRun) machine
  · intro z outside
    have ss : sb ≤ stop := Nat.le_add_right ..
    have zHead : z<head_ ∨ head_+3*p≤z :=
      outside.imp (fun lo => lo.trans_le headerStart)
        (fun hi => headEnd.le.trans (pbRb.trans (rbSb.trans (ss.trans hi))))
    have zPorts : z<pb ∨ pb+DescentScalarHaloPortROM.length H G M 4≤z :=
      outside.imp (fun lo => lo.trans_le (headerStart.trans before))
        (fun hi => pe.trans (rbSb.trans (ss.trans hi)))
    have zRaw : z<rb ∨ rb+n≤z :=
      outside.imp (fun lo => lo.trans_le (headerStart.trans (before.trans pbRb)))
        (fun hi => re.trans (ss.trans hi))
    have zSort : z<sb ∨ sb+n≤z :=
      outside.imp (fun lo => lo.trans_le (headerStart.trans (before.trans (pbRb.trans rbSb))))
        (fun hi => se.trans hi)
    calc
      o z = raw z := ProtocolRAMGeneratedWrite.frame_image sb n (code (chart base H G M) 4 H) raw z zSort
      _ = metadata z := ProtocolRAMGeneratedWrite.frame_image rb n (rawExpr prior base H G M) metadata z zRaw
      _ = hdr z := ps.2.2.1 z zPorts
      _ = m z := DescentStaticWordColumn.frame head_ (3*p) (literal H) m z zHead
  · exact @cheapProgram prior base H G M w

end Hierarchy.DescentResetSelfPortsRAM
end

end OAI

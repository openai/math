import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.DescentPackedFlowPublication
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # The public tables for directed and reciprocal packed flow
The prior stage supplies the signed token columns and its sorted roster.
A literal packed gate book and one row-address table are installed above them.
-/
namespace Hierarchy.DescentPackedFlowPublication.Book
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D r c b d w H J M : ℕ}

def width (b r d : ℕ) := max (b*r+d) (b*r+b*r)

def gate (D r b d grain : ℕ) : Fin (D*r+1) → DescentPackedZip.Book.Gate :=
  Fin.lastCases ⟨b*r,b*r,b*r,DescentPackedFlowPair.add (b:=b) (r:=r)⟩ (fun i =>
    let t : Fin D × Fin r := finProdFinEquiv.symm i
    ⟨b*r,d,b*r,DescentPackedFlowRAM.insert (b:=b) (d:=d) grain t.1.val t.2⟩)

def insId (i : Fin D) (x : Fin r) : Fin (D*r+1) := (finProdFinEquiv (i,x)).castSucc
def addId (D r : ℕ) := Fin.last (D*r)

private theorem ins_gate (i : Fin D) (x : Fin r) (b d grain : ℕ) :
    gate D r b d grain (insId i x)=⟨b*r,d,b*r,DescentPackedFlowRAM.insert grain i.val x⟩ := by
  simp only [gate,insId,Fin.lastCases_castSucc,Equiv.symm_apply_apply]

private theorem add_gate (D r b d grain : ℕ) :
    gate D r b d grain (addId D r)=⟨b*r,b*r,b*r,DescentPackedFlowPair.add⟩ := by
  simp [gate,addId]

private theorem widths (D r b d grain : ℕ) (j : Fin (D*r+1)) :
    (gate D r b d grain j).left+(gate D r b d grain j).right≤width b r d := by
  refine Fin.lastCases ?_ (fun i=>?_) j
  · simp [gate,width]
  · simp [gate,width]

def gateWords (D r b d M : ℕ) := (D*r+1)*(2*2^(width b r d*M))
def indexWords (D bits : ℕ) := (D+4)*2^bits

def indexBank (base bits j : ℕ) : Bank := ⟨base+j*2^bits,bits⟩
def indexData (D n bits a : ℕ) : ℕ :=
  let field:=a/2^bits
  let j:=a%2^bits
  if field<D then (j/n)*D+field
  else if field=D then n*j
  else if field=D+1 then j%n
  else if field=D+2 then j*D
  else j/n

def layout (tokens : DescentPackedFlowRAM.Slot r c→Bank) (roster : Bank)
    (floor bits D b d grain M : ℕ) : Layout D r c :=
  let atIndex:=floor+gateWords D r b d M
  let table:=DescentPackedZip.Book.tables (gate D r b d grain) (width b r d) M floor
  ⟨tokens,fun j x=>table (insId j x),
    ⟨fun j=>indexBank atIndex bits j.val,roster,indexBank atIndex bits D,indexBank atIndex bits (D+1)⟩,
    ⟨indexBank atIndex bits (D+2),indexBank atIndex bits (D+3)⟩,table (addId D r),
    atIndex+indexWords D bits,bits⟩

def pitchBits (hosts top : ℕ) := Nat.clog 2 hosts+top
theorem pitch_room (hosts top : ℕ) : hosts*2^top≤2^pitchBits hosts top := by
  rw [pitchBits,pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) hosts)

theorem pitch_upper (hosts top : ℕ) : 2^pitchBits hosts top≤(2*hosts+1)*2^top := by
  rw [pitchBits,pow_add]
  apply Nat.mul_le_mul_right
  cases h : Nat.clog 2 hosts with
  | zero => simp
  | succ n =>
    have prev : 2^n<hosts := (Nat.lt_clog_iff_pow_lt (b:=2) (by decide)).mp (by omega)
    rw [pow_succ]
    omega

def install (w floor bits D r b d grain J M : ℕ) :=
  (DescentPackedZip.Book.install (gate D r b d grain) (width b r d) M w floor).seq
    (DescentStaticWordColumn.program w (floor+gateWords D r b d M)
      (indexData D (chunks J M) bits) (indexWords D bits))

def image (floor bits D r b d grain J M : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image (floor+gateWords D r b d M) (indexData D (chunks J M) bits)
    (DescentPackedZip.Book.image (gate D r b d grain) (width b r d) M floor m) (indexWords D bits)

def charge (D r b d M bits : ℕ) := 8+10*(gateWords D r b d M+indexWords D bits)

theorem names (w floor bits D r b d grain J M : ℕ) :
    DescentStaticWordColumn.names (install w floor bits D r b d grain J M) =
      15*(gateWords D r b d M+indexWords D bits+2) := by
  rw [install,DescentStaticWordColumn.names_seq,DescentPackedZip.Book.names,DescentStaticWordColumn.names_mount]
  unfold gateWords
  omega

private theorem within {i n pitch a : ℕ} (hi : i<n) (ha : a<pitch) : i*pitch+a<n*pitch := by
  have last := Nat.mul_le_mul_right pitch hi
  rw [Nat.succ_mul] at last
  omega

private theorem bank_end {j bits D base : ℕ} (hj : j<D+4) :
    (indexBank base bits j).base+(indexBank base bits j).size ≤ base+indexWords D bits := by
  change base+j*2^bits+2^bits ≤ base+(D+4)*2^bits
  have le := Nat.mul_le_mul_right (2^bits) hj
  rw [Nat.succ_mul] at le
  omega

private theorem belowFits (B : Bank) {w cut : ℕ} (end_ : B.base+B.size≤cut) (fit : cut<2^w) :
    B.Fits w cut := ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt fit),end_⟩

private theorem later {B : Bank} {w a z : ℕ} (fit : B.Fits w a) (hle : a≤z) :
    B.Fits w z := ⟨fit.1,fit.2.1,fit.2.2.trans hle⟩

private theorem forwardFits (tokens : DescentPackedFlowRAM.Slot r c→Bank)
    (tables : Fin r→DescentPackedZip.Tables) {out : ℕ}
    (words : ∀i,(tokens i).Fits w out) (gates : ∀x,WordRoom (tables x) (b*r) d M w out) :
    (DescentPackedFlowRAM.sumRow tokens tables).Fits w out := by
  have fold (xs : List (DescentPackedFlowRAM.Slot r c)) (e : Expr) (he : e.Fits w out) :
      (xs.foldl (DescentPackedFlowRAM.entry tokens tables) e).Fits w out := by
    induction xs generalizing e with
    | nil=>exact he
    | cons q qs ih=>exact ih _ ((gates q.1).safe _ _ he ⟨words q,trivial⟩)
  exact fold _ _ trivial

private theorem reverseFits (C : DescentPackedFlowReturn.Index) (P : Ports D) (bank : Fin D→Bank)
    (T : DescentPackedZip.Tables) (i : Fin D) (out : ℕ)
    (links : ∀j,Accessible P (bank j) H J M w out)
    (start : C.starts.Fits w out) (hosts : C.hosts.Fits w out)
    (zip : WordRoom T (b*r) (b*r) M w out) :
    (DescentPackedFlowPair.expr C P bank T H i).Fits w out := by
  have fold (xs : List (Fin D)) (e : Expr) (he : e.Fits w out) :
      (xs.foldl (DescentPackedFlowPair.gather C P bank T H i) e).Fits w out := by
    induction xs generalizing e with
    | nil=>exact he
    | cons j js ih=>
      apply ih
      apply zip.safe _ _ he
      have a:=links j
      simp [DescentPackedFlowReturn.gated,DescentPackedFlowReturn.reverseID,neighborID,peerExpr,
        Expr.Fits,a.ids,a.roster,a.source,a.offsets,a.chunks,start,hosts]
  exact fold _ _ ⟨(links i).source,trivial⟩

section Placed

variable (tokens : DescentPackedFlowRAM.Slot r c→Bank) (roster : Bank)
  (floor bits D b d grain M : ℕ)
local notation "A" => layout tokens roster floor bits D b d grain M
local notation "indexAt" => floor+gateWords D r b d M
local notation "span" => 2^bits
local notation "wall" => (A).middle+D*(A).pitch

theorem stop : wall = floor+gateWords D r b d M+(3*D+4)*2^bits := by
  dsimp [Layout.middle,Layout.pitch,layout,indexWords]
  ring

theorem room {H J w : ℕ}
    (count : H*chunks J M≤ span) (hosts : H≤ span)
    (old : ∀t,(tokens t).base+(tokens t).size≤floor ∧ H*chunks J M≤(tokens t).size)
    (peer : roster.base+roster.size≤floor) (near : H*D≤roster.size)
    (endRoom : wall<2^w) : Room A H J M d b w := by
  let oldEnd:=(A).first
  let mid:=(A).middle
  have le₁ : floor≤oldEnd := by change floor≤floor+_+_; omega
  have le₂ : oldEnd≤ mid := Nat.le_add_right ..
  have le₃ : mid≤wall := Nat.le_add_right ..
  have firstFits:=le₂.trans_lt (le₃.trans_lt endRoom)
  have midFits:=le₃.trans_lt endRoom
  have room_bank (j : ℕ) (hj:j<D+4) : (indexBank indexAt bits j).Fits w oldEnd :=
    belowFits _ (bank_end hj) firstFits
  have tokenFits (s : DescentPackedFlowRAM.Slot r c) : (tokens s).Fits w oldEnd :=
    belowFits _ ((old s).1.trans le₁) firstFits
  have peerFits := belowFits roster (peer.trans le₁) firstFits
  have zip (j : Fin (D*r+1)) :
      let g:=gate D r b d grain j
      WordRoom (DescentPackedZip.Book.tables (gate D r b d grain) (width b r d) M floor j) g.left g.right M w oldEnd := by
    let g:=gate D r b d grain j
    obtain ⟨left,right⟩ := DescentPackedZip.Book.geometry (gate D r b d grain) (width b r d) M floor j
      (show indexAt≤oldEnd from Nat.le_add_right ..) firstFits (widths ..)
    exact ⟨left,right,rfl,rfl⟩
  have ins (j : Fin D) (x : Fin r) : WordRoom ((A).inserts j x) (b*r) d M w oldEnd := by
    have h:=zip (insId j x)
    change WordRoom _ _ _ _ _ _ at h
    simpa only [layout,ins_gate] using h
  have ad : WordRoom (A).add (b*r) (b*r) M w oldEnd := by
    have h:=zip (addId D r)
    change WordRoom _ _ _ _ _ _ at h
    simpa only [layout,add_gate] using h
  have addLater : WordRoom (A).add (b*r) (b*r) M w mid :=
    ⟨later ad.shift le₂,later ad.apply le₂,ad.shiftBits,ad.applyBits⟩
  have access (j : Fin D) : Accessible (A).peers ((A).issued j) H J M w mid := by
    have jlt:=j.isLt
    have lim : ((A).issued j).base+((A).issued j).size≤ mid := by
      change oldEnd+j.val*span+span≤oldEnd+D*span
      have reach:=Nat.mul_le_mul_right span j.isLt
      rw [Nat.succ_mul] at reach
      omega
    exact ⟨fun i=>later (room_bank i.val (by have:=i.isLt;omega)) le₂,fun _=>count,
      later peerFits le₂,near,later (room_bank D (by omega)) le₂,hosts,
      later (room_bank (D+1) (by omega)) le₂,count,belowFits _ lim midFits,count⟩
  refine ⟨count,endRoom,fun t=>⟨tokenFits t,(old t).2⟩,ins,?_,?_,access,addLater,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj
    simp only [Layout.front,dite_eq_left hj]
    exact PrefixAgreement.inputEnd_of_fits _ (forwardFits tokens _ tokenFits (ins ⟨j,hj⟩))
  · intro j hj
    simp only [Layout.both,dite_eq_left hj]
    exact PrefixAgreement.inputEnd_of_fits _ (reverseFits (A).header (A).peers (A).issued (A).add
      ⟨j,hj⟩ mid access (later (room_bank (D+2) (by omega)) le₂)
      (later (room_bank (D+3) (by omega)) le₂) addLater)
  · intro i
    exact (Nat.add_le_add_left count _).trans (room_bank i.val (by have:=i.isLt;omega)).2.2
  · exact (Nat.add_le_add_left near _).trans peerFits.2.2
  · exact (Nat.add_le_add_left hosts _).trans (room_bank D (by omega)).2.2
  · exact (Nat.add_le_add_left count _).trans (room_bank (D+1) (by omega)).2.2
  · exact (Nat.add_le_add_left hosts _).trans (room_bank (D+2) (by omega)).2.2
  · exact (Nat.add_le_add_left count _).trans (room_bank (D+3) (by omega)).2.2
  · simpa only [Bank.size,ad.shiftBits] using ad.shift.2.2
  · simpa only [Bank.size,ad.applyBits] using ad.apply.2.2

private theorem field_read {J w : ℕ} (mem : Memory w) {i a : ℕ} (hi : i<D+4) (ha : a<span) :
    image floor bits D r b d grain J M mem ((indexBank indexAt bits i).base+a)=
      (((if i<D then (a/chunks J M)*D+i else if i=D then chunks J M*a
      else if i=D+1 then a%chunks J M else if i=D+2 then a*D else a/chunks J M) : ℕ) : Word w) := by
  have inside : i*span+a < indexWords D bits := within hi ha
  have eqv : (indexBank indexAt bits i).base+a=indexAt+(i*span+a) := Nat.add_assoc ..
  rw [eqv, image,DescentStaticWordColumn.read _ _ _ _ inside]
  simp only [indexData,Nat.mul_comm i (2^bits),Nat.mul_add_div (Nat.two_pow_pos bits),
    Nat.div_eq_of_lt ha,Nat.add_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt ha]

theorem execute {J w H : ℕ} (mem : Memory w) (next : Fin H→Fin D→Option (Fin H))
    (count : H*chunks J M≤ span) (hosts : H≤ span)
    (old : ∀t,(tokens t).base+(tokens t).size≤floor ∧ H*chunks J M≤(tokens t).size)
    (peer : roster.base+roster.size≤floor) (near : H*D≤roster.size)
    (oldRanks : ∀v : Fin H,∀j : Fin D,mem (roster.base+(v.val*D+j.val))=(target (next v j):Word w))
    (endRoom : wall<2^w) :
    let dst:=image floor bits D r b d grain J M mem
    (install w floor bits D r b d grain J M).Exec mem dst (charge D r b d M bits) ∧
    Room A H J M d b w ∧ (∀j x,DescentPackedZip.Static ((A).inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=d) grain j.val x) M dst) ∧
    DescentPackedZip.Static (A).add (DescentPackedFlowPair.add (b:=b) (r:=r)) M dst ∧
    Mounted (A).peers next dst J M ∧ DescentPackedFlowReturn.Header (A).header (A).middle dst D H J M ∧
    (∀a,a<floor ∨ (A).first≤a→dst a=mem a) ∧ CheapCode (install w floor bits D r b d grain J M) := by
  intro dst
  have le₂ : (A).first≤(A).middle := Nat.le_add_right ..
  have top : (A).first<2^w := le₂.trans_lt ((Nat.le_add_right ..).trans_lt endRoom)
  have gatesFit : indexAt<2^w := (Nat.le_add_right ..).trans_lt top
  let gates:=gate D r b d grain
  let mid:=DescentPackedZip.Book.image gates (width b r d) M floor mem
  obtain ⟨tableRun,static,frame,cheap⟩ := DescentPackedZip.Book.mount gates (width b r d) M floor mem
    (widths D r b d grain) gatesFit
  have native : (DescentStaticWordColumn.program w indexAt (indexData D (chunks J M) bits) (indexWords D bits)).Exec
      mid dst (4+10*indexWords D bits) :=
    @DescentStaticWordColumn.mount w indexAt (indexWords D bits) (indexData D (chunks J M) bits) mid top
  have held (a : ℕ) (h:a < indexAt ∨ (A).first≤a) : dst a=mid a :=
    DescentStaticWordColumn.frame _ _ _ _ a h
  have keep (a : ℕ) (ha:a<floor ∨ (A).first≤a) : dst a=mem a := by
    have low : floor ≤ indexAt:=Nat.le_add_right ..
    have high : indexAt≤(A).first := Nat.le_add_right ..
    rcases ha with lt|ge
    · exact (held a (.inl (lt.trans_le low))).trans (frame a (.inl lt))
    · exact (held a (.inr ge)).trans (frame a (.inr (high.trans ge)))
  have retained := DescentPackedZip.Book.retained gates (width b r d) M floor dst mid (widths D r b d grain) static
    (fun a _ lt=>held a (.inl lt))
  have allocated:=room tokens roster floor bits D b d grain M count hosts old peer near endRoom
  have words (j a) (hj:j<D+4) (ha:a<span) := field_read (J:=J) (r:=r) floor bits D b d grain M mem hj ha
  have qr (v : Fin H) (j : Fin (chunks J M)) :
      (row H J M (v,j)).val / chunks J M=v.val ∧ (row H J M (v,j)).val % chunks J M=j.val := by
    have pos := Nat.zero_lt_of_lt j.isLt
    change (j.val+chunks J M*v.val)/chunks J M=v.val ∧ (j.val+chunks J M*v.val)%chunks J M=j.val
    simp only [Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt j.isLt,Nat.zero_add,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt,and_self]
  refine ⟨?_,allocated,?_,?_,?_,?_,keep,?_⟩
  · change ((DescentPackedZip.Book.install gates _ M w floor).seq _).Exec _ _ _
    rw [charge,show 8+10*(gateWords D r b d M+indexWords D bits)=
      (4+10*gateWords D r b d M)+(4+10*indexWords D bits) by omega]
    exact Procedure.Exec.then @tableRun @native
  · intro j x
    exact (congrArg (fun g : DescentPackedZip.Book.Gate =>
      DescentPackedZip.Static ((A).inserts j x) g.eval M dst)
      (ins_gate j x b d grain)).mp (retained (insId j x))
  · exact (congrArg (fun g : DescentPackedZip.Book.Gate =>
      DescentPackedZip.Static (A).add g.eval M dst)
      (add_gate D r b d grain)).mp (retained (addId D r))
  · constructor
    · rintro ⟨v,j⟩ i
      simpa only [layout,ite_eq_left i.isLt,(qr v j).1] using
        words i.val (row H J M (v,j)).val (by have:=i.isLt;omega) ((row H J M (v,j)).isLt.trans_le count)
    · intro v i
      have valid : v.val*D+i.val<H*D := within v.isLt i.isLt
      exact (keep _ (.inl ((Nat.add_lt_add_left (valid.trans_le near) _).trans_le peer))).trans (oldRanks v i)
    · intro v
      simpa [layout] using words D v.val (by omega) (v.isLt.trans_le hosts)
    · rintro ⟨v,j⟩
      simpa [layout,(qr v j).2] using words (D+1) (row H J M (v,j)).val (by omega) ((row H J M (v,j)).isLt.trans_le count)
  · have q (j) (hj:j<D+4) : (indexBank indexAt bits j).Fits w (A).middle :=
      later (belowFits _ (bank_end hj) top) le₂
    refine ⟨q _ (by omega),q _ (by omega),hosts,count,?_,?_⟩
    · intro v
      simpa [layout] using words (D+2) v.val (by omega) (v.isLt.trans_le hosts)
    · rintro ⟨v,j⟩
      simpa [layout,(qr v j).1] using words (D+3) (row H J M (v,j)).val (by omega) ((row H J M (v,j)).isLt.trans_le count)
  · exact @cheap_seq w (DescentPackedZip.Book.install gates (width b r d) M w floor)
      (DescentStaticWordColumn.program w indexAt (indexData D (chunks J M) bits) (indexWords D bits))
      @cheap (@DescentStaticWordColumn.cheap w indexAt (indexData D (chunks J M) bits) (indexWords D bits))

/-- The old signed chip at each port and each packed row is available to the
first flow scan after the book has issued its literals. -/
theorem token_reads {w J H : ℕ} (mem : Memory w)
    (tags : Fin H→Fin J→DescentPackedFlowRAM.Slot r c→Cell d)
    (old : ∀t,(tokens t).base+(tokens t).size≤floor ∧ H*chunks J M≤(tokens t).size)
    (stored : ∀t,Reads (tokens t) (fun v g=>tags v g t) M mem) :
    ∀t,Reads (tokens t) (fun v g=>tags v g t) M (image floor bits D r b d grain J M mem) := by
  intro t pair
  have below := (Nat.add_lt_add_left ((row H J M pair).isLt.trans_le (old t).2) (tokens t).base).trans_le
    (old t).1
  have before : floor ≤ indexAt := Nat.le_add_right ..
  have keep := DescentStaticWordColumn.frame indexAt (indexWords D bits)
    (indexData D (chunks J M) bits) (DescentPackedZip.Book.image (gate D r b d grain)
      (width b r d) M floor mem) _ (.inl (below.trans_le before))
  have saved := DescentStaticWordColumn.frame floor (gateWords D r b d M)
    (DescentPackedZip.Book.data (gate D r b d grain) (width b r d) M) mem _ (.inl below)
  exact keep.trans (saved.trans (stored t pair))

end Placed
end
end Hierarchy.DescentPackedFlowPublication.Book

end OAI

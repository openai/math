import OAI.Hierarchy.DescentResetReceivedEvidencePrice
import OAI.Hierarchy.DescentResetReceiverPitch
import OAI.Hierarchy.DescentDatedLocalScale
import OAI.Hierarchy.DescentCanonicalFrontSources
import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! # Packed reset stems at the attained input and output pitches -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSIMDLookup DescentDyadicSpan DescentResetStemPackedIssue ProtocolRAM
open ThreeFlat.Routing ThreeFlat.RAM
noncomputable section
set_option quotPrecheck false

def stemEnvelope (h P H G X A M : ℕ) :=
  P+H+P*chunks (G*X) A+H*chunks G M+P*chunks G M+(h+1)^3*2^(h/2)

private theorem product_chunks (G X M : ℕ) (hp : 0<M) (hx : 0<X) :
    chunks (G*X) (M*X)≤chunks G M:=by
  change (G*X) ⌈/⌉ (M*X)≤chunks G M
  apply (ceilDiv_le_iff_le_mul (Nat.mul_pos hp hx)).2
  calc G*X≤(M*chunks G M)*X:=Nat.mul_le_mul_right _ (CallPool.count_le_batches_mul G M hp)
       _=M*X*chunks G M:=by ring

def volumeFactor (N X : ℕ) :=N+N+N+(X+2)+X+N*X+1+1

theorem volume_paid (h N P H G X f A M : ℕ) (xp : 0<X) (mp : 0<M)
    (oldLane : A≤h) (lane : M≤h) (window : f*A≤h/2) (projection : (f*X)*M≤h/2) :
    DescentResetStemProject.volume N P G X f A M≤volumeFactor N X*stemEnvelope h P H G X A M:=by
  let E:=stemEnvelope h P H G X A M
  let dict:=2^(h/2)
  have one : 1≤E:=Nat.succ_le_of_lt (by dsimp [E,stemEnvelope];positivity)
  have table : (h+1)^3*dict≤E:=by dsimp [E,stemEnvelope,dict];omega
  have ref : dict≤E:=(Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans table
  have before : P*chunks (G*X) A≤E:=by dsimp [E,stemEnvelope];omega
  have after : P*chunks G M≤E:=by dsimp [E,stemEnvelope];omega
  have converted : (N*P)*chunks (G*X) (M*X)≤N*E:=by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left P (product_chunks G X M mp xp)).trans after)
  have input : (N*P)*chunks (G*X) A≤N*E:=by rw [Nat.mul_assoc];exact Nat.mul_le_mul_left _ before
  have pages : DescentVectorBookReshape.dictionaryWords X f M≤X*E:=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) projection).trans ref)
  have fieldRows : N*DescentVectorBookReshape.rows P 1 G X M≤N*X*E:=by
    unfold DescentVectorBookReshape.rows
    simpa only [Nat.mul_one,Nat.mul_assoc] using Nat.mul_le_mul_left (N*X) after
  have pieces : DescentSIMDLookup.Overlap.pieces (G*X) A (M*X)+1≤(X+2)*(h+1):=by
    have ol : chunks (M*X) A≤M*X+A:=(Nat.div_le_self ..).trans (Nat.sub_le ..)
    have hi:=Nat.mul_le_mul_right X lane
    have bound:=min_le_right (chunks (G*X) A) (chunks (M*X) A+1)
    unfold DescentSIMDLookup.Overlap.pieces
    nlinarith
  have overlap : (DescentSIMDLookup.Overlap.pieces (G*X) A (M*X)+1)*(A+1)*2^(f*A)≤(X+2)*E:=by
    calc _ ≤ ((X+2)*(h+1))*(h+1)*dict := Nat.mul_le_mul (Nat.mul_le_mul pieces (Nat.succ_le_succ oldLane))
          (Nat.pow_le_pow_right (by decide) window)
         _ ≤ (X+2)*((h+1)^3*dict):=by
           have power:=(Nat.pow_le_pow_right (by omega : 0<h+1) (by decide : 2≤3))
           exact (by simpa only [pow_two,Nat.mul_assoc] using Nat.mul_le_mul_left (X+2) (Nat.mul_le_mul_right dict power))
         _ ≤ (X+2)*E:=Nat.mul_le_mul_left _ table
  unfold DescentResetStemProject.volume DescentSIMDLookup.Overlap.rows
  change N+(N*P)*chunks (G*X) A+(N*P)*chunks (G*X) (M*X)+_+_+_+P*chunks G M+1≤volumeFactor N X*E
  calc _ ≤ N*E+N*E+N*E+(X+2)*E+X*E+(N*X)*E+1*E+1*E:=by
         simp only [Nat.one_mul]
         exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
           (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_mul_of_pos_right N one) input)
             converted) overlap) pages) fieldRows) after) one
       _ = _:=by unfold volumeFactor;ring

/-- All terms are linear in the physically scanned page sizes. The other quantities
are per-date local register counts and instruction counts. -/
private def stemLedger (D K X Q T U : ℕ) (unit rawH newH oldRows newRows prev volume key mux headers pointers : ℕ) :=
  let N:=Q*(D+2)
  let q:=X*Q
  let scalar:=DescentResetStemDescriptorRAM.workLimit (6*U+7)
  let project:=4096*volume+(4*unit+N*(4*unit+oldRows*(2*T+4)))+7*((15+N*(11+4*T))*unit)
  let print:=(4+10*56)*unit+(4*unit+(2*K)*(4*unit+newH*(2*scalar+4)))
  let printNames:=(15*(56+1)+(15+(2*K)*(11+4*scalar)))*unit
  let temps:=((4*unit+10*key)+(4*unit+q*(4*unit+prev*(2*(14+(D+2)*(7+11))+4))))+
    (4*unit+10*pointers)+(4*unit+10*headers+(4*unit+(2*K)*(4*unit+54*newRows)))+
    ((4*unit+10*mux)+(4*unit+q*(4*unit+newRows*(2*(1+K*(30+7+22))+4))))
  let code:=(15*(key+unit)+(15+q*(11+4*(14+(D+2)*(7+11))))*unit)+15*(pointers+unit)+
    (15*(headers+unit)+(15+(2*K)*(11+4*25))*unit)+
    (15*(mux+unit)+(15+q*(11+4*(1+K*(30+7+22))))*unit)
  260*(unit+rawH+newH)+7*(15*(rawH+unit)+2048*unit)+project+(print+temps)+7*(printNames+code)

def stemCoefficient (D K X Q shapes T U : ℕ) :=
  stemLedger D K X Q T U 1 shapes 1 1 1 1 (volumeFactor (Q*(D+2)) X) ((D+4)*2) ((K+1)*2) 7 9

section
-- Local operators combine certificates for sums and products of small functions.
local infixl:65 " +ₛ " => SmallAt.add
local infixl:70 " *ₛ " => SmallAt.mul

theorem stemCoefficient_small {ι : ℕ→Type*} {J : ℕ→ℕ} {D K X Q shapes T U : ∀h,ι h→ℕ}
    (d : SmallAt J D) (k : SmallAt J K) (x : SmallAt J X) (q : SmallAt J Q) (s : SmallAt J shapes)
    (t : SmallAt J T) (u : SmallAt J U) :
    SmallAt J (fun h i=>stemCoefficient (D h i) (K h i) (X h i) (Q h i) (shapes h i) (T h i) (U h i)):=by
  let c (n : ℕ) := SmallAt.const (ι:=ι) J n
  have number := q *ₛ (d +ₛ c 2)
  have queries := x *ₛ q
  have budget := c 6 *ₛ u +ₛ c 7
  have operand := c 1 +ₛ c 4 *ₛ (c 2 *ₛ budget +ₛ c 3 +ₛ c 4 *ₛ (c 2 *ₛ budget +ₛ c 2) +ₛ c 1)
  have scalar := budget +ₛ c 3 +ₛ (c 1 +ₛ c 7 *ₛ ((budget +ₛ c 1).max (operand) +ₛ c 6))
  have volume := number +ₛ number +ₛ number +ₛ (x +ₛ c 2) +ₛ x +ₛ number *ₛ x +ₛ c 1 +ₛ c 1
  have key := (d +ₛ c 4) *ₛ c 2
  have mux := (k +ₛ c 1) *ₛ c 2
  have project :=
    c 4096 *ₛ volume +ₛ (c 4 +ₛ number *ₛ (c 4 +ₛ c 1 *ₛ (c 2 *ₛ t +ₛ c 4))) +ₛ c 7 *ₛ ((c 15
      +ₛ number *ₛ (c 11 +ₛ c 4 *ₛ t)) *ₛ c 1)
  have printTime := c 564 +ₛ (c 4 +ₛ c 2 *ₛ k *ₛ (c 4 +ₛ c 1 *ₛ (c 2 *ₛ scalar +ₛ c 4)))
  have printNames := (c 855 +ₛ (c 15 +ₛ c 2 *ₛ k *ₛ (c 11 +ₛ c 4 *ₛ scalar))) *ₛ c 1
  have temps :=
    c 4 +ₛ c 10 *ₛ key +ₛ (c 4 +ₛ queries *ₛ (c 4 +ₛ c 1 *ₛ (c 2 *ₛ (c 14 +ₛ (d +ₛ c 2) *ₛ c
      18) +ₛ c 4))) +ₛ c 94 +ₛ (c 74 +ₛ (c 4 +ₛ c 2 *ₛ k *ₛ c 58)) +ₛ (c 4 +ₛ c 10 *ₛ mux +ₛ
      (c 4 +ₛ queries *ₛ (c 4 +ₛ c 1 *ₛ (c 2 *ₛ (c 1 +ₛ k *ₛ c 59) +ₛ c 4))))
  have code :=
    c 15 *ₛ (key +ₛ c 1) +ₛ (c 15 +ₛ queries *ₛ (c 11 +ₛ c 4 *ₛ (c 14 +ₛ (d +ₛ c 2) *ₛ c 18)))
      *ₛ c 1 +ₛ c 150 +ₛ (c 120 +ₛ (c 15 +ₛ c 2 *ₛ k *ₛ c 111) *ₛ c 1) +ₛ (c 15 *ₛ (mux +ₛ c
      1) +ₛ (c 15 +ₛ queries *ₛ (c 11 +ₛ c 4 *ₛ (c 1 +ₛ k *ₛ c 59))) *ₛ c 1)
  exact
    c 260 *ₛ (c 1 +ₛ s +ₛ c 1) +ₛ c 7 *ₛ (c 15 *ₛ (s +ₛ c 1) +ₛ c 2048) +ₛ project +ₛ
      (printTime +ₛ temps) +ₛ c 7 *ₛ (printNames +ₛ code)

end

theorem stemBill_funded (v : CandidateFront) (h T U : ℕ)
    (oldLane : v.oldLanes≤h) (lane : v.peer.lanes≤h) (mp : 0<v.peer.lanes) (xp : 0<v.blocks)
    (oldKey : v.stemField*v.oldLanes≤h/2)
    (project : v.stemField*v.blocks*v.peer.lanes≤h/2)
    (keyRoom : DescentResetStemKey.unit v.peer.oldDegree v.stemField*v.peer.lanes≤h/2)
    (muxRoom : DescentResetStemMux.unit (v.stemField+2) (v.metaBits*7)*v.peer.lanes≤h/2)
    (header : v.metaBits*7≤h/2) :
    v.stemBill T U≤ stemCoefficient v.peer.oldDegree v.oldTicketCount v.blocks v.signedQueries v.peer.shapes T U*
      stemEnvelope h v.peer.oldHosts v.newHosts v.peer.groups v.blocks v.oldLanes v.peer.lanes:=by
  let P:=v.peer.oldHosts
  let H:=v.newHosts
  let D:=v.peer.oldDegree
  let K:=v.oldTicketCount
  let X:=v.blocks
  let G:=v.peer.groups
  let A:=v.oldLanes
  let M:=v.peer.lanes
  let f:=v.stemField
  let b:=v.metaBits
  let Q:=v.signedQueries
  let n:=H*chunks G M
  let E:=stemEnvelope h P H G X A M
  let fun_:=stemLedger D K X Q T U
  have one : 1≤E:=Nat.succ_le_of_lt (by dsimp [E,stemEnvelope];positivity)
  have oh : P≤E:=by dsimp [E,stemEnvelope];omega
  have nh : H≤E:=by dsimp [E,stemEnvelope];omega
  have old : P*chunks (G*X) A≤E:=by dsimp [E,stemEnvelope];omega
  have cur : n≤E:=by dsimp [E,stemEnvelope,n];omega
  have prev : P*chunks G M≤E:=by dsimp [E,stemEnvelope];omega
  have dictionary : 2^(h/2)≤E:=by
    apply (Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans
    dsimp [E,stemEnvelope];omega
  have raw : v.peer.hosts≤v.peer.shapes*E:=by
    change P*v.peer.shapes≤_
    rw [Nat.mul_comm];exact Nat.mul_le_mul_left _ oh
  have kB : DescentResetStemKey.words D f M≤((D+4)*2)*E:=by
    unfold DescentResetStemKey.words
    rw [←Nat.mul_assoc]
    simpa [Nat.add_assoc] using Nat.mul_le_mul_left ((D+4)*2) ((Nat.pow_le_pow_right (by decide) keyRoom).trans dictionary)
  have mB : DescentResetStemMux.words K (f+2) (b*7) M≤((K+1)*2)*E:=by
    unfold DescentResetStemMux.words
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) muxRoom).trans dictionary)
  have head : DescentResetStemHeaders.romSize (b*7) n≤7*E:=by
    have mem : 2^(b*7) ≤ E := (Nat.pow_le_pow_right (by decide) header).trans dictionary
    unfold DescentResetStemHeaders.romSize
    have spanBound:=span_le n
    omega
  have pointer : span P+2*span n≤9*E:=by
    have first_:=span_le P
    have second_:=span_le n
    omega
  have vol:=volume_paid h (Q*(D+2)) P H G X f A M xp mp oldLane lane oldKey project
  let used:=fun_ 1 v.peer.hosts H (P*chunks (G*X) A) n (P*chunks G M)
    (DescentResetStemProject.volume (Q*(D+2)) P G X f A M) (DescentResetStemKey.words D f M)
    (DescentResetStemMux.words K (f+2) (b*7) M) (DescentResetStemHeaders.romSize (b*7) n) (span P+2*span n)
  have measure : v.stemBill T U=used:=by
    dsimp only [stemBill,Mixed.Projected.bill,Mixed.codeTariff,Mixed.keyNames,DescentResetStemKeyReindex.size,
      stemLedger,used,fun_,Nat.mul_one,D,K,X,Q,P,H,G,A,M,f,b,n]
    ring
  rw [measure]
  calc used ≤ fun_ E (v.peer.shapes*E) E E E E (volumeFactor (Q*(D+2)) X*E) (((D+4)*2)*E)
        (((K+1)*2)*E) (7*E) (9*E):=by
          dsimp only [used,fun_,stemLedger]
          gcongr
       _ = stemCoefficient D K X Q v.peer.shapes T U * E:=by
         dsimp only [stemCoefficient,stemLedger,fun_]
         ring

theorem original_port_work (v : CandidateFront) (base : ℕ) (old : v.Originals base) (flags count inverse : Bank) :
    (v.fromOriginals base old flags count inverse).stems.ports.All (fun e=>e.work≤22+8*v.peer.shapes):=
  DescentResetStemMaskedPorts.work _ _ _ _

theorem original_operand_work {n d : ℕ} (S : DescentCompiler.AtomSchedule) (board : NonlinearExpanders.Graph n d)
    (k tail age degree f g receiverBatch nextBatch rootField metaBits C packet : ℕ) (calendar : List ℕ)
    (floor : ℕ) (early : EarlierBanks degree k ((calendar.take age).prod*256) n) (flags count inverse : Bank)
    (j : Fin (DescentResetStemPackedIssue.count (2^k) ((calendar.take age).prod*256))) (i : Fin (degree+2)) :
    let a:=setupFront S board k tail age degree f g receiverBatch nextBatch rootField metaBits C packet calendar
    let e:=calendarOriginals S board k tail age degree f g receiverBatch nextBatch rootField metaBits C packet calendar floor early
    (((a.fromOriginals floor e flags count inverse).stems.operands j i).work≤45):=by
  apply DescentResetStemKey.readers_work

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "v" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "F₀" => (v).front
local notation "P" => (F₀).peer

theorem bought_stem_bill_at (T U : ℕ) (keys : ∀t,t∈(v).rootUnits ∨ t∈(v).receiverUnits→t*(v).receiver.lanes≤h/2) :
    (F₀).stemBill T U ≤
      CandidateFront.stemCoefficient (P).oldDegree (F₀).oldTicketCount (F₀).blocks (F₀).signedQueries (P).shapes
        T U*
      CandidateFront.stemEnvelope h (P).oldHosts (F₀).newHosts (P).groups (F₀).blocks (F₀).oldLanes (P).lanes:=by
  let M:=(v).receiver.lanes
  have pos : 0<M:=Nat.two_pow_pos e
  have small : ((F₀).stemField+2)*M≤h/2:=keys _ (Or.inl (by simp [rootUnits]))
  have lanes:M≤h:=((Nat.le_mul_of_pos_left M (by omega : 0<(F₀).stemField+2)).trans small).trans (Nat.div_le_self ..)
  have old : (F₀).stemField*M≤h/2:=(Nat.mul_le_mul_right _ (Nat.le_add_right _ 2)).trans small
  have proj : ((F₀).projectionBits*(v).sheets.blocks)*M≤h/2:=keys _ (Or.inr (by simp [receiverUnits]))
  have key:=(keys (DescentResetStemKey.unit (P).oldDegree (F₀).stemField) (Or.inr (by simp [receiverUnits])))
  have mux:=(keys (DescentResetStemMux.unit ((F₀).stemField+2) ((v).sheets.metaBits*7)) (Or.inr (by simp [receiverUnits])))
  have payload : ((v).sheets.metaBits*7+(v).sheets.metaBits)*M≤h/2:=keys _ (Or.inr (by simp [receiverUnits]))
  have header : (v).sheets.metaBits*7≤h/2:=(Nat.le_add_right ..).trans ((Nat.le_mul_of_pos_right _ pos).trans payload)
  exact CandidateFront.stemBill_funded (F₀) h T U lanes lanes pos (Nat.two_pow_pos k)
    old proj key mux header

theorem bought_stem_bill (keys : ∀t,t∈(v).rootUnits ∨ t∈(v).receiverUnits→t*(v).receiver.lanes≤h/2) :
    (F₀).stemBill 45 (22+8*(P).shapes) ≤
      CandidateFront.stemCoefficient (P).oldDegree (F₀).oldTicketCount (F₀).blocks (F₀).signedQueries (P).shapes
        45 (22+8*(P).shapes)*
      CandidateFront.stemEnvelope h (P).oldHosts (F₀).newHosts (P).groups (F₀).blocks (F₀).oldLanes (P).lanes:=
  bought_stem_bill_at G S board k tail age p f g drift degree h e prev nextM C packet prior base 45 (22+8*(P).shapes) keys

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

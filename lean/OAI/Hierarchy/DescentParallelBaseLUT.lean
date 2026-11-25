import OAI.Hierarchy.DescentSignedTableDimensions
import OAI.Hierarchy.DescentParallelBase
import OAI.Hierarchy.DescentSharedCableSender
import OAI.Hierarchy.DescentPackedMaskedData
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Native bounded weighted ranking of the gathered two-sided parent records -/
namespace Hierarchy.DescentParallelBase
open DescentSIMDLookup DescentSharedCableNames
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {D K L m : ℕ}

/-- The source bit orders the two possible directions of this very pair by
their true source sites. Inside either direction the source-relative parent
ticket supplies the actual chronology. No global source ID occurs on a pin. -/
def side {U : Type} (site : U↪ℕ) (s t : U) := decide (site t<site s)

private theorem lex (a b i j n : ℕ) (si : i<n) (sj : j<n) : a*n+i<b*n+j ↔ a<b ∨ a=b ∧ i<j :=by
  have gap {a b i : ℕ} (l:a<b) (lo:i<n) : a*n+i<b*n:=by
    have:=Nat.mul_le_mul_right n (Nat.succ_le_of_lt l);rw [Nat.succ_mul] at this;omega
  rcases lt_trichotomy a b with l|e|g
  · have:=gap l si;omega
  · subst b;omega
  · have:=gap g sj;omega

theorem orient {U : Type} (site : U↪ℕ) {s t u v : U} (parallel : (s=u ∧ t=v) ∨ (s=v ∧ t=u)) (a b : Fin K) :
    (side site s t).toNat*K+a.val<(side site u v).toNat*K+b.val ↔ site s<site u ∨ s=u ∧ a<b :=by
  rw [lex _ _ _ _ _ a.isLt b.isLt]
  obtain ⟨rfl,rfl⟩|⟨rfl,rfl⟩:=parallel
  · simp
  · rcases lt_trichotomy (site s) (site t) with lower | equal | higher
    · have distinct : s ≠ t := fun eq => (ne_of_lt lower) (congrArg site eq)
      simp [side, lower, not_lt_of_ge lower.le, distinct]
    · have same : s = t := site.injective equal
      subst t
      simp
    · have distinct : s ≠ t := fun eq => (ne_of_gt higher) (congrArg site eq)
      simp [side, higher, not_lt_of_ge higher.le, distinct]

namespace PackedBase
local notation "bp" => Packed.bits D
local notation "bt" => Packed.bits K
local notation "bw" => Packed.bits L


def word (o : Option (Entry D K L)) : Cell (width D K L) :=
  Exchange.Sender.pair _ _ (Packed.token (o.map Entry.peer),Exchange.Sender.pair _ _ (finTwoEquiv.symm (o.elim false Entry.upper),
    Exchange.Sender.pair _ _ (Packed.token (o.map Entry.ticket),⟨(o.elim 0 (fun e=>e.weight.val)),by
      cases o with | none=>exact Nat.two_pow_pos _ | some x=>exact x.weight.isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩)))

def decode (D K L : ℕ) (x : Cell (width D K L)) : Option (Entry D K L):=do
  let a:=(Exchange.Sender.pair (Packed.bits D) (1+(Packed.bits K+Packed.bits L))).symm x
  let b:=(Exchange.Sender.pair 1 (Packed.bits K+Packed.bits L)).symm a.2
  let c:=(Exchange.Sender.pair (Packed.bits K) (Packed.bits L)).symm b.2
  let peer←Packed.readToken D a.1
  let ticket←Packed.readToken K c.1
  if lim : c.2.val<L+1 then return ⟨peer,finTwoEquiv b.1,ticket,⟨c.2.val,lim⟩⟩ else none

@[simp] theorem back (x : Option (Entry D K L)) : decode D K L (word x)=x :=by
  cases x with
  | none=>simp [decode,word]
  | some x=>obtain ⟨peer,flip,key,wt⟩:=x;simp [decode,word,wt.isLt]

def input (x : Fin m→Option (Entry D K L)) : Cell (width D K L*m):=encode _ _ (word ∘ x)

def answer (x : Fin m→Option (Entry D K L)) : Cell (bw*m):=
  encode _ _ (fun i=>(x i).elim 0 (fun e=>(base x e:Cell bw)))

def table (D K L m : ℕ) (key : Cell (width D K L*m)) : Cell (Packed.bits L*m):=
  answer (decode D K L ∘ (encode (width D K L) m).symm key)

theorem table_at (x : Fin m→Option (Entry D K L)) : table D K L m (input x)=answer x:=by
  have rows : decode D K L ∘ (word ∘ x)=x:=funext fun i=>back _
  simp only [table,input,Equiv.symm_apply_apply,rows]

theorem native {H G M w : ℕ} (A : Banks) (out : Bank) (room : Fits A (width D K L*m) (bw*m) M H G w out.base)
    (rows : Fin H→Fin G→Fin m→Option (Entry D K L)) (mem : Memory w)
    (pins : PinFrame (M:=M) A (table D K L m) (fun h g=>input (rows h g)) mem) :
    let result:=image out.base (H*chunks G M) (DescentSIMDLookup.lookup A) mem
    (DescentSIMDLookup.program A out.base H G M w).Exec mem result (4+H*chunks G M*44) ∧
    DescentPackedColony.Reads out (fun h g=>answer (rows h g)) M result ∧ CheapCode (DescentSIMDLookup.program A out.base H G M w) :=by
  intro result
  have fit : (DescentSIMDLookup.lookup A).Fits w out.base:=by simp [DescentSIMDLookup.lookup,Expr.Fits,room.source,room.mask,room.dictionary]
  refine ⟨scan_exec _ _ _ _ fit room.output,fun p=>?_,by apply scan_cheap⟩
  have r:=(ProtocolRAMGeneratedWrite.read_image out.base (H * chunks G M) (DescentSIMDLookup.lookup A) mem (row H G M p)).trans (lookup_read A out.base room (table D K L m) _ mem pins p)
  simpa only [masked_eq_data,table_at] using r

/-- Exact numeric base even when a parent touches the upper-order receiver
and the lower-order source issued the matching donor ticket. -/
theorem physical {E U : Type} [Fintype E] [DecidableEq U] {n : ℕ} {B : Ends U n} (C : Blocks B E) (h : U)
    (address : Local C h↪Fin m) (row : Local C h→Entry D K L)
    (peer : ∀e f,(row e).peer=(row f).peer ↔ other C h e=other C h f)
    (order : ∀e f,other C h e=other C h f→(priority (row e)<priority (row f) ↔ C.first e.val<C.first f.val))
    (count : ∀e,(row e).weight.val=C.count e.val) (e : Local C h) (occupied : ∀u,(B.incident u).card≤L) :
    digit bw (address e).val (answer (place address row)).val=B.serial (C.src e.val) (C.dst e.val) (C.order ⟨e.val,⟨0,e.property.1⟩⟩) :=by
  unfold answer;rw [digit_encode,place_at];change ((base (place address row) (row e):Cell bw)).val=_
  rw [authentic C h address row peer order count e,Fin.val_cast_of_lt]
  have fits : L ≤ 2 ^ Packed.bits L :=
    (Nat.le_succ L).trans (Nat.le_pow_clog (by decide : 1 < 2) (L + 1))
  apply (B.serial_lt occupied _ _ _ ?_).trans_le fits
  simp [Ends.parallel,C.atSource,C.atTarget]

end PackedBase
end
end Hierarchy.DescentParallelBase

end OAI

import OAI.Hierarchy.DescentOrdinaryArgumentsAfter
import OAI.Hierarchy.DescentOrdinaryFirstAliasRead
import OAI.Hierarchy.DescentPackedSourceAccess

namespace OAI
/-! Read the four successor pointer fields at the address written by the ordinary date. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPackedOperand DescentOrdinaryFinal DescentOperandStateBanks DescentDatedPriorOperand
open DescentKernelHistory DescentLocalPrivateNames DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P Tag Port : Type} [Field F] (v : PhysicalOrdinary F P) {w : ℕ}
local notation "B" => v.finalChart
local notation "L" => v.resolver
variable («meta» : v.MetaWords) (old : Books (L))
  (jobs : Fin (L).jobs→DescentDatedPriorOperand.Source (L))
  (x : Fin (L).blocks) (h : Fin (L).hosts) (g : Fin (L).groups)
local notation "input_" p:arg => (B).dataAt (v.numericInputs «meta» old jobs) p x h g

def issuedFragment (i : Fin (B).keys) :=
  (jobs ((L).index (x,(B).slots.symm i))).compiled h g

theorem issued_stamp (p : Fin (B).outputs) (i : Fin (B).keys) :
    (B).stamp (input_ p) i=(word (v.issuedFragment jobs x h g i)).val := by
  let item:=word (v.issuedFragment jobs x h g i)
  have bound : outputWidth (L).size≤(B).scalarWidth := (Nat.le_max_right ..).trans
    ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  simp +instances only [Chart.stamp,Chart.dataAt,numericInputs,Chart.kind,Equiv.symm_apply_apply,Sum.elim,Fin.val_natCast]
  change (item.val%2^(outputWidth (L).size))%2^(B).scalarWidth=item.val
  rw [Nat.mod_eq_of_lt item.isLt,Nat.mod_eq_of_lt (item.isLt.trans_le
    (Nat.pow_le_pow_right (by decide:0<2) bound))]

theorem issued_arity (p : Fin (B).outputs) (u : Fin (L).nodes) :
    (B).arity (input_ p) u=digit (B).arityBits u.val («meta» 1 x h g).val := by
  let item:=«meta» 1 x h g
  have bound:(B).arityBits*(L).nodes≤(B).scalarWidth:=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have read:((input_ p) ((B).columns (.inl 1))).val=item.val:=by
    simp +instances only [Chart.dataAt,numericInputs,Chart.kind,Equiv.symm_apply_apply,Sum.elim,Fin.val_natCast]
    change (item.val%2^(v.metadata.chart.bits*(L).nodes))%2^(B).scalarWidth=item.val
    rw [Nat.mod_eq_of_lt item.isLt,Nat.mod_eq_of_lt (item.isLt.trans_le
      (Nat.pow_le_pow_right (by decide:0<2) bound))]
  exact congrArg (digit (B).arityBits u.val) read

variable (r : Recipe Tag Port) (node : r.Node ↪ Fin (L).nodes)
    (arg : ∀u,r.arity u≤(L).operands) (hidden : r.UsedWord↪Key)
local notation "idx" => (B).mouths r node arg
local notation "frag" => fun s : Slot r=>v.issuedFragment jobs x h g (idx s)

/-- Prior private aliases and both kinds of newly captured cable are identified at the
resolver's actual job ordinal. The constructor values for cables and pins are left visible. -/
structure SourceKeys : Prop where
  privateRead : ∀s u,DescentLocalPrivateNames.read r s=some u → resolve (frag s)=hidden u
  privateTag : ∀u,(hidden u).fields 0<3
  publicTag : ∀s,DescentLocalPrivateNames.read r s=none → 3≤(resolve (frag s)).fields 0

theorem reached_keys (keys : v.SourceKeys jobs x h g r node arg hidden) (p : Fin (B).outputs) :
    (B).Occurrences r node arg (input_ p) frag hidden :=
  ⟨fun s=>v.issued_stamp «meta» old jobs x h g p (idx s),keys.privateRead,keys.privateTag,keys.publicTag⟩

variable (floor : ℕ) (safe : (B).Early (v.finalSources floor) (v.metaEnd floor) w)
    (room : v.afterEnd floor<2^w) (m : Memory w)
    (newRead : ∀f b,Reads (v.nodeChart.bank (v.nodeBankBase floor) f b) («meta» f b) (L).lanes m)
    (spanRead : ∀b p,Reads (previousBank (L) (v.vectorOutput floor) b p) (old b p) (L).lanes m)
    (keyRead : ∀j,Reads (Banks.wordBank (L) (v.normalizedEnd floor) j)
      (fun h' g'=>word ((jobs j).compiled h' g')) (L).lanes m)
    (pos : 0<(L).lanes) (width : (B).field*(L).nodes*(L).lanes≤w)
local notation "out" => (v.argumentsAfter floor safe room).image m
local notation "page_" f:arg s:arg => ((B).pages ((f:Fin 4).castLE (by decide),(s:Slot r).2.castLE (arg s.1)))
local notation "bank_" p:arg => previousBank (L) ((B).out (v.metaEnd floor)) x p

/-- The literal host address, packed group lane and packed node ordinal. -/
def headerDigit (o:Memory w) (bank:Bank) (number:Fin (L).nodes) : ℕ :=
  digit (B).field number.val (digit ((B).field*(L).nodes) (g.val%(L).lanes)
    (o (bank.base+(g.val/(L).lanes+chunks (L).groups (L).lanes*h.val))).val)

include newRead spanRead keyRead pos width in
theorem issued_digit (p : Fin (B).outputs) (number : Fin (L).nodes) :
    v.headerDigit h g out (bank_ p) number=
      digit (B).field number.val ((B).law p (input_ p)).val := by
  have stored:=v.argumentsAfter_issued floor safe room m «meta» old jobs newRead spanRead keyRead x p
  have read:=PackedSource.read _ out (bank_ p).base pos width stored h g
  exact congrArg (digit (B).field number.val) read

variable (count : ∀u,digit (B).arityBits (node u).val («meta» 1 x h g).val=r.arity u)
    (absent : ∀j,(∀u,node u≠j)→digit (B).arityBits j.val («meta» 1 x h g).val=0)
    (keys : v.SourceKeys jobs x h g r node arg hidden)

include newRead spanRead keyRead pos width count absent keys in
theorem issued_private_header (s : Slot r) (u : r.UsedWord) (hit : DescentLocalPrivateNames.read r s=some u)
    (f : Fin 4) (fits : (Pointer.privateWord (firstAlias r idx u).val).header f<2^(B).field) :
    v.headerDigit h g out (bank_ (page_ f s)) (node s.1)=(Pointer.privateWord (firstAlias r idx u).val).header f := by
  let p:=page_ f s
  have seen:=v.reached_keys «meta» old jobs x h g r node arg hidden keys p
  have one:=v.issued_arity «meta» old jobs x h g p
  exact (v.issued_digit «meta» old jobs x h g floor safe room m newRead spanRead keyRead pos width p (node s.1)).trans
    ((B).private_header r node arg (input_ p) (fun z=>(one _).trans (count z))
      (fun z empty=>(one _).trans (absent z empty)) seen s u hit f fits)

include newRead spanRead keyRead pos width count keys in
theorem issued_public_header (s : Slot r) (hit : DescentLocalPrivateNames.read r s=none)
    (f : Fin 4) (fits : (Pointer.ofKey 0 (resolve (frag s))).header f<2^(B).field) :
    v.headerDigit h g out (bank_ (page_ f s)) (node s.1)=(Pointer.ofKey 0 (resolve (frag s))).header f := by
  let p:=page_ f s
  have seen:=v.reached_keys «meta» old jobs x h g r node arg hidden keys p
  exact (v.issued_digit «meta» old jobs x h g floor safe room m newRead spanRead keyRead pos width p (node s.1)).trans
    ((B).public_header r node arg (input_ p) (fun u=>(v.issued_arity «meta» old jobs x h g p _).trans (count u)) seen s hit f fits)

include newRead spanRead keyRead pos width count in
/-- A genuine surviving cable or pin can be read as soon as its own resolver
job has been identified, irrespective of the choice of aliases at other slots. -/
theorem issued_public_at (s : Slot r) (pub : 3≤(resolve (frag s)).fields 0)
    (f : Fin 4) (fits : (Pointer.ofKey 0 (resolve (frag s))).header f<2^(B).field) :
    v.headerDigit h g out (bank_ (page_ f s)) (node s.1)=
      (Pointer.ofKey 0 (resolve (frag s))).header f := by
  let p:=page_ f s
  have live := (B).mouth_live r node arg (input_ p)
    (fun u=>(v.issued_arity «meta» old jobs x h g p _).trans (count u)) s
  have projected : Pointer.ofKey (renameDigit ((B).marked (input_ p)) (idx s)-1) (resolve (frag s))=
      Pointer.ofKey 0 (resolve (frag s)) := by
    cases eqn : resolve (frag s) <;> simp [Pointer.ofKey,Key.fields,eqn] at pub ⊢
  exact (v.issued_digit «meta» old jobs x h g floor safe room m newRead spanRead keyRead pos width p
    (node s.1)).trans (((B).header f _ _ (input_ p) live _ (v.issued_stamp «meta» old jobs x h g p (idx s))
      (projected.symm ▸ fits)).trans (congrArg (fun z : Pointer=>z.header f) projected))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

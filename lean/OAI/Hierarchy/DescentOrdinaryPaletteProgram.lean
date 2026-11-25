import OAI.Hierarchy.DescentOrdinaryPaletteLayout
import OAI.Hierarchy.DescentOrdinaryRefsROM
import OAI.Hierarchy.DescentPackedScalarDonorOperands

namespace OAI
/-! The same numerical date on every old state, from the immutable primitive and original donor files. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPacking.PackedMatch.Local DescentHaloWalkRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {w : ℕ} (L : Layout) (base : ℕ) (B : L.Inputs)
local notation "H" => L.hosts
local notation "O" => L.oldGroups
local notation "M" => L.oldWork
local notation "D" => L.degree
local notation "P" => L.ports
local notation "k" => L.k
local notation "K" => L.oldNodes
local notation "cap" => L.capacity
local notation "header" => L.portStart base
local notation "dict" => L.references (L.bookStart base)
local notation "spread" => L.spreadStart base
local notation "C" => L.joinStart base
local notation "returned" => L.durableStart base
local notation "old" => L.prior.bank base
local notation "fresh" => fun x t j=>L.births.bank (L.birthStart base) (L.bornIndex x t j)
local notation "origin" => L.origins.bank (L.originStart base)
local notation "roster" => DescentScalarHaloPortROM.chart H O M P header B.halo

def field (j : Fin L.candidates) : Expr :=
  operand roster old fresh (dict).dictionary H (bookRoot D k K cap j) (bookBlock D k K cap j) (bookItem D k K cap j)
def pool : Expr :=Gather.assembly (dict).gates (L.field base B)

def portPhase (w : ℕ) : NativePhase w :=
  ⟨DescentScalarHaloPortROM.program H O M P w header,4+10*DescentScalarHaloPortROM.length H O M P,
    DescentScalarHaloPortROM.image H O M P header,@DescentStaticWordColumn.cheap _ _ _ _⟩
def refPhase (w : ℕ) : NativePhase w :=
  ⟨(dict).program w,(4+10*(dict).digitSize)+(4+10*(dict).tableSize),(dict).output,
    cheap_seq (ROM.cheap _ _ _ _) (ROM.cheap _ _ _ _)⟩
def head (w : ℕ) : NativePhase w :=
  ((((L.prior.phase base B.previous w).seq (L.births.phase (L.birthStart base) B.newborn w)).seq
    (L.origins.phase (L.originStart base) B.origin w)).seq (L.portPhase base w)).seq (L.refPhase base w)
def poolPhase (w : ℕ) :=L.spread.phase spread (fun _=>L.pool base B) w
def chosen (w : ℕ) :=L.join.phase C origin (L.spread.returned spread) w
def finishPhase (w : ℕ) :=L.durable.phase returned (L.join.bank C) w
def phase (w : ℕ) : NativePhase w :=
  (((L.head base B w).seq (L.poolPhase base B w)).seq (L.chosen base w)).seq (L.finishPhase base w)

theorem cuts : base≤L.birthStart base ∧ L.birthStart base≤L.originStart base ∧ L.originStart base≤header ∧
    header≤L.bookStart base ∧ L.bookStart base≤ spread ∧ spread≤C ∧ C≤returned ∧ returned≤L.roof base:=by
  refine ⟨L.prior.base_le _,L.births.base_le _,L.origins.base_le _,?_,?_,?_,L.join.base_le _,L.durable.base_le _⟩
  · exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  · exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  · rw [joinStart,DescentOrdinaryOriginReshape.Layout.affine];exact Nat.le_add_right ..

structure Early (w : ℕ) : Prop where
  «old» : ∀x,(B.previous x).Fits w base
  births : ∀i,(B.newborn i).Fits w base
  «origin» : ∀x,(B.origin x).Fits w base
  halo : B.halo.Fits w base
  slots : H*P≤B.halo.size

def Keep (p : NativePhase w) (start stop : ℕ) : Prop :=
  ∀ m, p.Runs m ∧ ∀ i, i < start ∨ stop ≤ i → p.image m i=m i
theorem Keep.seq {p q : NativePhase w} {a b c : ℕ} (first : Keep p a b) (second : Keep q b c)
    (ab : a≤b) (bc : b≤c) : Keep (p.seq q) a c:=by
  intro m
  refine ⟨p.seq_runs q m (first m).1 (second _).1,?_⟩
  intro i hi
  exact ((second _).2 i (hi.imp_left (·.trans_le ab))).trans ((first m).2 i (hi.imp_right (bc.trans ·)))

theorem widen {w L U : ℕ} {b : Bank} (lo : L≤U) (fit : b.Fits w L) : b.Fits w U :=
  ⟨fit.1,fit.2.1,fit.2.2.trans lo⟩

theorem head_keeps (e : L.Early base B w) (room : spread<2^w) : Keep (L.head base B w) base spread:=by
  obtain ⟨p,q,r,s,t,_,_,_⟩:=L.cuts base
  have h : L.birthStart base≤ spread:=q.trans (r.trans (s.trans t))
  have j : L.originStart base≤ spread:=r.trans (s.trans t)
  have ph : Keep (L.portPhase base w) header (L.bookStart base):=by
    intro m
    have «until» : header+DescentScalarHaloPortROM.length H O M P≤L.bookStart base:=Nat.le_add_right ..
    have made:=DescentScalarHaloPortROM.mount H O M P header B.halo m («until».trans_lt (t.trans_lt room))
    exact ⟨made.1,fun i hi=>made.2.2.1 i (hi.imp_right («until».trans ·))⟩
  have dic : Keep (L.refPhase base w) (L.bookStart base) spread:=fun m=>⟨((dict).any m room).1,((dict).any m room).2.2.2⟩
  have pr : Keep (L.prior.phase base B.previous w) base (L.birthStart base):=
    fun m=>L.prior.any base B.previous m e.old (h.trans_lt room)
  have br : Keep (L.births.phase (L.birthStart base) B.newborn w) (L.birthStart base) (L.originStart base):=
    fun m=>L.births.any (L.birthStart base) B.newborn m (fun v=>widen p (e.births v)) (j.trans_lt room)
  have og : Keep (L.origins.phase (L.originStart base) B.origin w) (L.originStart base) header:=
    fun m=>L.origins.any (L.originStart base) B.origin m (fun v=>widen (p.trans q) (e.origin v)) ((s.trans t).trans_lt room)
  exact ((((pr.seq br p q).seq og (p.trans q) r).seq ph (p.trans (q.trans r)) s).seq dic
    (p.trans (q.trans (r.trans s))) t)

theorem field_fit (e : L.Early base B w) (room : spread<2^w) (j : Fin L.candidates) : (L.field base B j).Fits w spread:=by
  obtain ⟨p,q,r,s,t,_,_,_⟩:=L.cuts base
  have eb:=q.trans (r.trans (s.trans t))
  have ef:=r.trans (s.trans t)
  have scoped_ (b : Bank) (fit : b.Fits w spread) (size : H*chunks O M≤b.size) :=
    (DescentScalarHaloPortROM.geometry H O M P header spread B.halo b t room
      (widen (p.trans eb) e.halo) e.slots fit size).1
  have tables:=(dict).rooms (w:=w) le_rfl room
  let r₀:=bookRoot D k K cap j
  let b₀:=bookBlock D k K cap j
  let idx:=bookItem D k K cap j
  change (operand roster old fresh (dict).dictionary H r₀ b₀ idx).Fits w spread
  obtain ⟨id₀,at_⟩:=finSumFinEquiv.surjective idx
  unfold operand
  erw [←at_,finSumFinEquiv.symm_apply_apply id₀]
  cases id₀ with
  | inl n =>
    have b:=L.prior.placed base (w:=w) (eb.trans_lt room) b₀
    exact ⟨(tables.dictionary n).1,peer_fits roster _ spread (scoped_ _ (widen eb b.1) b.2) r₀⟩
  | inr u =>
    let z:=finProdFinEquiv.symm u
    have b:=L.births.placed (L.birthStart base) (w:=w) (ef.trans_lt room) (L.bornIndex b₀ z.1 z.2)
    exact peer_fits roster _ spread (scoped_ _ (widen ef b.1) b.2) r₀

theorem pool_fit (e : L.Early base B w) (room : spread<2^w) : (L.pool base B).Fits w spread:=
  Gather.fits (d:=L.primitiveBits) («M»:=M) _ _ _ (((dict).rooms (w:=w) le_rfl room).fields _ (L.field_fit base B e room)) (List.finRange _)

theorem any (e : L.Early base B w) (room : L.roof base<2^w) : Keep (L.phase base B w) base (L.roof base):=by
  obtain ⟨p,q,r,s,t,a,b,c⟩:=L.cuts base
  have cd:=c.trans_lt room
  have joinFit (x : Fin L.blocks) : (origin x).Fits w C ∧ (L.spread.returned spread x).Fits w C:=
    ⟨widen (s.trans (t.trans a)) (L.origins.placed (L.originStart base) (w:=w) (((s.trans t).trans (a.trans b)).trans_lt cd) x).1,
      (L.spread.returned_fits spread x (b.trans_lt cd)).1⟩
  have start:=p.trans (q.trans (r.trans (s.trans t)))
  have middle:=fun m=>L.spread.framed spread (fun _=>L.pool base B) m (fun _=>L.pool_fit base B e ((a.trans b).trans_lt cd)) (b.trans_lt cd)
  have selected_:=fun m=>L.join.any C origin (L.spread.returned spread) m joinFit cd
  have final_:=fun m=>L.durable.any returned (L.join.bank C) m (fun x=>(L.join.bank_fits C x cd).1) room
  exact (((L.head_keeps base B e ((a.trans b).trans_lt cd)).seq middle start a).seq selected_ (start.trans a) b).seq
    final_ ((start.trans a).trans b) c


end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

end OAI

import OAI.Hierarchy.DescentContactOutputOperands
import OAI.Hierarchy.DescentContactCatalog

namespace OAI
/-! # The original socket tally and the three selected first-live joint operands -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentContactDonorSelection DescentContactCoordinateJoint DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
set_option quotPrecheck false
local notation "D" => A.donor
local notation "H" => A.sparseHosts
local notation "G" => (D).groups
local notation "N" => (D).lows*(2*(D).cap)
local notation "M" => (D).batch
local notation "b" => (D).fieldBits
local notation "t" => A.metaBits
local notation "R" => 2^(Nat.clog 2 ((D).degree+2))
local notation "U" => A.choicePage first
local notation "E" => A.projected first
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
local notation "Q" => Fin A.sockets
local notation "own" => A.ownAt donorStart
local notation "other" => A.otherAt donorStart first
local notation "flag" => A.markFlag donorStart first
local notation "old_" => A.oldAt donorStart first u
local notation "here" => A.ownShape donorStart first
local notation "mass" => A.ownMass donorStart first

structure Indicators (q : Q) where
  «own» : Fin N→Fin H→Fin G→Cell b
  used : Fin N→Fin H→Fin G→Cell b
  remote : Fin N→Fin H→Fin G→Cell t
  «here» : Fin H→Fin G→Cell t
  halo : Bool→Fin N→Fin H→Fin G→Cell t
  «mass» : Fin H→Fin G→Cell t

namespace Indicators
variable {A} {q : Fin A.sockets} (x : Indicators A q)
def shape (s : Bool) (j : Fin N) :=if s=(A.socketWing q).1 then x.here else x.remote j
def atEnd (s : Bool) (j : Fin N) (h : Fin H) (g : Fin G) :=join R (x.shape s j h g) (x.halo s j h g)
def ticket (j : Fin N) (h : Fin H) (g : Fin G) : Cell b:=(A.request q)*(x.used j h g).val
def item (s : Option Bool) (j : Fin N) (h : Fin H) (g : Fin G) : Cell t:=
  match s with
  | none=>x.atEnd (A.socketWing q).1 j h g
  | some e=>keep (A.request q) (x.ticket j h g) (x.atEnd e j h g)
def selected (s : Option Bool) (h : Fin H) (g : Fin G) : Cell t:=visits (A.request q) (fun j=>x.own j h g) (fun j=>x.item s j h g)
def output : Fin 4→Fin H→Fin G→Cell t:=![x.mass,x.selected (some false),x.selected (some true),x.selected none]
end Indicators

structure InputFits (q : Q) (w : ℕ) : Prop where
  «own» : ∀j,(own q j).Fits w U
  used : ∀j,(flag q j).Fits w U
  remote : ∀j,(other q j).Fits w U
  «here» : (here).Fits w U
  halo : ∀s j,(old_ s j).Fits w U
  «mass» : (mass q).Fits w U

def InputRead (q : Q) (x : Indicators A q) (m : Memory w) :=
  (∀j,Source (own q j) (x.own j) M m) ∧ (∀j,Source (flag q j) (x.used j) M m) ∧
  (∀j,Source (other q j) (x.remote j) M m) ∧ Source here x.here M m ∧
  (∀s j,Source (old_ s j) (x.halo s j) M m) ∧ Source (mass q) x.mass M m

private theorem match_fits (j : Q) {left right : Expr} (l : left.Fits w E) (r : right.Fits w E) (room : E<2^w) :
    Fits (DescentResetDonorBook.table A.request b t M U j.succ) left right b t M E w:=by
  let P:=DescentResetDonorBook.page A.request b t M
  have bank (i : Fin 2) :=ROM.bank_room P A.choiceBits U E (DescentResetDonorBook.ix j.succ i)
    (DescentResetDonorBook.size A.request b t M _) le_rfl room
  have width (i : Fin 2):=(congrArg ROM.Page.bits (DescentResetDonorBook.request_page A.request b t M j i))
  exact ⟨l,r,bank 0,bank 1,width 0,width 1⟩

private theorem scaled_source {hostCount groupCount fieldWidth laneCount w : ℕ} (k : ℕ) (e : Expr) (x : Fin hostCount→Fin groupCount→Cell fieldWidth) (m : Memory w)
    (held : Source e x laneCount m) (small : ∀h g,k*(x h g).val<2^fieldWidth) :
    Source (ProtocolRAM.scale k e) (fun h g=>((k*(x h g).val:ℕ):Cell fieldWidth)) laneCount m:=by
  intro p
  have packed : k*(data x p).val=(data (fun h g=>((k*(x h g).val:ℕ):Cell fieldWidth)) p).val:=by
    simp only [DescentPackedSumWords.lanes_val,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split
    · rename_i inside
      let g : Fin groupCount := ⟨p.2.val*laneCount+j.val,inside⟩
      exact (Nat.mul_assoc k (x p.1 g).val ((2^fieldWidth)^j.val)).symm.trans
        (congrArg (fun n : ℕ => n*(2^fieldWidth)^j.val) (Fin.val_cast_of_lt (small p.1 g)).symm)
    · simp
  rw [ProtocolRAM.eval_scale,held p,←Nat.cast_mul,packed]

theorem fields_read (q : Q) (x : Indicators A q) (m : Memory w) (r : A.InputFits donorStart first u q w)
    (room : E<2^w) (prior : A.InputRead donorStart first u q x m)
    (requestFits : ∀j h g,A.request q*(x.used j h g).val<2^b)
    (coordinateFits : ∀s j h g,number R (x.shape s j h g).val (x.halo s j h g).val<2^t) (f : Fin 4) :
    Source (A.fieldsAt donorStart first u q f) (x.output f) M (A.choices first m):=by
  obtain ⟨_,firstBook,matchBook,frame,_,_⟩:=DescentResetDonorBook.installed A.request b t M U m room
  let dst:=A.choices first m
  have up {e : Expr} (h : e.Fits w U) := ProtocolRAMGeneratedWrite.fits_mono _ (show U≤E from Nat.le_add_right ..) h
  have kept {a : ℕ} {e : Expr} {v : Fin H→Fin G→Cell a} (fit : e.Fits w U) (src : Source e v M m) : Source e v M dst:=
    fun p=>(eval_below _ _ m dst fit (fun z h=>frame z (.inl h))).trans (src p)
  obtain ⟨sourceOwn,sourceUsed,sourceOther,sourceHere,sourceHalo,sourceMass⟩:=prior
  have joint (s : Bool) (j : Fin N) : (A.endsAt donorStart first u q j s).Fits w E ∧
      Source (A.endsAt donorStart first u q j s) (x.atEnd s j) M dst:=by
    let sh:=if s=(A.socketWing q).1 then here else other q j
    have fits_ : sh.Fits w E := by
      by_cases h : s=(A.socketWing q).1
      · simpa only [sh,ite_eq_left h] using up r.here
      · simpa only [sh,ite_eq_right h] using up (r.remote j)
    have read_ : Source sh (x.shape s j) M dst:=by
      by_cases h:s=(A.socketWing q).1
      · simpa [sh,Indicators.shape,h] using kept r.here sourceHere
      · simpa [sh,Indicators.shape,h] using kept (r.remote j) (sourceOther j)
    exact ⟨DescentContactCoordinateJoint.fits R _ _ fits_ (up (r.halo s j)),
      DescentContactCoordinateJoint.source R _ _ dst _ _ (coordinateFits s j) read_ (kept (r.halo s j) (sourceHalo s j))⟩
  have select (s : Option Bool) : Source (A.selectAt donorStart first u q s) (x.selected s) M dst:=by
    let cargo:=fun j=>A.witnessAt donorStart first u q j s
    have carried (j : Fin N) : (cargo j).Fits w E ∧ Source (cargo j) (x.item s j) M dst:=by
      cases s with
      | none=>exact joint _ _
      | some e=>
        let k:=A.request q
        have raw:=scaled_source k (flag q j) (x.used j) dst (kept (r.used j) (sourceUsed j)) (requestFits j)
        have readTicket : Source (ProtocolRAM.scale k (flag q j)) (x.ticket j) M dst := by
          have label : (fun h g => ((k*(x.used j h g).val : ℕ) : Cell b)) = x.ticket j := by
            funext h g
            first | rfl | exact Nat.cast_mul _ _
          simpa only [label] using raw
        have guard:=A.match_fits first q (scaled_fits _ (up (r.used j)) k) (joint e j).1 room
        exact ⟨⟨guard.apply,guard.right,guard.shift,guard.left⟩,
          read_data _ _ _ _ guard _ (by simp [keep]) dst (matchBook q) _ _ readTicket (joint e j).2⟩
    let P:=DescentResetDonorBook.page A.request b t M
    have bank (i : Fin 2):=(ROM.bank_room P A.choiceBits U E (DescentResetDonorBook.ix 0 i)
      (DescentResetDonorBook.size A.request b t M _) le_rfl room)
    have bits (i : Fin 2):=congrArg ROM.Page.bits (DescentResetDonorBook.prefer_page A.request b t M i)
    exact (DescentContactDonorCargo.fold_source _ _ (A.request q) _ _ E dst _ _
      (fun j=>A.match_fits first q (up (r.own j)) (carried j).1 room)
      (fun j=>⟨kept (r.own j) (sourceOwn j),(carried j).2⟩) (matchBook q) (bank 0) (bank 1) (bits 0) (bits 1) firstBook).2
  fin_cases f
  · exact kept r.mass sourceMass
  all_goals exact select _

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI

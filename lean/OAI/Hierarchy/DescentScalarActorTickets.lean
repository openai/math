import OAI.Hierarchy.DescentScalarVenueMask
import OAI.Hierarchy.DescentPackedActorHeadRAM
import OAI.Hierarchy.DescentPackedActorPath

namespace OAI
/-! # Read old and six-party scalar venue tickets from the actual owner register -/
namespace Hierarchy.DescentScalarVenueMask
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedCableNames DescentPacking.PackedMatch.Local
open DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
variable {r D p d k slots raw H G M w : ℕ}

def unwalk (b : ℕ) (v : Cell (b*4)) : Walk:=let q:=(encode b 4).symm v;((q 0).val,(q 1).val,(q 2).val,(q 3).val)

def Bounded (b : ℕ) (v : Walk) :=v.1<2^b ∧ v.2.1<2^b ∧ v.2.2.1<2^b ∧ v.2.2.2<2^b

theorem unwalk_word (b : ℕ) (v : Walk) (fit : Bounded b v) : unwalk b (Owners.routeWord b v)=v :=by
  rcases v with ⟨h,i,j,t⟩;rcases fit with ⟨hh,hi,hj,ht⟩
  simp [unwalk,Owners.routeWord,word,Nat.mod_eq_of_lt hh,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt ht]

def issue (D slots raw : ℕ) (v : Walk) : Ticket (breadth D) raw:=
  let n:=v.2.2.1*slots+v.2.2.2
  if yes:n<raw then some (ActorPath.index D v,⟨n,yes⟩) else none

def oldTicket (x : Fin r) (slots raw : ℕ) (present : Cell (1*r)) (reg : Owners.Register r D d) :=
  if (encode 1 r).symm present x=0 then none else issue D slots raw (0,Owners.addressed reg x)

def newTicket (x : Fin r) (s : Fin p) (j : Fin 6) (slots raw : ℕ) (present : Cell (1*r)) (report : Cell (Owners.outputBits r D p d)) :=
  let bits:=Owners.digits r D d
  let piece:=(encode ((bits*4)*8) (r*p)).symm report (finProdFinEquiv (x,s))
  let records:=(encode (bits*4) 8).symm piece
  if (encode 1 r).symm present x=0 ∨ records 0=0 then none
  else issue D slots raw (unwalk bits (records j.succ.succ))

theorem old_read (x : Fin r) (mask : Cell (1*r)) (B n : ℕ) (l : Bool) (u : Panel r D p d) (live : (encode 1 r).symm mask x≠0) :
    oldTicket x slots raw mask (Owners.render r D p d B n (Owners.register l u))=issue D slots raw (0,resolved B n u l x) :=by
  simp [oldTicket,live,Owners.addressed_read]

/-- This is also valid for an isolated old site. Its old target only uses
its prior actor bit and its own three-field resolved venue register. -/
theorem old_missing (x : Fin r) (mask : Cell (1*r)) (reg : Owners.Register r D d) (absent : (encode 1 r).symm mask x=0) :
    oldTicket x slots raw mask reg=none :=by simp [oldTicket,absent]

theorem new_missing (x : Fin r) (s : Fin p) (j : Fin 6) (mask : Cell (1*r)) (report : Cell (Owners.outputBits r D p d)) (absent : (encode 1 r).symm mask x=0) :
    newTicket x s j slots raw mask report=none:=by simp [newTicket,absent]

theorem new_at (x : Fin r) (s : Fin p) (j : Fin 6) (mask : Cell (1*r)) (report : Cell (Owners.outputBits r D p d)) (heads : Heads)
    (shelf : (encode ((Owners.digits r D d*4)*8) (r*p)).symm report (finProdFinEquiv (x,s))=Owners.headWord (Owners.digits r D d) heads)
    (live : (encode 1 r).symm mask x≠0) (positive : 0<Owners.digits r D d)
    (bounded : ∀born,heads.born=some born→Bounded (Owners.digits r D d) (born j)) :
    newTicket x s j slots raw mask report=heads.born.bind (fun b=>issue D slots raw (b j)) :=by
  have one:(1:Cell (Owners.digits r D d*4))≠0:=by
    intro e;have h:=congrArg Fin.val e
    have wide : 1<2^(Owners.digits r D d*4):=Nat.one_lt_two_pow (by omega)
    simp [Nat.mod_eq_of_lt wide] at h
  cases born:heads.born with
  | none=>simp [newTicket,shelf,Owners.headWord,born,live]
  | some b=>simp [newTicket,shelf,Owners.headWord,born,live,one,unwalk_word _ _ (bounded _ born)]

private theorem addressed_fit (reg : Owners.Register r D d) (x : Fin r) :
    let q:=Owners.addressed reg x;q.1<2^Owners.digits r D d ∧ q.2.1<2^Owners.digits r D d ∧ q.2.2<2^Owners.digits r D d:=by
  exact ⟨Fin.isLt _,Fin.isLt _,Fin.isLt _⟩

theorem look_fit (here : Owners.Register r D d) (peer : Fin D→Owners.Register r D d) (z : ℕ×ℕ) (hop : z.1≤D) :
    Bounded (Owners.digits r D d) (look (Owners.addressed here) (fun v=>Owners.addressed (peer v)) z) :=by
  have width : D<2^Owners.digits r D d:= (Nat.lt_succ_of_le (le_max_right r D)).trans_le
    ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (le_max_right ..)))
  refine ⟨hop.trans_lt width,?_⟩
  unfold look
  split
  · split
    · exact addressed_fit ..
    · split
      · exact addressed_fit ..
      · exact ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _⟩
  · exact ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _⟩

/-- Mask and register are the real two packed inputs. The binary dictionary
emits either the short halo query or the local heap/pack from the same tag. -/
theorem source {a b P N bitsOut : ℕ} (T : Tables) (mask data_ : Expr) (base : ℕ) (m : Memory w)
    (actor : Cell a→Cell b→Ticket P N) (project : Ticket P N→Cell bitsOut) (blank : actor 0 0=none) (padding : project none=0)
    (admit : Fin H→Fin G→Cell a) (rows : Fin H→Fin G→Cell b) (present : Source mask admit M m) (actual : Source data_ rows M m)
    (room : DescentPackedZip.Fits T mask data_ a b M base w) (statics : Static T (fun x y=>project (actor x y)) M m) :
    Source (T.read mask data_) (fun h g=>project (actor (admit h g) (rows h g))) M m :=
  read_data T mask data_ base room _ (by rw [blank,padding]) m statics _ _ present actual

end
end Hierarchy.DescentScalarVenueMask

end OAI

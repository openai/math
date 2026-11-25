import OAI.Hierarchy.DescentScalarVenueDirectory
import OAI.Hierarchy.DescentPackedHostLookup
import OAI.Hierarchy.DescentSharedCableSerial
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedTrimOwner

namespace OAI
/-! # Receiving old and six-party actor tickets at their actual coalesced venue -/
namespace Hierarchy.DescentScalarVenueMask
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedCableNames DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
variable {P raw low k gain slots H G M w : ℕ}
local notation "SIMD" => DescentPackedChildNeighbor.SIMD.Chart

abbrev Ticket (P raw : ℕ) :=Option (Fin P×Fin raw)
def pathCode (t : Ticket P raw) :=Packed.token (t.map Prod.fst)
def localCode (t : Ticket P raw) :=Packed.token (t.map Prod.snd)

def reached (walks : Fin H→Fin P→Option (Fin H)) (s : Fin P) (h : Fin H) (t : Ticket P raw) :=
  (t.map fun z=>DescentScalarVenueDirectory.hit walks s h z.1).getD false

def checks (walks : Fin H→Fin P→Option (Fin H)) (s : Fin P) (h : Fin H) (p : Fin P) : Cell 1 :=(DescentScalarVenueDirectory.hit walks s h p).toNat

theorem check_at (walks : Fin H→Fin P→Option (Fin H)) (s : Fin P) (h : Fin H) (t : Ticket P raw) :
    DescentPackedChildNeighbor.SIMD.lookup (checks walks s h) (pathCode t) (List.finRange P)=((reached walks s h t).toNat:Cell 1) :=by
  cases t with
  | none=>apply DescentPackedChildNeighbor.SIMD.lookup_missing;intro j;simp [pathCode,Packed.token]
  | some z=>rw [DescentPackedChildNeighbor.SIMD.lookup_at _ _ z.1 (by rfl),ite_eq_left (List.mem_finRange _)];rfl

/-- An unsigned low key from the pointed-to host is retained exactly when
its path arrives. Zero remains the distinct missing token. -/
def keepRaw (b : Cell 1) (code : Cell (Packed.bits raw)) : Cell (Packed.bits raw) :=if b=0 then 0 else code

def trimmed (k gain slots raw low : ℕ) (hub : Cell 1) (code : Cell (Packed.bits raw)) : Cell (Packed.bits low) :=
  Packed.token ((Packed.readToken raw code).bind fun j=>
    let v:=DescentHostDirectory.SiteDecode.trim k gain slots (hub≠0) j.val
    if yes:v<low then some ⟨v,yes⟩ else none)

def returned (k gain slots raw low : ℕ) (walks : Fin H→Fin P→Option (Fin H)) (s : Fin P) (h : Fin H) (hub : Cell 1) (t : Ticket P raw) :=
  trimmed k gain slots raw low hub (keepRaw ((reached walks s h t).toNat:Cell 1) (localCode t))

theorem returned_iff (walks : Fin H→Fin P→Option (Fin H)) (s : Fin P) (h : Fin H) (hub : Cell 1) (t : Ticket P raw) (l : Fin low) :
    returned k gain slots raw low walks s h hub t=Packed.token (some l) ↔
      ∃p v,t=some (p,v) ∧ DescentScalarVenueDirectory.hit walks s h p=true ∧
        DescentHostDirectory.SiteDecode.trim k gain slots (hub≠0) v.val=l.val :=by
  have token {x y : Option (Fin low)} : Packed.token x=Packed.token y ↔ x=y:=by
    constructor
    · intro h;simpa only [Packed.token_back] using congrArg (Packed.readToken low) h
    · exact congrArg Packed.token
  unfold returned trimmed
  rw [token]
  cases t with
  | none=>simp [reached,keepRaw,show (0:Cell (Packed.bits raw))=Packed.token (none : Option (Fin raw)) from rfl]
  | some z =>
    rcases z with ⟨p,v⟩
    cases yes : DescentScalarVenueDirectory.hit walks s h p with
    | false =>
      simp [yes,reached,keepRaw,show (0:Cell (Packed.bits raw))=Packed.token (none : Option (Fin raw)) from rfl]
    | true =>
      have arrived : reached walks s h (some (p,v)) = true := yes
      have pass : keepRaw (true.toNat : Cell 1) (localCode (some (p,v))) = Packed.token (some v) := by
        exact ite_eq_right (by decide : (true.toNat : Cell 1) ≠ 0)
      rw [arrived,pass,Packed.token_back]
      let value := DescentHostDirectory.SiteDecode.trim k gain slots (hub≠0) v.val
      change (if valid : value < low then some (⟨value,valid⟩ : Fin low) else none) = some l ↔ _
      constructor
      · intro accepted
        by_cases valid : value < low
        · rw [dite_eq_left valid] at accepted
          exact ⟨p,v,rfl,yes,congrArg Fin.val (Option.some.inj accepted)⟩
        · rw [dite_eq_right valid] at accepted
          cases accepted
      · rintro ⟨p',v',ticket,_,same⟩
        have local_eq : v = v' := congrArg Prod.snd (Option.some.inj ticket)
        subst v'
        have equal : value = l.val := same
        have valid : value < low := equal.trans_lt l.isLt
        rw [dite_eq_left valid]
        exact congrArg some (Fin.ext equal)

structure Hardware (P : ℕ) where
  host : DescentPackedChildNeighbor.SIMD.Chart P
  prior : Tables
  trim : Tables

def expr (C : Hardware P) (path local_ hub : Expr) :=C.trim.read hub (C.prior.read (DescentPackedChildNeighbor.SIMD.body C.host path (List.finRange P)) local_)

/-- These operands come from the path and raw-low fields of the same
optional actor ticket, the numerical per-rack direction table, and the
current receiver's actual hub bit. -/
theorem from_chips (C : Hardware P) (path local_ hub : Expr) (base : ℕ) (m : Memory w)
    (walks : Fin H→Fin P→Option (Fin H)) (s : Fin P) (t : Fin H→Fin G→Ticket P raw) (hubs : Fin H→Fin G→Cell 1)
    (bits : Source path (fun h g=>pathCode (t h g)) M m) (loc : Source local_ (fun h g=>localCode (t h g)) M m)
    (flags : Source hub hubs M m) (space : DescentPackedChildNeighbor.SIMD.Room C.host path H G (Packed.bits P) 1 M w base)
    (directory : DescentPackedChildNeighbor.SIMD.Stored C.host H G (Packed.bits P) 1 M (checks walks s) m)
    (first : DescentPackedZip.Fits C.prior (DescentPackedChildNeighbor.SIMD.body C.host path (List.finRange P)) local_ 1 (Packed.bits raw) M base w)
    (last : DescentPackedZip.Fits C.trim hub (C.prior.read (DescentPackedChildNeighbor.SIMD.body C.host path (List.finRange P)) local_) 1 (Packed.bits raw) M base w)
    (keepROM : Static C.prior (keepRaw (raw:=raw)) M m) (trimROM : Static C.trim (trimmed k gain slots raw low) M m) :
    Source (expr C path local_ hub) (fun h g=>returned k gain slots raw low walks s h (hubs h g) (t h g)) M m :=by
  have yes:=DescentPackedChildNeighbor.SIMD.measures C.host path base space (checks walks s) m directory _ bits (List.finRange P)
  simp only [check_at] at yes
  have incoming:=read_data C.prior _ _ base first (keepRaw (raw:=raw)) (by simp [keepRaw]) m keepROM _ _ yes loc
  exact read_data C.trim hub _ base last (trimmed k gain slots raw low) (by simp [trimmed,Packed.readToken,Packed.token]) m trimROM _ _ flags incoming

end
end Hierarchy.DescentScalarVenueMask

end OAI

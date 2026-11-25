import OAI.Hierarchy.DescentSignedPrimitiveBanks
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentSignedPrefixReceipt

namespace OAI
/-! Access to genuine entries of the append-only prefix, shared binary
tables, and earlier input words used by the ordinary renderer. -/
namespace Hierarchy.DescentDatedAddressBook.SignedPrefix
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def start (base:ℕ):List Job→ℕ→ℕ
  | [],_=>base
  | _::_,0=>base
  | j::js,n+1=>start (base+j.width) js n

theorem at_job {w:ℕ} (m:Memory w) (js:List Job) (base n:ℕ) (live:n<js.length) (sheets:Written m js base):
    (js[n]).Written (start base js n) m:=by
  induction js generalizing base n with
  | nil=>simp at live
  | cons j js ih=>
    cases n with
    | zero=>exact sheets.1
    | succ n=>exact ih (base+j.width) n (by simpa using live) sheets.2

theorem at_table {w a b d M n:ℕ} (m:Memory w) (f:Cell a→Cell b→Cell d)
    (pages:Fin n→DescentOrdinaryAtomFieldRAM.ROM.Page) (width base:ℕ) (ptr:Fin 2→Fin n)
    (room:∀j,(pages j).bits≤width)
    (shape:∀i,pages (ptr i)=DescentOrdinaryAtomFieldRAM.ROM.binary f M i)
    (real:(SignedExtent.lit pages width).Written base m):
    Static (DescentOrdinaryAtomFieldRAM.ROM.joined pages width base ptr) f M m:=by
  let after:=DescentOrdinaryAtomFieldRAM.ROM.after pages width base m
  have keep (p:Fin n) (i:Cell (pages p).bits):
      m ((DescentOrdinaryAtomFieldRAM.ROM.bank pages width base p).base+i.val)=
        after ((DescentOrdinaryAtomFieldRAM.ROM.bank pages width base p).base+i.val):=by
    have inner:i.val<2^width:=i.isLt.trans_le (Nat.pow_le_pow_right (by decide) (room p))
    have hi:p.val*2^width+i.val<n*2^width:=(Nat.add_lt_add_left inner _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ p.isLt)
    simpa only [after, DescentOrdinaryAtomFieldRAM.ROM.after,
      DescentOrdinaryAtomFieldRAM.ROM.bank, Nat.add_assoc] using
      (real ⟨_,hi⟩).trans (DescentStaticWordColumn.read base (n*2^width) (DescentOrdinaryAtomFieldRAM.ROM.contents pages width) m hi).symm
  have installed:=DescentOrdinaryAtomFieldRAM.ROM.binary_mounted f M pages width base m room ptr shape
  constructor
  · intro i
    have h:(pages (ptr 0)).bits=a*M:=by rw [shape];rfl
    exact (keep (ptr 0) (Fin.cast (congrArg (2^·) h.symm) i)).trans (installed.1 i)
  · intro i
    have h:(pages (ptr 1)).bits=(a+b)*M:=by rw [shape];rfl
    exact (keep (ptr 1) (Fin.cast (congrArg (2^·) h.symm) i)).trans (installed.2 i)

theorem column_read {w H G M b count:ℕ} (m:Memory w) (base:ℕ) (expr:Fin count→Expr)
    (written:(SignedExtent.col count (H*chunks G M) (SignedExtent.fromIndex expr)).Written base m)
    (j:Fin count) (v:Fin H→Fin G→Cell b) (measured:Source (expr j) v M m):
    Reads (SignedExtent.subbank base (H*chunks G M) j.val) v M m:=by
  intro p
  exact (written j (row H G M p)).trans (by simpa [SignedExtent.fromIndex,j.isLt] using measured p)

theorem column_source {w H G M b:ℕ} (m:Memory w) (B:Bank) (v:Fin H→Fin G→Cell b)
    (read:Reads B v M m) (bits:(H*chunks G M)≤B.size) (wide:B.size<2^w):
    Source (.lookup B .row) v M m:=by
  intro r
  have h:(row H G M r).val<B.size:=(row H G M r).isLt.trans_le bits
  change m (B.base+((↑(row H G M r).val:Word w).val%B.size))=_
  rw [Fin.val_natCast,Nat.mod_eq_of_lt (h.trans wide),Nat.mod_eq_of_lt h]
  exact read r

theorem from_prior {w H G M b base:ℕ} (m m':Memory w) (e:Expr) (v:Fin H→Fin G→Cell b)
    (before:∀a<base,m' a=m a) (early:e.Fits w base) (reads:Source e v M m):Source e v M m':=
  fun q=>(eval_below e _ m m' early before).trans (reads q)


end
end Hierarchy.DescentDatedAddressBook.SignedPrefix

end OAI

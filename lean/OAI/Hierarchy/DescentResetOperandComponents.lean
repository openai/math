import OAI.Hierarchy.DescentResetOperandRendered
import OAI.Hierarchy.DescentResetRetainedFields
import OAI.Hierarchy.DescentOperandFieldJoin

namespace OAI
/-! # The seven actual values read across a reset at a cable, original pin, or private operand -/
namespace Hierarchy.DescentResetOperandComponents
open DescentSIMDLookup DescentPackedZip DescentResetOperandSlices DescentOperandStateBanks DescentNextSignedWindow
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {b t H G w M : ℕ}

def correction (unit : ℕ) (r : Role) (f : Field) (tag : Cell b) (hub : Cell 1) (chunk : Cell b) : Cell b :=
  if f.val=2 then part unit true (mode r tag hub) chunk else
  if f.val=3 then part unit false (mode r tag hub) chunk else 0

def fresh (a n : ℕ) (f : Field) : ℕ :=
  if f=0 then 1 else if f=1 then a else if f=2 then n else 0

theorem no_cable (u : ℕ) (r : Role) (f : Field) (tag : Cell b) (hub : Cell 1) (chunk : Cell b)
    (other : tag.val≠1) : correction u r f tag hub chunk=0 :=by
  simp [correction,mode,other,part]

theorem from_cable {degree cap : ℕ} (u : ℕ) (up : 0<u) (role : Role) (old : Field→Cell b)
    (hub : Cell 1) (label : Cell t) (span : Span) (prevPeer prevSerial prevChunk : ℕ)
    (original : ∀f,(old f).val=(Pointer.cable prevPeer prevSerial prevChunk).fields span f)
    (coarse : Cell b) (row : Record degree cap) (live : DescentSharedCableNames.Stage.Live degree cap)
    (classify : marked role (decide (hub.val=1))=row.marked ∨ coarse.val<u)
    (read : render row (coarse.val/u)=some live) (f : Field) :
    (DescentResetRetainedPages.kept f (old 0) (old f) label).val+
      (correction u role f (old 0) hub coarse).val+fresh row.neighbor.val row.shared f=
      (Pointer.cable live.neighbor.val (live.wire.val-live.within.val)
        (if row.marked then coarse.val%u else coarse.val)).fields span f := by
  have tag : (old 0).val=1:=original 0
  have actual:=from_render role (old 0) hub u up coarse row live tag classify read
  have peer : live.neighbor=row.neighbor:=by
    simp [render] at read
    obtain ⟨_, rfl⟩ := read
    rfl
  rw [DescentResetRetainedPages.cable old prevPeer prevSerial prevChunk span label original f]
  fin_cases f <;> simp [fresh,correction,Pointer.fields,Pointer.header,peer,Nat.add_comm,←actual.1,actual.2]

theorem from_pin (u : ℕ) (role : Role) (x : Field→Cell b) (copy block : ℕ) (span : Span)
    (hub : Cell 1) (chunk : Cell b) (alias_ : Cell t)
    (old : ∀f,(x f).val=(Pointer.pin copy block).fields span f) (f : Field) :
    (DescentResetRetainedPages.kept f (x 0) (x f) alias_).val+(correction u role f (x 0) hub chunk).val=
      (Pointer.pin copy block).fields span f :=by
  have at0 : (x 0).val=2:=old 0
  rw [no_cable u role f (x 0) hub chunk (by omega),DescentResetRetainedPages.pin x copy block span alias_ old f]
  simp

theorem from_private (u : ℕ) (role : Role) (x : Field→Cell b) (oldName newName : ℕ) (span : Span)
    (hub : Cell 1) (chunk : Cell b) (alias_ : Cell t)
    (old : ∀f,(x f).val=(Pointer.privateWord oldName).fields span f)
    (name : alias_.val=newName+1) (room : newName<2^b) (f : Field) :
    (DescentResetRetainedPages.kept f (x 0) (x f) alias_).val+(correction u role f (x 0) hub chunk).val=
      (Pointer.privateWord newName).fields span f :=by
  have at0 : (x 0).val=0:=old 0
  rw [no_cable u role f (x 0) hub chunk (by omega),
    DescentResetRetainedPages.hidden x oldName newName span alias_ old name room f]
  simp

/-- The additional two local short fields are ordinary compiled row expressions:
everything outside columns two and three bypasses the lookup. -/
def expression (u b M base : ℕ) (r : Role) (f : Field) (kept tag hub chunk : Expr) : Expr :=
  if f.val=2 then .op .add kept (expr u b M base r true tag hub chunk) else
  if f.val=3 then .op .add kept (expr u b M base r false tag hub chunk) else kept

theorem charged (u base : ℕ) (r : Role) (f : Field) (kept tag hub chunk : Expr) (m : Memory w)
    (prior tx cx actual : Fin H→Fin G→Cell b) (hx : Fin H→Fin G→Cell 1)
    (early : kept.Fits w base) (te : tag.Fits w base) (he : hub.Fits w base) (ce : chunk.Fits w base)
    (ks : Source kept prior M m) (ts : Source tag tx M m) (hs : Source hub hx M m) (cs : Source chunk cx M m)
    (values : ∀h g,(prior h g).val+(correction u r f (tx h g) (hx h g) (cx h g)).val=(actual h g).val)
    (room : endAddress base b M<2^w) :
    (expression u b M base r f kept tag hub chunk).Fits w (endAddress base b M) ∧
    Source (expression u b M base r f kept tag hub chunk) actual M (image u b M base m) := by
  let done:=image u b M base m
  have step (a : Bool):=issue u b M base r a tag hub chunk m tx cx hx te he ce ts hs cs room
  have valid:=ProtocolRAMGeneratedWrite.fits_mono _ (show base≤endAddress base b M from Nat.le_add_right ..) early
  have keep : Source kept prior M done:=fun p=>(ProtocolRAM.eval_below kept _ m done early
    (fun j h=>(mount_any u b M base m room).2.1 j (.inl h))).trans (ks p)
  have add (a : Bool) (port : ∀h g,correction u r f (tx h g) (hx h g) (cx h g)=part u a (mode r (tx h g) (hx h g)) (cx h g)) :
      Source (.op .add kept (expr u b M base r a tag hub chunk)) actual M done :=by
    intro p
    change kept.eval done _+(expr u b M base r a tag hub chunk).eval done _=_
    rw [keep p,(step a).2 p,←Nat.cast_add]
    apply congrArg (fun n : ℕ=>(n:Word w))
    apply DescentOperandFieldJoin.packed_add
    intro h g;rw [←port];exact values h g
  dsimp only [expression]
  split
  · rename_i two
    exact ⟨⟨valid,(step true).1⟩,add true (fun _ _=>by simp [correction,two])⟩
  · rename_i two
    split
    · rename_i three
      exact ⟨⟨valid,(step false).1⟩,add false (fun _ _=>by simp [correction,three])⟩
    · rename_i three
      have same : prior=actual:=by
        funext h g;apply Fin.ext;simpa [correction,two,three] using values h g
      exact ⟨valid,same ▸ keep⟩

end
end Hierarchy.DescentResetOperandComponents

end OAI

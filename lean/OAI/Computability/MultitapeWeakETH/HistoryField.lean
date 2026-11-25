import OAI.Computability.MultitapeWeakETH.ChildScan

/-! # Reading a child argument's incoming or outgoing field length -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan

open IntegerMultiplication Code VPVNP Compression CompressorRecords BurstRAM
open PairSimulation LocalHistory TerminalWords
open private address address_poly address_eq from OAI.Computability.MultitapeWeakETH.TerminalColumns
open private start start_poly start_eq from OAI.Computability.MultitapeWeakETH.ChildScan
open scoped Fin.CommRing
noncomputable section

variable {A : Type} [Codec A] (read : A × Bits.Word → Bits.Word)

abbrev FieldQuery (A : Type) := Query A × Tally

/-- The site and slot are unary. All pointer arithmetic uses the native word width.
Incoming slots follow the inverse permutation before consulting the width column. -/
def field (incoming : Bool) (q : FieldQuery A) : Tally :=
  let ctx := q.1.1.1.1
  let head := q.1.1.1.2
  let fetch (j : ℕ) := read (ctx,address (head,tally j))
  let row (base : Bits.Word) := address (start ((base,fetch 16),q.1.2),q.2)
  let width := fetch 20
  let pos := bif incoming then start ((width,read (ctx,row (fetch 19))),tally 1) else row width
  capped (read (ctx,pos),q.1.1.2)

theorem field_poly (hr : Poly read) (incoming : Bool) : Poly (field read incoming) := by
  have ctx : Poly (fun q : FieldQuery A => q.1.1.1.1) := by fun_prop
  have head : Poly (fun q : FieldQuery A => q.1.1.1.2) := by fun_prop
  have cap : Poly (fun q : FieldQuery A => q.1.1.2) := by fun_prop
  have site : Poly (fun q : FieldQuery A => q.1.2) := by fun_prop
  have fetch (j : ℕ) := (ctx.pair ((head.pair (Code.Poly.const (tally j))).compose address_poly)).compose hr
  have row (base : FieldQuery A → Bits.Word) (hb : Poly base) :=
    ((((hb.pair (fetch 16)).pair site).compose start_poly).pair Easy.snd.poly).compose address_poly
  cases incoming with
  | false => exact (((ctx.pair (row _ (fetch 20))).compose hr).pair cap).compose capped_poly
  | true =>
    have inv := (ctx.pair (row _ (fetch 19))).compose hr
    have ptr := (((fetch 20).pair inv).pair (Code.Poly.const (tally 1))).compose start_poly
    exact (((ctx.pair ptr).compose hr).pair cap).compose capped_poly

variable {w a g : ℕ} (X : State a g) (T : IncidenceDirectory w) (ctx : A) (m : Memory w)
  (rd : ∀ h : Word w, read (ctx,wordBits h)=wordBits (m h.val))

include rd
omit [Codec A] in
theorem field_eq (head : Word w) (cap : ℕ)
    (deg : m (head+16).val=((2^a : ℕ) : Word w)) (inv : m (head+19).val=T.actualIn)
    (wid : m (head+20).val=T.width) (cols : T.ActualColumns X m)
    (allow : X.maxWireWidth ≤ cap) (fit : X.maxWireWidth < 2^w)
    (v : X.network.Site) (d : Bool) (j : Fin (2^a)) :
    field read d ((((ctx,wordBits head),tally cap),tally ((siteOrder X).entries.symm v).val),tally j.val) =
      tally (X.halfWidth v d j) := by
  let p := IncidenceDirectory.actualPort (w:=w) X (v,j)
  have idx : ((((siteOrder X).entries.symm v).val : Word w)*((2^a : ℕ) : Word w)+(j.val : Word w)) = p := by
    rw [show p = _ from TerminalPrefix.actualPort_eq X (v,j)]
    change _ = ((j.val+2^a*((siteOrder X).entries.symm v).val : ℕ) : Word w)
    push_cast
    ring
  have row (base : Word w) : base + (((siteOrder X).entries.symm v).val : Word w)*((2^a : ℕ) : Word w)+(j.val : Word w) = base+p := by rw [add_assoc,idx]
  have out : m (T.width+p).val = CursorRAM.encode w (X.halfWidth v false j) := cols.width (v,j)
  have inside := cols.width (X.slots.actualGraph.target.symm (v,j))
  have bounds := X.halfWidth_le_max v d j
  cases d with
  | false =>
    simp only [field,Bool.cond_false,address_eq,rd,Nat.cast_ofNat,deg,wid,start_eq,row,out,capped,value_native,tally_length]
    change tally (min ((X.halfWidth v false j) % 2^w) cap) = _
    rw [Nat.mod_eq_of_lt (bounds.trans_lt fit),Nat.min_eq_left (bounds.trans allow)]
  | true =>
    have back : m (T.actualIn+p).val = IncidenceDirectory.actualPort X (X.slots.actualGraph.target.symm (v,j)) := cols.actualIn _
    simp only [field,Bool.cond_true,address_eq,rd,Nat.cast_ofNat,Nat.cast_one,deg,inv,wid,start_eq,row,back,one_mul,inside,capped,value_native,tally_length]
    change tally (min ((X.halfWidth v true j) % 2^w) cap) = _
    rw [Nat.mod_eq_of_lt (bounds.trans_lt fit),Nat.min_eq_left (bounds.trans allow)]

end
end OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan

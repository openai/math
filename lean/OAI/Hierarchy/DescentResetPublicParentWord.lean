import OAI.Hierarchy.DescentResetParentCodec
import OAI.Hierarchy.DescentIssuedGoodHeaders

namespace OAI
/-! # Physical ordinal words for trunk and direct reset parents -/
namespace Hierarchy.DescentResetPublicParentWord
open DescentResetParentCodec DescentResetCompactParent DescentHostDirectory DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open DescentPackedZip DescentSharedCableNames
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Shape where
  halo : ℕ
  depth : ℕ
  ports : ℕ
  span : ℕ
  cap : ℕ
  sockets : ℕ
  program : ℕ

def Shape.count (s : Shape) :=capCount s.halo s.depth s.ports s.span s.cap s.sockets s.program
abbrev Site (s : Shape) := SiteWord s.halo s.depth s.ports
abbrev Parent (s : Shape) := DescentResetCompactParent.Word s.halo s.depth s.ports s.span s.cap s.sockets s.program

/-- Numerical fields of a measured old root. The receiver-relative host,
residual dyadic depth/index and optional port are all short integers. -/
def rootFields {s : Shape} : Site s→Fin 5→ℕ
  | .inl (h,l)=>![h.val,0,l.val.1,l.val.2,0]
  | .inr (h,l,p)=>![h.val,1,l.val.1,l.val.2,p.val]

def decode (s : Shape) (v : Fin 5→ℕ) : Option (Site s) :=
  if host : v 0< s.halo then
    if legal : (v 2,v 3)∈codes s.depth then
      let h : Fin s.halo:=⟨v 0,host⟩
      let l : Label s.depth:=⟨(v 2,v 3),legal⟩
      if v 1=0 then some (.inl (h,l))
      else if port : v 4< s.ports+1 then some (.inr (h,l,⟨v 4,port⟩)) else none
    else none
  else none

theorem decoded (s : Shape) (a : Site s) : decode s (rootFields a)=some a:=by
  rcases a with ⟨h,q⟩ | ⟨h,q,p⟩
  · simp [decode, rootFields, h.isLt, q.property]
  · simp [decode, rootFields, h.isLt, q.property, Nat.le_of_lt_succ p.isLt]

def parent (s : Shape) (a : Site s) (socket : Option (Fin s.sockets)) : Parent s :=
  socket.elim (.inr (.inl a)) (fun j=>.inr (.inr (.inl (a,j))))

def «fields» (live zero : Bool) {s : Shape} (a : Site s) (socket : ℕ) : Fin 8→ℕ :=
  ![live.toNat,zero.toNat,rootFields a 0,rootFields a 1,rootFields a 2,rootFields a 3,rootFields a 4,socket]

def emit (s : Shape) (direct : Bool) (v : Fin 8→ℕ) : ℕ :=
  if v 0=0 then 0 else
    match decode s (![v 2,v 3,v 4,v 5,v 6]) with
    | none=>0
    | some a=>
      if direct then
        if bound : v 7< s.sockets then number (decide (v 1≠0)) (parent s a (some ⟨v 7,bound⟩)) else 0
      else number (decide (v 1≠0)) (parent s a none)

theorem emitted (s : Shape) (zero : Bool) (a : Site s) (socket : Option (Fin s.sockets)) :
    emit s socket.isSome («fields» true zero a (socket.elim 0 Fin.val))=number zero (parent s a socket):=by
  have unpack : (![rootFields a 0,rootFields a 1,rootFields a 2,rootFields a 3,rootFields a 4] : Fin 5→ℕ)=rootFields a:=by funext j;fin_cases j <;> rfl
  cases zero <;> cases socket with
  | none=>simp [emit,«fields»,unpack,decoded]
  | some j=>simp [emit,«fields»,unpack,decoded,j.isLt]

def render {b : ℕ} (s : Shape) (direct : Bool) (v : Fin 8→Cell b) : Cell (Packed.bits s.count) :=
  emit s direct (fun i=>(v i).val)

theorem render_live {b : ℕ} (s : Shape) (z : Bool) (a : Site s) (j : Option (Fin s.sockets))
    (v : Fin 8→Cell b) (row : ∀i,(v i).val=«fields» true z a (j.elim 0 Fin.val) i) :
    (render s j.isSome v).val=number z (parent s a j):=by
  unfold render
  rw [funext row,emitted]
  apply Fin.val_cast_of_lt
  exact (number_lt z (parent s a j)).trans_le ((Nat.le_succ s.count).trans (Nat.le_pow_clog (by decide) (s.count+1)))

theorem render_empty {b : ℕ} (s : Shape) (direct : Bool) (v : Fin 8→Cell b) (absent : (v 0).val=0) :
    render s direct v=0:=by simp [render,emit,absent]

variable {H G M w field : ℕ}

/-- The two scans assemble the actual preceding columns and execute the one
fixed dictionary for every packed group with zeroed tail lanes. -/
theorem issue (s : Shape) (direct : Bool) (tables : Fin 8→Tables) (reads : Fin 8→Expr)
    (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank) (x : Fin H→Fin G→Fin 8→Cell field)
    (pos : 0<M) (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*8) (Packed.bits s.count) M H G w out.base)
    (rom : resident (render s direct ∘ (encode field 8).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*8)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>render s direct (x a g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr :=by
  obtain ⟨run,whole,_,frame⟩:=gathered_words (render s direct) tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentResetPublicParentWord

end OAI

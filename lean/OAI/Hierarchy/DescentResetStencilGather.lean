import OAI.Hierarchy.DescentResetPackedStencil
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedPayloadBudget

namespace OAI
/-! # Gathering the reset source fields and executing the leaf lookup at a common lane pitch -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPacking.PackedMatch.Local ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {r q n t H G M w : ℕ}

def slotName (r q : ℕ) := (Fintype.equivFin (Slot r q)).symm
def assembly (T : Fin (count r q)→Tables) (field : Slot r q→Expr) :=
  Gather.assembly T (fun i=>field (slotName r q i))

theorem fields_at (T : Fin (count r q)→Tables) (field : Slot r q→Expr) (base : ℕ) (m : Memory w)
    (bounds : Gather.Bounds (w:=w) (d:=n) (M:=M) T (fun i=>field (slotName r q i)) base)
    (rom : ∀i,Static (T i) (Gather.setField (d:=n) i) M m)
    (values : Fin H→Fin G→panel r q n) (read : ∀s,Source (field s) (fun v g=>values v g s) M m) :
    Source (assembly T field) (fun v g=>pack r q n (values v g)) M m := by
  have done:=Gather.collected T (fun i=>field (slotName r q i)) base bounds m rom
    (fun v g i=>values v g (slotName r q i)) (fun i=>read _) (List.finRange (count r q))
  change Source (Gather.collect T (fun i => field (slotName r q i)) (List.finRange (count r q)))
    (fun v g => encode n (count r q) (fun i => values v g (slotName r q i))) M m
  simpa only [List.mem_finRange,ite_true] using done

def execute (T : Fin (count r q)→Tables) (field : Slot r q→Expr) (g : Banks) (out H G M w : ℕ) :=
  (scan w g.source.base (H*chunks G M) (assembly T field)).seq (DescentSIMDLookup.program g out H G M w)

def cost (T : Fin (count r q)→Tables) (field : Slot r q→Expr) (H G M : ℕ) :=
  (4+H*chunks G M*(2*(assembly T field).work+4))+(4+44*(H*chunks G M))

theorem returned_words (r q n t f B Y : ℕ) (T : Fin (count r q)→Tables) (field : Slot r q→Expr)
    (g : Banks) (out : ℕ) (m : Memory w) (values : Fin H→Fin G→panel r q n) (pos : 0<M)
    (fit : DescentSIMDLookup.Fits g (n*count r q) (t*2^r) M H G w out)
    (bounds : Gather.Bounds (w:=w) (d:=n) (M:=M) T (fun i=>field (slotName r q i)) g.source.base)
    (room : g.source.base+H*chunks G M<2^w)
    (tabs : ∀i,Static (T i) (Gather.setField (d:=n) i) M m)
    (read : ∀s,Source (field s) (fun v h=>values v h s) M m)
    (rom : resident (lookup r q n t f B Y) g H G M m)
    (belowDict : g.dictionary.base+g.dictionary.size≤g.source.base)
    (belowMask : g.mask.base+g.mask.size≤g.source.base) :
    ∃dst,(execute T field g out H G M w).Exec m dst (cost T field H G M) ∧
      (∀v j (x : DescentColonies.Block r),digit t x.val (digit (t*2^r) (lane j pos).val
        (dst (out+(DescentSIMDLookup.row H G M (position v j pos)).val)).val)=((word (values v j) f B Y x:ℕ):Cell t).val) ∧
      (∀z<g.source.base,dst z=m z) ∧ (∀z,out+H*chunks G M≤z→dst z=m z) ∧
      ∀i : Row H G M,dst (out+(DescentSIMDLookup.row H G M i).val)=
        ((data (fun v j=>encode t (2^r) (fun x=>(word (values v j) f B Y x:Cell t))) i).val:Word w) := by
  let term:=assembly T field
  let mid:=image g.source.base (H*chunks G M) term m
  have run : (scan w g.source.base (H*chunks G M) term).Exec m mid
      (4+H*chunks G M*(2*term.work+4)) := by
    intro labels regs slots machine
    exact scan_exec g.source.base (H*chunks G M) term m
      (Gather.fits T _ g.source.base bounds (List.finRange _)) room machine
  have input:=fields_at T field g.source.base m bounds tabs values read
  have got (u : Row H G M) : mid (g.source.base+(DescentSIMDLookup.row H G M u).val)=
      ((data (fun v j=>pack r q n (values v j)) u).val:Word w):=
    (ProtocolRAMGeneratedWrite.read_image g.source.base (H*chunks G M) term m (DescentSIMDLookup.row H G M u)).trans (input u)
  have retained (z) (lo : z<g.source.base ∨ g.source.base+H*chunks G M≤z) : mid z=m z :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ lo
  have live : resident (lookup r q n t f B Y) g H G M mid := by
    constructor
    · intro i
      have lt : i.val<g.dictionary.size:=by simp [Bank.size,fit.dictBits]
      exact (retained _ (.inl ((Nat.add_lt_add_left lt _).trans_le belowDict))).trans (rom.1 i)
    · intro i
      have bound:=i.isLt.trans_le fit.maskSize
      exact (retained _ (.inl ((Nat.add_lt_add_left bound _).trans_le belowMask))).trans (rom.2 i)
  obtain ⟨second,words,lower,upper,allWords⟩:=compiled_words r q n t f B Y g out pos fit mid values live got
  have endBelow : g.source.base+H*chunks G M≤out:=(Nat.add_le_add_left fit.srcSize _).trans fit.source.2.2
  refine ⟨imageBank H G M out g mid,?_,words,?_,?_,allWords⟩
  · intro labels regs slots machine
    exact Procedure.Exec.then run second machine
  · intro z before
    exact (lower z (by omega)).trans (retained z (.inl before))
  · intro z after
    exact (upper z after).trans (retained z (.inr (by omega)))

theorem returned (r q n t f B Y : ℕ) (T : Fin (count r q)→Tables) (field : Slot r q→Expr)
    (g : Banks) (out : ℕ) (m : Memory w) (values : Fin H→Fin G→panel r q n) (pos : 0<M)
    (fit : DescentSIMDLookup.Fits g (n*count r q) (t*2^r) M H G w out)
    (bounds : Gather.Bounds (w:=w) (d:=n) (M:=M) T (fun i=>field (slotName r q i)) g.source.base)
    (room : g.source.base+H*chunks G M<2^w)
    (tabs : ∀i,Static (T i) (Gather.setField (d:=n) i) M m)
    (read : ∀s,Source (field s) (fun v h=>values v h s) M m)
    (rom : resident (lookup r q n t f B Y) g H G M m)
    (belowDict : g.dictionary.base+g.dictionary.size≤g.source.base)
    (belowMask : g.mask.base+g.mask.size≤g.source.base) :
    ∃dst,(execute T field g out H G M w).Exec m dst (cost T field H G M) ∧
      (∀v j (x : DescentColonies.Block r),digit t x.val (digit (t*2^r) (lane j pos).val
        (dst (out+(DescentSIMDLookup.row H G M (position v j pos)).val)).val)=((word (values v j) f B Y x:ℕ):Cell t).val) ∧
      (∀z<g.source.base,dst z=m z) ∧ ∀z,out+H*chunks G M≤z→dst z=m z := by
  obtain ⟨dst,exe,rd,lo,hi,_⟩:=returned_words r q n t f B Y T field g out m values pos fit bounds room tabs read rom belowDict belowMask
  exact ⟨dst,exe,rd,lo,hi⟩

theorem assembly_work (T : Fin (count r q)→Tables) (field : Slot r q→Expr) (L : ℕ)
    (bound : ∀s,(field s).work≤L) : (assembly T field).work≤1+count r q*(L+11) := by
  have walk (is : List (Fin (count r q))) :
      (Gather.collect T (fun i=>field (slotName r q i)) is).work≤1+is.length*(L+11) := by
    induction is with
    | nil=>simp [Gather.collect,Expr.work]
    | cons i is ih=>
      have cost:=bound (slotName r q i)
      simp only [Gather.collect,Tables.read,Expr.work,List.length_cons,Nat.add_mul,Nat.one_mul] at *
      omega
  simpa only [assembly,Gather.assembly,List.length_finRange] using walk (List.finRange _)

theorem bit_price (T : Fin (count r q)→Tables) (field : Slot r q→Expr)
    (h w K H G shared L : ℕ) (positive : 0<shared) (wide : 2*shared≤h) (hardware : w≤K*h)
    (bound : ∀s,(field s).work≤L) :
    cost T field H G (lanes h shared)*w≤K*((60+2*count r q*(L+11))*(h+H*h+4*H*G*shared)) := by
  let N:=H*chunks G (lanes h shared)
  let A:=h+H*h+4*H*G*shared
  have hn : N*h≤A:=(volume H G h shared positive wide).trans (by dsimp [A];omega)
  have hh : h≤A:=by dsimp [A];omega
  have fields:=assembly_work T field L bound
  apply DescentPackedPayloadBudget.clock hardware
  change ((4+N*(2*(assembly T field).work+4))+(4+44*N))*h≤_
  calc
    _=8*h+N*h*(2*(assembly T field).work+48):=by ring
    _≤8*A+A*(2*(1+count r q*(L+11))+48):=by gcongr
    _≤(60+2*count r q*(L+11))*A:=by nlinarith only [Nat.zero_le A]

end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil

end OAI

import OAI.Hierarchy.DescentResetMixedWordROM

namespace OAI
/-! # The reset parent word scanner after mounting its shared literal pages -/
namespace Hierarchy.DescentResetMixedWordRAM.Book
open DescentPackedZip DescentSIMDLookup DescentOrdinaryAtomFieldRAM.ROM DescentResetFieldAssembler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {b z u t o M H G w : ℕ}
def program (b z u t o M H G w base out : ℕ) (f : ℕ→ℕ→ℕ→ℕ→ℕ) («meta» zero halo arg : Expr) :=
  let pieces:=pages b z u t o M f
  let op:=operation (chart b z u t o M base f) «meta» zero halo arg
  (mount pieces (unit b z u t*M) w base).seq (scan w out (H*chunks G M) op)

def ticks (b z u t M H G : ℕ) («meta» zero halo arg : Expr) :=
  4+10*(6*2^(unit b z u t*M))+(4+H*chunks G M*(2*(«meta».work+zero.work+halo.work+arg.work+33)+4))

private theorem ticks_eq (C : Charts) (b z u t M H G : ℕ) («meta» zero halo arg : Expr) :
    ticks b z u t M H G «meta» zero halo arg =
      (4+10*(6*2^(unit b z u t*M))) +
        (4+H*chunks G M*(2*(operation C «meta» zero halo arg).work+4)) := by
  rw [ticks, work]

theorem from_old (fn : ℕ→ℕ→ℕ→ℕ→ℕ) (absent : fn 0 0 0 0=0)
    («meta» zero halo arg : Expr) (out : Bank) (base end_ : ℕ) (m : Memory w)
    (src : Fin H→Fin G→Meta) (test : Fin H→Fin G→Bool) (rank : Fin H→Fin G→Cell u) (operand : Fin H→Fin G→Cell t)
    (liveWidth : 0<b) (zeroWidth : 0<z)
    (ms : Source «meta» (fun h g=>raw b (src h g)) M m) (zs : Source zero (fun h g=>((test h g).toNat:Cell z)) M m)
    (hs : Source halo rank M m) (ds : Source arg operand M m)
    (metaFit : «meta».Fits w base) (zeroFit : zero.Fits w base) (haloFit : halo.Fits w base) (argFit : arg.Fits w base)
    (apart : base+6*2^(unit b z u t*M)≤out.base) (room : out.Fits w end_) (extent : H*chunks G M≤out.size)
    (space : out.base+H*chunks G M<2^w) :
    let doneROM:=after (pages b z u t o M fn) (unit b z u t*M) base m
    let op:=operation (chart b z u t o M base fn) «meta» zero halo arg
    let n:=H*chunks G M
    let dst:=image out.base n op doneROM
    let cpu:=program b z u t o M H G w base out.base fn «meta» zero halo arg
    cpu.Exec m dst (ticks b z u t M H G «meta» zero halo arg) ∧
      Source (.lookup out .row) (fun h g=>(fn (src h g).live.toNat (test h g).toNat (rank h g).val (operand h g).val:Cell o)) M dst ∧
      (∀p : Row H G M,dst (out.base+(row H G M p).val)=((data (fun h g=>(fn (src h g).live.toNat (test h g).toNat (rank h g).val (operand h g).val:Cell o)) p).val:Word w)) ∧
      (∀j,j<base ∨ out.base+n≤j→dst j=m j) ∧ CheapCode cpu ∧
      DescentStaticWordColumn.names cpu=15*(6*2^(unit b z u t*M)+1)+(11+4*(«meta».work+zero.work+halo.work+arg.work+33)):=by
  intro doneROM op n dst cpu
  have below : out.base<2^w := (Nat.le_add_right out.base (H*chunks G M)).trans_lt space
  have early : base≤out.base:=(Nat.le_add_right ..).trans apart
  obtain ⟨init,fixed₁,fixed₂,fixed₃,mem₀,cheap₀,_⟩:=setup (b:=b) (z:=z) (u:=u) (t:=t) (o:=o) (M:=M) fn base m (apart.trans_lt below)
  have preserve {a : ℕ} (e : Expr) (x : Fin H→Fin G→Cell a) (fits : e.Fits w base) (prev : Source e x M m) : Source e x M doneROM:=by
    intro p
    exact (ProtocolRAM.eval_below e _ m doneROM fits (fun j l=>mem₀ j (.inl l))).trans (prev p)
  obtain ⟨k₁,k₂,k₃⟩:=gates (b:=b) (z:=z) (u:=u) (t:=t) (o:=o) (M:=M) fn base out.base apart below «meta» zero halo arg
    (ProtocolRAMGeneratedWrite.fits_mono _ early metaFit) (ProtocolRAMGeneratedWrite.fits_mono _ early zeroFit)
    (ProtocolRAMGeneratedWrite.fits_mono _ early haloFit) (ProtocolRAMGeneratedWrite.fits_mono _ early argFit)
  obtain ⟨scan_,read,full,frame'⟩:=DescentResetMixedWordRAM.run (b:=b) (z:=z) (u:=u) (t:=t) (o:=o) (M:=M)
    (H:=H) (G:=G) (chart b z u t o M base fn) «meta» zero halo arg out doneROM fn absent
    src test rank operand liveWidth zeroWidth (preserve _ _ metaFit ms) (preserve _ _ zeroFit zs)
    (preserve _ _ haloFit hs) (preserve _ _ argFit ds) k₁ k₂ k₃ fixed₁ fixed₂ fixed₃ end_ room extent space
  refine ⟨?_,read,full,?_,@ProtocolRAM.cheap_seq w (mount (pages b z u t o M fn) (unit b z u t*M) w base)
    (scan w out.base n op) (@cheap₀) (@ProtocolRAM.scan_cheap w out.base n op),
    hardware (b:=b) (z:=z) (u:=u) (t:=t) (o:=o) (M:=M) (w:=w) fn base (chart b z u t o M base fn)
      «meta» zero halo arg out.base n⟩
  · rw [ticks_eq (chart b z u t o M base fn)]
    exact @Procedure.Exec.then w (mount (pages b z u t o M fn) (unit b z u t*M) w base)
      (scan w out.base n op) m doneROM dst _ _ (@init) (@scan_)
  · intro j outside
    rcases outside with lo | hi
    · exact (frame' j (.inl (lo.trans_le early))).trans (mem₀ j (.inl lo))
    · exact (frame' j (.inr hi)).trans (mem₀ j (.inr (apart.trans ((Nat.le_add_right out.base n).trans hi))))

/-- The fixed original hardware always stops on its public clock, including
when a branch supplied an unparseable, absent, or oversize logical header. -/
theorem any_framed (fn : ℕ→ℕ→ℕ→ℕ→ℕ) («meta» zero halo arg : Expr) (m : Memory w) (base out : ℕ)
    (metaFit : «meta».Fits w base) (zeroFit : zero.Fits w base) (haloFit : halo.Fits w base) (argFit : arg.Fits w base)
    (apart : base+6*2^(unit b z u t*M)≤out) (space : out+H*chunks G M<2^w) :
    ∃dst,(program b z u t o M H G w base out fn «meta» zero halo arg).Exec m dst (ticks b z u t M H G «meta» zero halo arg) ∧
      CheapCode (program b z u t o M H G w base out fn «meta» zero halo arg) ∧
      ∀j,(j<base ∨ base+6*2^(unit b z u t*M)≤j)→(j<out ∨ out+H*chunks G M≤j)→dst j=m j:=by
  let P:=pages b z u t o M fn
  let width:=unit b z u t*M
  let C:=chart b z u t o M base fn
  let stage:=after P width base m
  let op:=operation C «meta» zero halo arg
  let N:=H*chunks G M
  have below : out<2^w:=(Nat.le_add_right ..).trans_lt space
  have early : base≤out:=(Nat.le_add_right ..).trans apart
  obtain ⟨installed, _⟩ := DescentOrdinaryAtomFieldRAM.ROM.run P width base m (apart.trans_lt below)
  obtain ⟨_,_,last⟩:=gates (b:=b) (z:=z) (u:=u) (t:=t) (o:=o) (M:=M) fn base out apart below «meta» zero halo arg
    (ProtocolRAMGeneratedWrite.fits_mono _ early metaFit) (ProtocolRAMGeneratedWrite.fits_mono _ early zeroFit)
    (ProtocolRAMGeneratedWrite.fits_mono _ early haloFit) (ProtocolRAMGeneratedWrite.fits_mono _ early argFit)
  have safe : op.Fits w out := ⟨last.apply, last.right, last.shift, last.left⟩
  refine ⟨image out N op stage, ?_, @ProtocolRAM.cheap_seq w (mount P width w base) (scan w out N op)
    (@DescentOrdinaryAtomFieldRAM.ROM.cheap 6 P width w base) (@ProtocolRAM.scan_cheap w out N op), ?_⟩
  · rw [ticks_eq C]
    exact @Procedure.Exec.then w (mount P width w base) (scan w out N op)
      m stage (image out N op stage) _ _ (@installed) (@scan_exec w out N op stage safe space)
  · intro j old new_
    exact (ProtocolRAMGeneratedWrite.frame_image out N op stage j new_).trans (frame P width base m j old)

theorem any (fn : ℕ→ℕ→ℕ→ℕ→ℕ) («meta» zero halo arg : Expr) (m : Memory w) (base out : ℕ)
    (metaFit : «meta».Fits w base) (zeroFit : zero.Fits w base) (haloFit : halo.Fits w base) (argFit : arg.Fits w base)
    (apart : base+6*2^(unit b z u t*M)≤out) (space : out+H*chunks G M<2^w) :
    ∃dst,(program b z u t o M H G w base out fn «meta» zero halo arg).Exec m dst (ticks b z u t M H G «meta» zero halo arg):=by
  obtain ⟨dst,exec,_,_⟩:=any_framed (b:=b) (z:=z) (u:=u) (t:=t) (o:=o) (M:=M) (H:=H) (G:=G) fn «meta» zero halo arg m base out metaFit zeroFit haloFit argFit apart space
  exact ⟨dst,exec⟩

theorem rom_room (w b z u t o : ℕ) :
    6*2^(unit b z u t*lanes w (max (unit b z u t) o))≤6*2^(w/2):=
  Nat.mul_le_mul_left 6 (rom_entries (unit b z u t) o w)

end
end Hierarchy.DescentResetMixedWordRAM.Book

end OAI

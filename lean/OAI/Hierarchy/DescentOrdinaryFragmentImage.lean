import OAI.Hierarchy.DescentNativeLocalFragment
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! Exact two-sided memory frame of allocating the successor operand resolver. -/
namespace Hierarchy.DescentPackedOperand.ROM
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section

def endAddress (base k H G M : ℕ):=maskBase base k M+3*rows H G M
def result (base k H G M : ℕ) (banks : Fin 10→Bank) {w : ℕ} (m : Memory w):=
  finished (chart base k H G M banks) (output base k H G M) H G M (mounted base k H G M m)

theorem result_frame (base k H G M : ℕ) (banks : Fin 10→Bank) {w : ℕ} (m : Memory w) (a : ℕ)
    (apart : a<base ∨ endAddress base k H G M≤a) : result base k H G M banks m a=m a :=by
  let L:=chart base k H G M banks
  let R:=rows H G M
  let P:=page k M
  let N:=H*chunks G M
  have bound : N≤R:=(row_bounds H G M).1
  change a<base ∨ base+12*P+3*R≤a at apart
  have left : a<L.remap.source.base ∨ L.remap.source.base+H*chunks G M≤a:=by
    change a<base+12*P+R ∨ base+12*P+R+N≤a
    omega
  have right : a<output base k H G M ∨ output base k H G M+H*chunks G M≤a:=by
    change a<base+12*P+2*R ∨ base+12*P+2*R+N≤a
    omega
  have fixed : mounted base k H G M m a=m a:=by
    apply DescentStaticWordColumn.frame
    change a<base ∨ base+(12*P+N)≤a
    omega
  exact (finished_frame L (output base k H G M) H G M (mounted base k H G M m) a left right).trans fixed

private theorem literal_scans_cheap (w base length : ℕ) (tape : ℕ → ℕ) (src out n : ℕ) (left right : Expr) :
    CheapCode ((DescentStaticWordColumn.program w base tape length).seq
      ((scan w src n left).seq (scan w out n right))) := by
  have pair : CheapCode ((scan w src n left).seq (scan w out n right)) :=
    @cheap_seq w (scan w src n left) (scan w out n right) (@scan_cheap w src n left) (@scan_cheap w out n right)
  exact @cheap_seq w (DescentStaticWordColumn.program w base tape length)
    ((scan w src n left).seq (scan w out n right)) (@DescentStaticWordColumn.cheap w base tape length) @pair

theorem fixed_cheap (base k H G M w : ℕ) (banks : Fin 10→Bank) : CheapCode (run base k H G M w banks) := by
  let L := chart base k H G M banks
  let n := H*chunks G M
  unfold run routed mount prepare DescentSIMDLookup.program
  intro P R K
  exact @literal_scans_cheap w base (12*page k M+n) (contents k H G M)
    L.remap.source.base (output base k H G M) n (panel L) (lookup L.remap) P R K

theorem any (base k H G M w : ℕ) (banks : Fin 10→Bank) (m : Memory w)
    (up : ∀i,(banks i).Fits w base) (cap : ∀i,H*chunks G M≤(banks i).size)
    (word : M*unit k≤w/2) (space : endAddress base k H G M<2^w) :
    (run base k H G M w banks).Exec m (result base k H G M banks m) (12+120*page k M+420*(H*chunks G M)) ∧
    (∀a,a<base ∨ endAddress base k H G M≤a → result base k H G M banks m a=m a) ∧
    CheapCode (run base k H G M w banks) :=by
  let L:=chart base k H G M banks
  let boot:=mounted base k H G M m
  let n:=H*chunks G M
  have valid : Room L k H G M w (output base k H G M) := room base k H G M w banks up cap word space
  have bound:= (row_bounds H G M).1
  change base+12*page k M+3*rows H G M<2^w at space
  have first : (mount base k H G M w).Exec m boot (4+10*(12*page k M+n)) :=
    DescentStaticWordColumn.mount base (12*page k M+n) (contents k H G M) m (by dsimp only [n]; omega)
  have second : (prepare L H G M w).Exec boot (prepared L H G M boot) (4+n*(2*(panel L).work+4)) :=
    scan_exec L.remap.source.base n (panel L) boot
      (DescentPacking.PackedMatch.Local.Gather.fits L.joins (source L) L.remap.source.base valid.join (List.finRange 10))
      (by change base+12*page k M+rows H G M+H*chunks G M<2^w; omega)
  have lastFit : (lookup L.remap).Fits w (output base k H G M) := by
    simp [lookup, Expr.Fits, valid.route.source, valid.route.dictionary, valid.route.mask]
  have third : (DescentSIMDLookup.program L.remap (output base k H G M) H G M w).Exec
      (prepared L H G M boot) (result base k H G M banks m) (4+n*(2*(lookup L.remap).work+4)) :=
    scan_exec (output base k H G M) n (lookup L.remap) (prepared L H G M boot) lastFit valid.route.output
  have ticks : 12+120*page k M+420*n=(4+10*(12*page k M+n))+
      ((4+n*(2*(panel L).work+4))+(4+n*(2*(lookup L.remap).work+4))) :=by
    rw [panel_work,lookup_work];omega
  refine ⟨?_,result_frame base k H G M banks m,fixed_cheap base k H G M w banks⟩
  change (run base k H G M w banks).Exec m (result base k H G M banks m) (12+120*page k M+420*n)
  rw [ticks];exact Procedure.Exec.then first (Procedure.Exec.then second third)

theorem execute_framed (base k H G M w : ℕ) (banks : Fin 10→Bank) (x : Fin H→Fin G→Fragment k)
    (up : ∀i,(banks i).Fits w base) (cap : ∀i,H*chunks G M≤(banks i).size)
    (word : M*unit k≤w/2) (positive : 0<M) (space : endAddress base k H G M<2^w) (m : Memory w)
    (src : ∀i (p : Row H G M),m ((banks i).base+(row H G M p).val)=((data (fun h g=>sourceFields (x h g) i) p).val : Word w)) :
    let done:=result base k H G M banks m
    (run base k H G M w banks).Exec m done (12+120*page k M+420*(H*chunks G M)) ∧
    (∀h g (f : Fin 5),digit (k+4) f.val (digit (outputWidth k) (lane g positive).val
      (done (output base k H G M+(row H G M (position h g positive)).val)).val)=(resolve (x h g)).fields f) ∧
    (∀a,a<base ∨ endAddress base k H G M≤a→done a=m a) ∧ CheapCode (run base k H G M w banks) :=by
  intro done
  obtain ⟨_, stored⟩ := installed base k H G M w banks x up cap m src space
  have fits := room base k H G M w banks up cap word space
  obtain ⟨exec, frame, cheap⟩ := any base k H G M w banks m up cap word space
  exact ⟨exec, finished_read (chart base k H G M banks) (output base k H G M) fits x
    (mounted base k H G M m) stored positive, frame, cheap⟩

end
end Hierarchy.DescentPackedOperand.ROM

namespace Hierarchy.DescentOrdinaryLocalFragment
open DescentPackedOperand DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {k H G M w : ℕ}

def endAddress (base k H G M : ℕ):=ROM.endAddress (finish base k M (H*chunks G M)) k H G M
def outputMemory (base k H G M : ℕ) (banks : Fin 10→Bank) (peer old role : Expr) (m : Memory w):=
  let n:=H*chunks G M
  ROM.result (finish base k M n) k H G M (fields base k M n banks) (memory base k M n banks peer old role m)
def hardware (base k H G M w : ℕ) (banks : Fin 10→Bank) (peer old role : Expr):=
  let n:=H*chunks G M
  (program base k M n w banks peer old role).seq (ROM.run (finish base k M n) k H G M w (fields base k M n banks))
def time (base k H G M : ℕ) (banks : Fin 10→Bank) (peer old role : Expr):=
  let n:=H*chunks G M
  cost base k M n banks peer old role+(12+120*ROM.page k M+420*n)

set_option maxHeartbeats 600000 in
theorem cheap (base k H G M w : ℕ) (banks : Fin 10→Bank) (peer old role : Expr) :
    CheapCode (hardware base k H G M w banks peer old role) := by
  let n := H*chunks G M
  let head := finish base k M n
  exact @cheap_seq w (program base k M n w banks peer old role)
    (ROM.run head k H G M w (fields base k M n banks))
    (@cheap_seq w (DescentOrdinaryAtomFieldRAM.ROM.mount (pages (k+2) M) (width (k+2) M) w base)
      (ProtocolRAM.program w (sweep base k M n banks peer old role))
      (@DescentOrdinaryAtomFieldRAM.ROM.cheap 4 (pages (k+2) M) (width (k+2) M) w base)
      (@ProtocolRAM.program_cheap w (sweep base k M n banks peer old role)))
    (@ROM.fixed_cheap head k H G M w (fields base k M n banks))

theorem end_formula (base k H G M : ℕ) :
    endAddress base k H G M=base+4*2^(width (k+2) M)+2*DescentDyadicSpan.span (H*chunks G M)
      +12*ROM.page k M+3*ROM.rows H G M :=rfl

theorem names_bound (base k H G M w : ℕ) (banks : Fin 10→Bank) (peer old role : Expr) :
    let n:=H*chunks G M
    DescentStaticWordColumn.names (hardware base k H G M w banks peer old role)≤
      15*(4*2^(width (k+2) M)+1)+15+2*(11+4*maxField peer old role)+(841+15*(12*ROM.page k M+n)) :=by
  intro n
  rw [hardware,DescentStaticWordColumn.names_seq]
  exact Nat.add_le_add (text_bound base banks peer old role _)
    (ROM.control (finish base k M n) k H G M w (fields base k M n banks)).le

theorem time_bound (base k H G M : ℕ) (banks : Fin 10→Bank) (peer old role : Expr) :
    let n:=H*chunks G M
    time base k H G M banks peer old role≤4+40*2^(width (k+2) M)+(4+2*(4+n*(2*maxField peer old role+4)))+
      (12+120*ROM.page k M+420*n) :=by
  intro n
  exact Nat.add_le_add_right (clock_bound base banks peer old role n) _

set_option maxHeartbeats 600000 in
private theorem initial_any (base k H G M w : ℕ) (banks : Fin 10→Bank) (peer old role : Expr) (m : Memory w)
    (bankFit : ∀i,(banks i).Fits w base) (peerFit : peer.Fits w base) (oldFit : old.Fits w base) (roleFit : role.Fits w base)
    (space : finish base k M (H*chunks G M)<2^w) :
    let n:=H*chunks G M
    (program base k M n w banks peer old role).Exec m (memory base k M n banks peer old role m) (cost base k M n banks peer old role) ∧
    (∀a,a<base ∨ finish base k M n≤a→memory base k M n banks peer old role m a=m a) ∧
    CheapCode (program base k M n w banks peer old role) :=by
  intro n
  let a:=k+2
  let start:=specEnd base a M
  let pages_:=pages a M
  let loaded:=DescentOrdinaryAtomFieldRAM.ROM.after pages_ (width a M) base m
  let e:=fun i:ℕ=>expression a M base (input banks) peer old role (i:Fin 2)
  have sep : base≤ start:=Nat.le_add_right ..
  have upper : start≤finish base k M n:=Nat.le_add_right ..
  have room:=upper.trans_lt space
  have ready (i:ℕ) (_:i<2) : (e i).Fits w start:=by
    let j:Fin 2:=i
    let B:=tables a M base
    have raw (i:Fin 10) : (input banks i).Fits w base:=⟨bankFit i,trivial⟩
    have newFit : (rhs peer old role j).Fits w base:=by
      by_cases one:j.val=0 <;> simp [rhs,one,DescentPackedRawTicket.ticket,DescentPackedRawTicket.double,Expr.Fits,peerFit,oldFit,roleFit]
    have hold (sign:Bool) (x:Expr) (above:x.Fits w base) : ((B sign).read (input banks 0) x).Fits w start:=by
      have shifted:=DescentOrdinaryAtomFieldRAM.ROM.bank_room pages_ (width a M) base start
        (atPage sign 0) (page_room _) le_rfl room
      have entry:=DescentOrdinaryAtomFieldRAM.ROM.bank_room pages_ (width a M) base start
        (atPage sign 1) (page_room _) le_rfl room
      have f:=(ProtocolRAMGeneratedWrite.fits_mono x sep above)
      have t:=(ProtocolRAMGeneratedWrite.fits_mono _ sep (raw 0))
      change (B sign).apply.Fits w start ∧ x.Fits w start ∧ (B sign).shift.Fits w start ∧ (input banks 0).Fits w start
      exact ⟨entry,f,shifted,t⟩
    exact ⟨hold false _ (raw (index j)),hold true _ newFit⟩
  have bat:=DescentPackedFlowBatch.execute start n (DescentDyadicSpan.span n) 2 e loaded ready space (DescentDyadicSpan.span_ge n)
  have boot:=DescentOrdinaryAtomFieldRAM.ROM.run pages_ (width a M) base m room
  refine ⟨Procedure.Exec.then boot.1 bat.1,?_,
    cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap pages_ (width a M) w base) (program_cheap w _)⟩
  intro z away
  rcases away with low|high
  · exact (bat.2.2 z (low.trans_le sep)).trans (DescentOrdinaryAtomFieldRAM.ROM.frame pages_ _ base m z (.inl low))
  · have rest:=DescentPackedFlowBatch.above start n (DescentDyadicSpan.span n) e loaded 0 2 z (DescentDyadicSpan.span_ge n) high
    exact rest.trans (DescentOrdinaryAtomFieldRAM.ROM.frame pages_ _ base m z (.inr (upper.trans high)))

theorem any (base k H G M w : ℕ) (banks : Fin 10→Bank) (peer old role : Expr) (m : Memory w)
    (bankFit : ∀i,(banks i).Fits w base) (cap : ∀i,H*chunks G M≤(banks i).size)
    (peerFit : peer.Fits w base) (oldFit : old.Fits w base) (roleFit : role.Fits w base)
    (word : M*unit k≤w/2) (space : endAddress base k H G M<2^w) :
    (hardware base k H G M w banks peer old role).Exec m (outputMemory base k H G M banks peer old role m)
      (time base k H G M banks peer old role) ∧
      (∀a,a<base ∨ endAddress base k H G M≤a → outputMemory base k H G M banks peer old role m a=m a) ∧
      CheapCode (hardware base k H G M w banks peer old role) :=by
  let n:=H*chunks G M
  let head:=finish base k M n
  have cut : base≤head:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have high : head≤endAddress base k H G M:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have small:=high.trans_lt space
  have initial:=initial_any base k H G M w banks peer old role m bankFit peerFit oldFit roleFit small
  have final_:=ROM.any head k H G M w (fields base k M n banks) (memory base k M n banks peer old role m)
    (fun j=>(ready_fields base banks j n bankFit cap small).1) (fun j=>(ready_fields base banks j n bankFit cap small).2) word space
  refine ⟨Procedure.Exec.then initial.1 final_.1,?_,cheap_seq initial.2.2 final_.2.2⟩
  intro a apart
  rcases apart with low|last
  · exact (final_.2.1 a (.inl (low.trans_le cut))).trans (initial.2.1 a (.inl low))
  · exact (final_.2.1 a (.inr last)).trans (initial.2.1 a (.inr (high.trans last)))

theorem execute_framed (base : ℕ) (banks : Fin 10→Bank) (peer old role : Expr)
    (x : Fin H→Fin G→Fragment k) (peerAt oldAt roleAt : Fin H→Fin G→Cell (k+2)) (m : Memory w)
    (within : ∀h g,11*(oldAt h g).val+(roleAt h g).val<2^(k+2))
    (bankFit : ∀i,(banks i).Fits w base) (cap : ∀i,H*chunks G M≤(banks i).size)
    (priorRead : ∀i,Reads (banks i) (fun h g=>sourceFields (x h g) i) M m)
    (peerFit : peer.Fits w base) (oldFit : old.Fits w base) (roleFit : role.Fits w base)
    (peerRead : Source peer peerAt M m) (oldRead : Source old oldAt M m) (roleRead : Source role roleAt M m)
    (room : finish base k M (H*chunks G M)<2^w) (word : M*unit k≤w/2) (positive : 0<M)
    (space : endAddress base k H G M<2^w) :
    let next_:=fun h g=>route (x h g) (peerAt h g) (DescentPackedRawTicket.payload oldAt roleAt within h g)
    let done:=outputMemory base k H G M banks peer old role m
    (hardware base k H G M w banks peer old role).Exec m done (time base k H G M banks peer old role) ∧
    (∀h g (f : Fin 5),digit (k+4) f.val (digit (outputWidth k) (lane g positive).val
      (done (ROM.output (finish base k M (H*chunks G M)) k H G M+(row H G M (position h g positive)).val)).val)=(resolve (next_ h g)).fields f) ∧
    (∀a,a<base ∨ endAddress base k H G M≤a→done a=m a) ∧ CheapCode (hardware base k H G M w banks peer old role) :=by
  intro next_ done
  let n:=H*chunks G M
  let head:=finish base k M n
  have compiled:=run base banks peer old role x peerAt oldAt roleAt m within bankFit cap priorRead
    peerFit oldFit roleFit peerRead oldRead roleRead room
  have packed:=ROM.execute_framed head k H G M w (fields base k M n banks) next_
    (fun j=>(ready_fields base banks j n bankFit cap room).1)
    (fun j=>(ready_fields base banks j n bankFit cap room).2) word positive space
    (memory base k M n banks peer old role m) compiled.2.1
  have cut : base≤head:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have high : head≤endAddress base k H G M:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  refine ⟨Procedure.Exec.then compiled.1 packed.1,packed.2.1,?_,cheap_seq compiled.2.2.2 packed.2.2.2⟩
  intro a apart
  rcases apart with low|last
  · exact (packed.2.2.1 a (.inl (low.trans_le cut))).trans (compiled.2.2.1 a (.inl low))
  · exact (packed.2.2.1 a (.inr last)).trans (compiled.2.2.1 a (.inr (high.trans last)))

end
end Hierarchy.DescentOrdinaryLocalFragment

end OAI

import OAI.Hierarchy.DescentScalarVenueHeaders

namespace OAI
/-! # Numeric safety of the scalar venue directory on an arbitrary input tape -/
namespace Hierarchy.DescentScalarVenueDirectory.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
variable {w : ℕ}

theorem geometry (sorted ends : Bank) (base H P : ℕ)
    (sortedFit : sorted.Fits w base) (endFit : ends.Fits w base)
    (sortedSize : H*P ≤ sorted.size) (endSize : H*P≤ends.size)
    (hi : base+size H P+P*(H*P)<2^w) : Room (chart sorted ends base H P) (base+size H P) H P w := by
  let out:=base+size H P
  let C:=chart sorted ends base H P
  change Room C out H P w
  have lim : max H (H*P)+1≤page H P:=Nat.le_pow_clog (by decide) _
  have cap : H≤page H P ∧ H*P≤page H P := ⟨(le_max_left ..).trans ((Nat.le_succ _).trans lim),(le_max_right ..).trans ((Nat.le_succ _).trans lim)⟩
  have space:out<2^w:=(Nat.le_add_right ..).trans_lt hi
  have pos:0<page H P:=Nat.two_pow_pos _;have below:base≤out:=Nat.le_add_right ..
  have fit {B:Bank} (fits:B.Fits w base):B.Fits w out:=⟨fits.1,fits.2.1,fits.2.2.trans below⟩
  have three (i : Fin 3) : (⟨base+i.val*page H P,width H P⟩:Bank).Fits w out:=by
    have total : base + 3*page H P < 2^w := space
    have span : page H P < 2^w := by omega
    refine ⟨pos, span, ?_⟩
    change base + i.val*page H P + page H P ≤ base + 3*page H P
    rw [Nat.add_assoc, ←Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _
  refine ⟨fit sortedFit,fit endFit,?_,?_,?_,sortedSize,endSize,cap.2,cap.2,cap.1,?_,hi⟩
  · simpa [C,chart] using three 0
  · simpa [C,chart] using three 1
  · simpa [C,chart] using three 2
  · exact cap.1.trans_lt (by dsimp [out,size] at space;omega)

end Hierarchy.DescentScalarVenueDirectory.ROM

namespace Hierarchy.DescentScalarVenueMask.Headers
open DescentSIMDLookup DescentSharedCableNames DescentPackedZip DescentScalarVenueDirectory ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {w : ℕ}

theorem any (sorted ends : Bank) (base H G M P : ℕ) (m : Memory w)
    (sortedFit : sorted.Fits w base) (endFit : ends.Fits w base) (sortedSize : H*P ≤ sorted.size)
    (endSize : H*P≤ends.size) (last : post base H G M P+H*chunks G M<2^w) :
    let out:=post base H G M P; let state:=image sorted ends base H G M P m
    (code sorted ends base H G M P w).Exec m state (ticks sorted ends base H G M P) ∧
    (∀s q,q.Fits w out→DescentPackedChildNeighbor.SIMD.Room (layout base H G M P s) q H G (Packed.bits P) 1 M w out) ∧
    (∀a,a<base ∨ out≤a →state a=m a) ∧ CheapCode (code sorted ends base H G M P w) := by
  intro out state
  have middle:afterHeaders base H P≤rom base H P:=Nat.le_add_right ..
  have top:rom base H P+DescentPackedChildNeighbor.SIMD.ROM.cells P (Packed.bits P) 1 M H G≤out:=Nat.le_add_right ..
  have exist:rom base H P≤out:=(Nat.le_add_right ..).trans top
  have high:out<2^w:=(Nat.le_add_right ..).trans_lt last
  have span:=middle.trans_lt (exist.trans_lt high)
  let C:=DescentScalarVenueDirectory.ROM.chart sorted ends base H P
  let terms:=List.ofFn (expression C H : Fin P→Expr)
  let mid:=DescentStaticWordColumn.image base (DescentScalarVenueDirectory.ROM.shape H P) m (DescentScalarVenueDirectory.ROM.size H P)
  have ss:=DescentScalarVenueDirectory.ROM.geometry sorted ends base H P sortedFit endFit sortedSize endSize span
  have fit : ∀e∈terms,e.Fits w (start base H P):=by
    intro e member; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp member;exact fitted C _ ss j
  have sep : start base H P+terms.length*(H*P)<2^w:=by simpa [terms,afterHeaders] using span
  let scans := passes C (start base H P) H P
  let printed := ProtocolRAM.result scans mid
  let tableSize := DescentPackedChildNeighbor.SIMD.ROM.cells P (Packed.bits P) 1 M H G
  let tableWords := DescentPackedChildNeighbor.SIMD.ROM.numbers P (Packed.bits P) 1 M H G
  let shapeCode := DescentStaticWordColumn.program w base (DescentScalarVenueDirectory.ROM.shape H P)
    (DescentScalarVenueDirectory.ROM.size H P)
  let shapeTicks := 4+10*DescentScalarVenueDirectory.ROM.size H P
  let lookupCode := DescentStaticWordColumn.program w (rom base H P) tableWords tableSize
  have run₁ : shapeCode.Exec m mid shapeTicks :=
    @DescentStaticWordColumn.mount w base (DescentScalarVenueDirectory.ROM.size H P)
      (DescentScalarVenueDirectory.ROM.shape H P) m ((Nat.le_add_right ..).trans_lt span)
  have run₂ : (ProtocolRAM.program w scans).Exec mid printed (ProtocolRAM.clock scans) :=
    @ProbeStage.Native.columns_exec w (H*P) (start base H P) terms mid
      (ProbeStage.Native.columns_safe terms le_rfl fit sep)
  have run₃ : lookupCode.Exec printed state (4+10*tableSize) :=
    @DescentStaticWordColumn.mount w (rom base H P) tableSize tableWords printed (top.trans_lt high)
  have headerRun : (shapeCode.seq (ProtocolRAM.program w scans)).Exec m printed
      (shapeTicks+ProtocolRAM.clock scans) :=
    @Procedure.Exec.then w shapeCode (ProtocolRAM.program w scans) m mid printed
      shapeTicks (ProtocolRAM.clock scans) (@run₁) (@run₂)
  refine ⟨@Procedure.Exec.then w (shapeCode.seq (ProtocolRAM.program w scans)) lookupCode
      m printed state (shapeTicks+ProtocolRAM.clock scans) (4+10*tableSize) (@headerRun) (@run₃),
    ?_, ?_, @cheap_seq w (shapeCode.seq (ProtocolRAM.program w scans)) lookupCode
      (@cheap_seq w shapeCode (ProtocolRAM.program w scans)
        (@DescentStaticWordColumn.cheap w base (DescentScalarVenueDirectory.ROM.shape H P)
          (DescentScalarVenueDirectory.ROM.size H P))
        (@ProtocolRAM.program_cheap w scans))
      (@DescentStaticWordColumn.cheap w (rom base H P) tableWords tableSize)⟩
  · intro s q ok
    exact (DescentPackedChildNeighbor.SIMD.ROM.arranged_expr (T:=P) (a:=Packed.bits P) (b:=1)
      (H:=H) (G:=G) (M:=M) (bank base H P s) q (rom base H P) (bankFits base H G M P w s last)
      ok last).2
  · intro a away
    have fr:=DescentStaticWordColumn.frame base (DescentScalarVenueDirectory.ROM.size H P) (DescentScalarVenueDirectory.ROM.shape H P) m
    have fp:=ProbeStage.Native.columns_frame (n:=H*P) (base:=start base H P) (address:=a) terms mid
    have retain := DescentStaticWordColumn.frame (rom base H P) tableSize tableWords printed a
    rcases away with below|above
    · have early:a<start base H P:=below.trans_le (Nat.le_add_right ..)
      exact (retain (.inl (early.trans_le ((Nat.le_add_right ..).trans middle)))).trans ((fp (.inl early)).trans (fr _ (.inl below)))
    · have later:afterHeaders base H P≤a:=middle.trans (exist.trans above)
      exact (retain (.inr (top.trans above))).trans ((fp (.inr (by simpa [terms,afterHeaders] using later))).trans (fr _ (.inr ((Nat.le_add_right ..).trans later))))

end
end Hierarchy.DescentScalarVenueMask.Headers

end OAI

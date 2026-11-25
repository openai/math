import OAI.ThreeFlat.Diagonal.TraceBitPhysical
import OAI.ThreeFlat.RAM.TraceRawOverlay
import OAI.ThreeFlat.RAM.FixedTraceImage
import OAI.ThreeFlat.Diagonal.TraceBitRecordWord
import OAI.ThreeFlat.Diagonal.TickWorkspace

namespace OAI
/-! # One native word of the virtual H trace from its two finite tables -/

namespace ThreeFlat.Diagonal.TraceBitPhysical
open Computability.VPVNP.BurstRAM RAM RAM.BitLayout TraceBitDescriptor
open scoped Classical Fin.CommRing
variable {F : Type} [Fintype F] [Field F] {w W p r k d S f : ℕ}
variable (hF : Fintype.card F≤2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
  (hs : S≤2^w) (hf : f≤2^(w+1)) (base : ℕ) (st : Word w)
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "srcs" => input (p:=p) (r:=r) (k:=k) (d:=d) hw hs hf base
local notation "keys" => records (p:=p) (r:=r) (k:=k) (d:=d) hw base S f
local notation "X" => TraceBitHeader.network hF hw hp base st hs hf r k d
local notation "ports" => Fintype.card (TraceAddressRecord.StaticPortIndex w p r k d)

/-- Only the physical H template and its eleven public address parameters are read.
This works at every scalar address in the virtual interval, including reverse lookups
at a different cursor lane. -/
theorem physical_source (code : FieldCode F W) (raw gateBase publicBase : ℕ) (m : Memory W)
    (pub : ∀ i, m (publicBase+(FixedTraceProgram.extra i).val) =
      FixedTraceProgram.publicWords G code S (TraceUniformRow.SharedCount w p r k d f)
        raw gateBase (gateBase+11*(G).cells) i)
    (gate : ∀ (i : Fin (G).cells) (j : Fin 11),m (gateBase+11*i.val+j.val)=record G code i j)
    (fields : ∀ (a : Fin ports) (j : Fin 11),m (TraceAddressReader.address (gateBase+11*(G).cells) a.val j) =
      (TraceAddressReader.fields (keys a) j : Word W))
    (gateFit : gateBase+11*(G).cells ≤ 2^W) (portFit : (gateBase+11*(G).cells)+11*ports ≤ 2^W)
    (safe : ∀ (v : Fin (2^d)) i,(keys i).Fits W v.val)
    (sourceFit : 2+ports+(G).internal<2^W) (widthFit : (G).cells<2^W) (eleven : 11<2^W) :
    ∀ a : Word W,raw≤a.val → a.val<raw+11*(X).cells →
      (FixedTraceProgram.program W).eval (fun i=>m (publicBase+i.val)) m (fun _=>a) =
        TraceRawOverlay.memory X code raw m a.val := by
  rw [←same_network (r:=r) (k:=k) (d:=d) hF hw hp hs hf base st]
  let N := PhysicalTraceSource.expanded G srcs
  intro a lo hi
  obtain ⟨⟨cell,slot⟩,eq⟩ := BitNetwork.exists_rowLocation (q:=N.cells) lo hi
  let j : Fin 11 := finSumFinEquiv slot
  obtain ⟨⟨v,u⟩,hc⟩ := (finProdFinEquiv (m:=2^d) (n:=(G).cells)).surjective cell
  let n := GuardedDescriptor.recordAddress raw (G).cells 0 v.val u.val j.val
  have hn : n=a.val := by
    rw [←eq,←hc]
    change raw+(11*(v.val*((G).cells+0)+u.val)+j.val)=raw+11*(u.val+(G).cells*v.val)+j.val
    rw [Nat.add_zero]
    ac_rfl
  have read := FixedTraceProgram.row G code keys srcs raw gateBase (gateBase+11*(G).cells)
    (fun i=>m (publicBase+i.val)) m pub gate fields gateFit portFit safe (records_correct hw hs hf base)
    sourceFit widthFit eleven v u j (by change n<2^W; rw [hn]; exact a.isLt)
  change (FixedTraceProgram.program W).eval _ _ (fun _=>(n:Word W))=_ at read
  have cast : (n:Word W)=a := by rw [hn]; exact Fin.cast_val_eq_self a
  rw [cast,hc] at read
  rw [read,←eq]
  exact (TraceRawOverlay.loaded N code raw m cell j).symm

/-- At the diagonal word size it suffices that S53 retains its packed finite table
and S57 its fixed operands. S52 can remain completely unwritten. -/
theorem sector_source {u dH Hbase hS fuel : ℕ} (age : 5120≤u)
    (hCard : Fintype.card F≤2^(16*u^10)) (width : 3≤16*u^10+1) (labels : u≤2^(16*u^10+1))
    (header : hS≤2^(16*u^10)) (time : fuel≤2^(16*u^10+1)) (state : Word (16*u^10))
    (grid : hS+fuel≤2^(1+dH)) (text : Hbase+(1+6*u+u)*(16*u^10)≤hS) (depth : dH≤15*u^10)
    (encoder : FieldCode F (16*u^10)) (before now : Memory (16*u^10)) :
    let GH := TraceStaticRow.gateTable hCard width labels Hbase fuel state u u dH
    let KH := records (p:=u) (r:=u) (k:=u) (d:=dH) width Hbase hS fuel
    let NH := TraceBitHeader.network hCard width labels Hbase state header time u u dH
    let raw := TickWorkspace.base u 52
    let packed := TickWorkspace.base u 53
    let publicBase := TickWorkspace.base u 57
    FixedTraceImage.count GH≤TickWorkspace.stride u →
    (∀ i,now (publicBase+(FixedTraceProgram.extra i).val) =
      FixedTraceProgram.publicWords GH encoder hS (TraceUniformRow.SharedCount (16*u^10) u u u dH fuel)
        raw packed (packed+11*GH.cells) i) →
    (∀ a,packed≤a → a<packed+FixedTraceImage.count GH →
      now a=FixedTraceImage.packed GH encoder KH packed before a) →
    ∀ a : Word (16*u^10),raw≤a.val → a.val<raw+11*NH.cells →
      (FixedTraceProgram.program (16*u^10)).eval (fun i=>now (publicBase+i.val)) now (fun _=>a) =
        TraceRawOverlay.memory NH encoder raw now a.val := by
  intro GH KH NH raw packed publicBase size params keep
  have du : 1≤u^10 := Nat.one_le_pow _ _ (by omega)
  have c53 : 53<TickWorkspace.stride u := by
    change 53<(2^(u^10))^4
    have four : 4≤u^10 := (show 4≤u by omega).trans (Nat.le_self_pow (by decide) u)
    have t : 16≤2^(u^10) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) four
    exact (by decide : 53<16^4).trans_le (Nat.pow_le_pow_left t _)
  have wfit := TickWorkspace.word_space (by omega : 1≤u) c53
  let n := Fintype.card (TraceAddressRecord.StaticPortIndex (16*u^10) u u u dH)
  change 11*(GH.cells+n)≤TickWorkspace.stride u at size
  have internal : GH.internal≤GH.cells := TraceStaticRow.table_internal_le_cells
    hCard width labels Hbase fuel state u u dH
  have addr := TickWorkspace.lower u 53
  have pcap : u≤1*(16*u^10+1)^1 := by
    have := Nat.le_self_pow (by decide : 10≠0) u
    simp only [pow_one,one_mul]
    omega
  refine physical_source hCard width labels header time Hbase state encoder raw packed publicBase now params ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j
    trans FixedTraceImage.packed GH encoder KH packed before (packed+11*i.val+j.val)
    · apply keep _ (by omega)
      change _<packed+11*(GH.cells+n)
      have hi : i.val<GH.cells := i.isLt
      have := j.isLt
      omega
    · exact FixedTraceImage.packed_gate GH encoder KH packed before i j
  · intro i j
    trans FixedTraceImage.packed GH encoder KH packed before (TraceAddressReader.address (packed+11*GH.cells) i.val j)
    · apply keep _ (by unfold TraceAddressReader.address; omega)
      change _<packed+11*(GH.cells+n)
      have hi : i.val<n := i.isLt
      have := j.isLt
      change packed+11*GH.cells+11*i.val+j.val<packed+11*(GH.cells+n)
      omega
    · exact FixedTraceImage.packed_port GH encoder KH packed before i j
  · change packed+11*GH.cells≤_
    dsimp only [packed]
    omega
  · change packed+11*GH.cells+11*n≤_
    dsimp only [packed]
    omega
  · intro v j
    exact TraceAddressRecord.staticBitPort_fits_of_public_bounds (c:=1) (e:=1)
      width grid text age depth pcap pcap pcap v ((Fintype.equivFin _).symm j)
  · change 2+n+GH.internal<_
    omega
  · change GH.cells<_
    omega
  · omega

end ThreeFlat.Diagonal.TraceBitPhysical

end OAI

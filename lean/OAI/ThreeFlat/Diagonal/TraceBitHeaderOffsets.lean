import OAI.ThreeFlat.Diagonal.TraceBitNetwork

namespace OAI
/-! # The public XOR masks of a compressed self-simulation row layout -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open LaneCursor
variable {F : Type*} {lane low n c : ℕ}

theorem indexedLayout_offsets {t b q P o : ℕ} (ht : t = 2^lane*2^low)
    (rows : Fin t → Fin c → TraceCircuit.Cell F n q) (inp : Fin t → Fin q → BitSource b P)
    (hidden : Fin b → Row lane low) (pins : Fin P → Row lane low)
    (off : Fin o → Row lane low) (base : Fin o) (hbase : (off base).val=0)
    (idx : Fin t → Fin q → Fin o) (ok : ∀ v j,
      v.cast ht = partner (sourceRow hidden pins (v.cast ht) (inp v j)) (off (idx v j))) :
    (indexedLayout ht rows inp hidden pins off base hbase idx ok).offset = off := by
  subst t
  rfl

end ThreeFlat.Diagonal.TraceUniformRow

namespace ThreeFlat.Diagonal

open Computability.VPVNP BurstRAM LaneCursor
variable {F : Type*} [Fintype F] [CommRing F] {w p lane low S f : ℕ}

theorem TraceStaticRow.layout_offset (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f ≤ 2^(1+(lane+low))) :
    (TraceStaticRow.layout hF hw hp base st hs hf r k fit).offset =
      fun i => TracePhysical.laneRow (TracePhysical.offset (lane+low) i) := by
  unfold TraceStaticRow.layout
  exact TraceUniformRow.indexedLayout_offsets ..

theorem TraceBitHeader.rawLayout_offset (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f ≤ 2^(1+(lane+low))) :
    (TraceBitHeader.rawLayout hF hw hp base st hs hf r k fit).offset =
      fun i => TracePhysical.laneRow (TracePhysical.offset (lane+low) i) :=
  TraceStaticRow.layout_offset hF hw hp base st hs hf r k fit

theorem TraceBitHeader.layout_offset (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f ≤ 2^(1+(lane+low))) :
    (TraceBitHeader.layout hF hw hp base st hs hf r k fit).offset =
      fun i => TracePhysical.laneRow (TracePhysical.offset (lane+low) i) :=
  TraceBitHeader.rawLayout_offset hF hw hp base st hs hf r k fit


end ThreeFlat.Diagonal

end OAI

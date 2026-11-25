import OAI.Computability.BorderVNP.DiagonalSignedPublicationFields
import OAI.Computability.BorderVNP.CubeISALocalRowDecoderRoom
import OAI.Computability.BorderVNP.CubeRouteProfileInputs

/-! # Schedule parameters read from the real published signed directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots RoutingISA.LocalRow
open Packing RoutingOutputs DiagonalResidueRAM GeometryAdvice BorderVNP.Cube

set_option maxRecDepth 6000 in
/-- The placement and directory opcodes preserve the original geometry frame;
the count consumed by the chooser is exactly the length of the array they wrote.
The original signed bootstrap supplies its product-label alphabet at frame 56. -/
theorem signed_published_label_layout {w : ℕ} (task : SignedTaskArena.Layout) (dir : Directory.Layout)
    (frame origin next gap : ℕ) (profile placed : Memory w) (pp lp : ℕ → ℕ × ℕ)
    (old : Fin 81 → Word w) (raw team subtotal fresh reserve gates outputs width off ell : ℕ)
    (pub : Arg → Word w) (f : BroadcastFrame) (hdr : List Bool) :
    let ar := task.cube
    let pl := privateLayout frame origin ar.cables ar.cells dir.entries dir.description gap
    let rows := dir.directory pp lp
    let out := Directory.ISA.publish placed frame next rows
    let l := LabelIndex.layout frame (readings out)
    (pub 0).val=frame → frame+112 ≤ next → next+7*dir.candidates ≤ origin → origin < 2^w →
    0 < ar.header.d → 0 < ar.header.blocks → ar.stop < 2^w →
    Header frame origin ar.cables ar.cells dir.entries (readings profile) →
    pl.Image (readings profile) dir.entries (readings placed) →
    BootPins pub f (signedProfileExtension task old dir origin ar.cables ar.cells raw team subtotal fresh reserve
      gates outputs width off ell) hdr out →
    l.cells=ar.cells ∧ l.cableCount=ar.cables ∧ l.deliveryCount=rows.length ∧ l.labels=ar.alphabet := by
  intro ar pl rows out l same low span endFit symbols blocks fit header slots boot
  have keep {j : ℕ} (hj : j<112) (skip : j≠9) : readings out (frame+j)=readings profile (frame+j) := by
    have first := CableTriples.published_outside placed frame next rows (frame+j) (by omega) (Or.inl (by omega))
    have before := slots.outside (frame+j) (fun i _ => by dsimp only [pl,privateLayout,bases]; omega)
      (by dsimp only [pl,privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied]; left; omega)
    exact (congrArg Fin.val first).trans before
  have count : rows.length < 2^w := by
    have := dir.directory_length_le pp lp
    dsimp only [rows]
    omega
  have product := (bootScalars_of_arena ar w symbols blocks fit).2
  have lab := congrArg Fin.val (boot.extension (25 : Fin 81))
  rw [same] at lab
  change readings out (frame+31+25)=ar.alphabet % 2^w at lab
  refine ⟨(keep (by decide : 11<112) (by decide)).trans header.cells,
    (keep (by decide : 7<112) (by decide)).trans header.edges,?_,?_⟩
  · change (Directory.ISA.publish placed frame next rows (frame+9)).val=_
    rw [Directory.ISA.publish,Function.update_self]
    exact Nat.mod_eq_of_lt count
  · change readings out (frame+56)=ar.alphabet
    simpa only [Nat.add_assoc] using lab.trans (Nat.mod_eq_of_lt product)

/-- Even the largest raw declaration fits the decoder's two logarithmic width
fields. Both widths are paid by the same cube arena used by the signed route. -/
theorem signed_decoder_widths {w : ℕ} (ar : CubeArena.Layout) (saved : ℕ) (symbols : 2 ≤ ar.header.d)
    (blocks : 0 < ar.header.blocks) (axes : ar.header.a=ar.n+1) (fit : ar.stop < 2^w) :
    (ar.header.decoder saved).cw ≤ w ∧ (ar.header.decoder saved).rw ≤ w := by
  have sym : 0<ar.header.d := by omega
  have product := (bootScalars_of_arena ar w sym blocks fit).2
  have a : ar.header.a ≤ 2^w := by
    rw [axes]
    have pow := Nat.pow_le_pow_left symbols (ar.n+1)
    have base : ar.n+1 < 2^(ar.n+1) := Nat.lt_two_pow_self
    omega
  have c : ar.header.cap+1 ≤ ar.pairStride := by unfold CubeArena.Layout.pairStride; omega
  have positive : 0 < ar.header.d^2 := Nat.pow_pos sym
  have stride : ar.pairStride ≤ ar.header.d^2*ar.pairStride := Nat.le_mul_of_pos_left _ positive
  have room : ar.header.d^2*ar.pairStride ≤ ar.stop := by unfold CubeArena.Layout.stop CubeArena.Layout.cellBank; omega
  exact ⟨Nat.clog_le_of_le_pow a,Nat.clog_le_of_le_pow (c.trans (stride.trans (room.trans fit.le)))⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI

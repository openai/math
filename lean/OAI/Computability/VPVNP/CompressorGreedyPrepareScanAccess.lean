import OAI.Computability.VPVNP.CompressorGreedyPrepareVisitAccess
import OAI.Computability.VPVNP.RAMChoicePrefix

/-! # External accesses of the complete greedy preparation sweep

Each row writer leaves the old mate tables readable for the next row.
The external address bounds therefore hold throughout the native scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy.PrepareAccess

open BurstRAM SourceTransport Compression
open scoped Fin.CommRing

variable {w N width d : ℕ} {V : Type*}

theorem scan (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows' : OperandRows d) (m : Memory w)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (space : L.limit < 2^w) (free : GraphOutside (d := d) L T order)
    (size : ∀ i : Fin N, (rowWords T G order (order.symm i) rows').length = width)
    (rd : ℕ → Prop) (cells : ∀ e : V × Fin d, ∀ b ∈ [T.outgoing,T.incoming], rd (b+portNumber order e).val)
    (rs : List (Report w))
    (run : runSegment ((Relocated.preparePass rows').table.instantiate w (Relocated.publicWords d L T)).program
      (1+(Relocated.prepareCode rows').length) (some 0) m (List.replicate N []) = some rs) :
    LogAccess rd (Interval L.origin L.limit) rs := by
  let P := ((Relocated.preparePass rows').table.instantiate w (Relocated.publicWords d L T)).program
  let fuel := 1+(Relocated.prepareCode rows').length
  apply OrdinalRun.footprint P fuel (Fin.ofNat (2^w)) N (fun _ ↦ T.Represents G order) rd
    (Interval L.origin L.limit) _ 0 _ m rs (by simp) rep run
  intro j hj mem hRep bits row executed
  let i : Fin N := ⟨j,hj⟩
  obtain ⟨es,he,read,write⟩ := one L T G order rows' mem i labels hRep space free (size i) rd cells
  have eq := (execute_prefix_unique he (show execute P fuel (P.start (Fin.ofNat _ j)) mem ([]++bits) =
    some row from executed)).2
  subst row
  have keep (e : V × Fin d) (b : Word w) (hb : b ∈ [T.outgoing,T.incoming]) :
      after mem es (b+portNumber order e).val = mem (b+portNumber order e).val := by
    apply SourceTransport.after_outside mem write
    have := free e b hb
    rintro ⟨x,y⟩; omega
  exact ⟨rfl,⟨hRep.degree,hRep.fits,hRep.vertices,fun e ↦ (keep e _ (by simp)).trans (hRep.outgoing e),
    fun e ↦ (keep e _ (by simp)).trans (hRep.incoming e)⟩,read,write⟩

end CompressorRecords.Greedy.PrepareAccess

end VPVNP
end Computability
end OAI

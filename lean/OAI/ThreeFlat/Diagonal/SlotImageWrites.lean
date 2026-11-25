import OAI.ThreeFlat.Diagonal.SlotImage
import OAI.ThreeFlat.RAM.SweepSegment

namespace OAI
/-! # Publishing the six graph columns and the source-width array in RAM -/

namespace ThreeFlat.Diagonal.SlotImage

open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan
open CompressorPacking.Native
open scoped Fin.NatCast

variable {B L : Type} {W v lanes d : ℕ} (G : LiftedSlots B d L) (base : B ≃ Fin v) (lane : L ≃ Fin lanes)
    (C : Columns) (width : Edge B L d → ℕ)

private theorem fieldBound (p : B × Fin d) (b : Bool) (f : Fin 3) (vertices : v≤2^W) (degree : d≤2^W)
    (laneFit : lanes≤2^W) : fields G base lane p b f<2^W := by
  fin_cases f
  · exact (base _).isLt.trans_le vertices
  · exact (oriented G b p).2.isLt.trans_le degree
  · exact (lane _).isLt.trans_le laneFit

private theorem rowsBound (count : C.rows=v*d) (p : B × Fin d) (b : Bool) (f : Fin 3) :
    C.graph≤cell C base p b f ∧ cell C base p b f<C.graph+6*C.rows := by
  have low : ordinal base p<C.rows := by rw [count]; exact ordinal_lt base p
  have hi : column b f<6 := by cases b <;> dsimp [column] <;> have := f.isLt <;> omega
  have h := Nat.mul_le_mul_right C.rows hi
  rw [Nat.succ_mul] at h
  unfold cell
  rw [Nat.mul_comm C.rows]
  omega

/-- Two numerical producers suffice at their actual slot coordinates. The
later width stores leave all earlier graph fields in place. -/
theorem stored_after_fill (m : Memory W) (graphWord widthWord : ℕ → Word W) (count : C.rows=v*d)
    (separate : C.graph+6*C.rows≤C.widths ∨ C.widths+v*d*lanes≤C.graph)
    (vertices : v≤2^W) (degree : d≤2^W) (laneFit : lanes≤2^W) (bitsFit : ∀ e, width e<2^W)
    (graphRead : ∀ p b f, graphWord (cell C base p b f)=((fields G base lane p b f:ℕ):Word W))
    (widthRead : ∀ e, widthWord (C.widths+edgeOrdinal base lane e)=((width e:ℕ):Word W)) :
    Stored G base lane C (fun i => (fillSegment C.widths (v*d*lanes) widthWord
      (fillSegment C.graph (6*C.rows) graphWord m) i).val) width where
  rowCount := count
  graph p b f := by
    obtain ⟨lb,ub⟩ := rowsBound base C count p b f
    have outside : ¬(C.widths≤cell C base p b f ∧ cell C base p b f<C.widths+v*d*lanes) := by
      rcases separate with h | h <;> omega
    simp only [fillSegment,ite_eq_right outside,ite_eq_left (And.intro lb ub),graphRead,
      Fin.val_cast_of_lt (fieldBound G base lane p b f vertices degree laneFit)]
  widthWord e := by
    have low : C.widths≤C.widths+edgeOrdinal base lane e := Nat.le_add_right ..
    have high := Nat.add_lt_add_left (edgeOrdinal_lt base lane e) C.widths
    simp only [fillSegment,ite_eq_left (And.intro low high),widthRead,Fin.val_cast_of_lt (bitsFit e)]

/-- The actual chronological scan has the same image even though the row
program runs against memory already modified by its earlier iterations. -/
theorem stored_after_sweeps (m : Memory W) (graphRow widthRow : Word W → Memory W → Word W)
    (graphWord widthWord : ℕ → Word W) (count : C.rows=v*d)
    (separate : C.graph+6*C.rows≤C.widths ∨ C.widths+v*d*lanes≤C.graph)
    (graphFit : C.graph+6*C.rows<2^W) (widthFit : C.widths+v*d*lanes<2^W)
    (vertices : v≤2^W) (degree : d≤2^W) (laneFit : lanes≤2^W) (bitsFit : ∀ e, width e<2^W)
    (graphRead : ∀ p b f, graphWord (cell C base p b f)=((fields G base lane p b f:ℕ):Word W))
    (widthRead : ∀ e, widthWord (C.widths+edgeOrdinal base lane e)=((width e:ℕ):Word W))
    (gStable : ∀ a : Word W, C.graph≤a.val → a.val<C.graph+6*C.rows →
      ∀ m', agreesOutside C.graph (C.graph+6*C.rows) m' m → graphRow a m'=graphWord a.val)
    (wStable : ∀ a : Word W, C.widths≤a.val → a.val<C.widths+v*d*lanes →
      ∀ m', agreesOutside C.widths (C.widths+v*d*lanes) m' (fillSegment C.graph (6*C.rows) graphWord m) →
        widthRow a m'=widthWord a.val) :
    Stored G base lane C (fun i => (sweep widthRow (v*d*lanes) (C.widths:Word W)
      (sweep graphRow (6*C.rows) (C.graph:Word W) m) i).val) width := by
  have g : ((C.graph:Word W)).val=C.graph := Fin.val_cast_of_lt (by omega)
  have ww : ((C.widths:Word W)).val=C.widths := Fin.val_cast_of_lt (by omega)
  rw [sweep_segment graphRow C.graph (C.graph+6*C.rows) m graphWord gStable (C.graph:Word W)
    (6*C.rows) m g.ge (by rw [g]) graphFit (fun _ _=>rfl),g,
    sweep_segment widthRow C.widths (C.widths+v*d*lanes) _ widthWord wStable (C.widths:Word W)
    (v*d*lanes) _ ww.ge (by rw [ww]) widthFit (fun _ _=>rfl),ww]
  exact stored_after_fill G base lane C width m graphWord widthWord count separate vertices degree laneFit
    bitsFit graphRead widthRead

end ThreeFlat.Diagonal.SlotImage

end OAI

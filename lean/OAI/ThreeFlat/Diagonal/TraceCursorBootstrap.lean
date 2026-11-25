import OAI.ThreeFlat.Diagonal.TraceCursorState
import OAI.ThreeFlat.RAM.InitialRelayBootstrap

namespace OAI
/-! # The seed native procedure establishes the block's numbered cursor state -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM PhysicalProcedure LaneCursor SlotImage
open CompressorPacking.Native
open scoped Fin.CommRing

variable {F : Type} [Field F] (B : Block F)

theorem cursor_width_card {k : ℕ} (hk : 2≤k+1) (low offsets slots : ℕ) (e) :
    (B.cursorState hk low offsets slots).width e =
      Fintype.card (Fin offsets × Fin (2^low) × Fin slots × Fin 3) := by
  rw [B.cursorState_width]
  simp only [Fintype.card_prod,Fintype.card_fin]
  ring

private theorem transfer {v old new n lanes t : ℕ} {L : Type*} (G : LiftedSlots (Fin v) old L)
    (h : old=new) (order : v=n) (num : L ≃ Fin lanes) (C : Columns) (mem : ℕ → ℕ)
    (s : Stored G (Equiv.refl _) num C mem (fun _ => t)) :
    Stored (h ▸ G : LiftedSlots (Fin v) new L) (finCongr order) num C mem (fun _ => t) := by
  subst new
  subst n
  exact s

theorem cursor_bootstrap {W k : ℕ} (current : Word W) (hk : 2≤k+1) (C : Columns)
    (low offsets slots : ℕ) (rows : C.rows=(k+1)*((B.cursorCopies+1)*2))
    (bits : 2^low*(offsets*slots*3)<2^W) (axes : k+1≤W) (wide : 6<2^W)
    (graph : C.graph+6*C.rows<2^W) (width : C.widths+C.rows*2^(k+1)<2^W)
    (apart : C.graph+6*C.rows≤C.widths ∨ C.widths+C.rows*2^(k+1)≤C.graph) :
    let A := B.cursorState hk low offsets slots
    let d := (B.cursorCopies+1)*2
    let t := 2^low*(offsets*slots*3)
    (InitialRelayBootstrap.procedure current C (k+1) d t).Spec
      (InitialRelayBootstrap.loaded current C (k+1) d (2^(k+1)))
      (fun m out => out=InitialRelayBootstrap.image C (k+1) d (2^(k+1)) t m ∧
        Stored A.graph A.order (tagOrdinal _) C (fun a => (out a).val) A.width)
      (InitialRelayBootstrap.budget W C (k+1) d (2^(k+1))) := by
  dsimp only
  intro _ _ _ machine
  apply Procedure.Spec.mono
    (A:=InitialRelayBootstrap.procedure current C (k+1) ((B.cursorCopies+1)*2) (2^low*(offsets*slots*3)))
    (InitialRelayBootstrap.stored_spec current hk C _ rows bits axes (by omega) wide graph width apart)
    (fun _ h => h) _ le_rfl machine
  intro m out h
  refine ⟨h.1,?_⟩
  exact transfer _ B.cursor_degree (Fintype.card_fin (k+1)).symm (tagOrdinal _) C _ h.2

end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI

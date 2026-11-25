import OAI.Computability.BorderVNP.CellPacketGeometryFixed
import OAI.Computability.BorderVNP.CellPacketGeometryFixedReferences
import OAI.Computability.BorderVNP.CellPacketGeometryLiveFrame

/-! # One fixed native geometry table for all branches of the sparse initializer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open PackedHistogram ParseBatchSort Packing.Word Packing.BankPacket VPVNP.VerifierNetwork GeometryFrameEncoding
open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryAdvice RoutingISA.CellPacket

variable {σ E I Orig : Type} [Fintype σ] [Fintype E] [Fintype I] {s C p d k w u : ℕ}

/-- The source stage consists of the single site-word arithmetic frame and the
two histogram frames. Its output labeling depends only on the template. -/
noncomputable def Template.sourcePins (T : Template E I Orig s C) (up : Frame σ (Base s k w E I)) :
    Frame σ (Schema.Pins T.atoms.length T.chunkLabels.length k w T.Fields) :=
  (T.exists_liveFrame up T.chunkLabels.get).choose

/-- Hardwired reference selected by the static global chunk ordinal. -/
def Template.reference (T : Template E I Orig s C) (baseOwner : Fin s → Fin C)
    (pin : Orig → T.Fields) (i : Fin T.chunkLabels.length) : Reference T.atoms.length T.Fields :=
  (T.fixedReferences baseOwner pin).get (i.cast (T.fixedReferences_length baseOwner pin).symm)

/-- One table for all choices of input, owner cells, and private one-copy bodies. -/
noncomputable def Template.geometry (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields) (d : ℕ) (fit : C+T.atoms.length+C ≤ 2^p)
    (dest H : ℕ) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) :=
  compile (joint (Schema.source C p d (T.sourcePins up))
    (Schema.expression C d fit dest H (T.reference baseOwner pin))) pins

/-- A bound on the compiled literal gate table. The two sort budgets are shared
across all sections; each fixed record operand contributes its own expression size. -/
theorem Template.geometry_size (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields) (d : ℕ) (fit : C+T.atoms.length+C ≤ 2^p)
    (dest H : ℕ) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) :
    (T.geometry up baseOwner pin d fit dest H pins).size ≤
      4*(up.size + 1 + (∑ z : T.RowPin, (tape (T.format z.1))[z.2].nodes)*(100*(w+1)^2) +
      2*histogramBudget s C k w + T.atoms.length*(k+w) + T.chunkLabels.length*k + Fintype.card T.Fields*w + 1 +
      2^p*(k+w) + 2^d*k + Fintype.card T.Fields*w + 1 +
      (sortedFrame p k w).size + (sortedFrame d k w).size + 1 + 5*2^d*(100*(w+1)^2)) := by
  have a := (T.exists_liveFrame up T.chunkLabels.get).choose_spec.1
  change (T.sourcePins up).size ≤ _ at a
  have b := Schema.joint_budget (d := d) (T.sourcePins up) fit dest H (T.reference baseOwner pin)
  exact (GeometryFrameEncoding.size_le _ pins).trans (Nat.mul_le_mul_left 4 (b.trans (by omega)))

/-- Running the literal fixed table on an accepted input constructs the actual
compact public source buffer and native chunk directory in RAM for every cell.
The table's source is individual site labels and fixed record operands. Both
the private factors and their repetition counts remain outside the public table. -/
theorem Template.execute_geometry (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields) (fit : C+T.atoms.length+C ≤ 2^p)
    (space : C+(Schema.coords T.chunkLabels.length).length+C ≤ 2^d) (H : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : RoutingISA.Bank w) (mem : Memory w)
    (f : BroadcastFrame) (a : Stripe) (L : RoutingISA.Pins.Layout) (P : RoutingISA.Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (frameFits : f.Fits w (pub 0).val) (stripeFits : a.Fits f w (pub 0).val)
    (keysFit : C < 2^k) (sourceFit : l.dest+2^p < 2^w) (hd : 2^d ≤ 2^w)
    (header : H < 2^w) (one : 1 < 2^w) (owner : Fin s → Fin C) :
    let t := T.geometry up baseOwner pin d fit l.dest H pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    let g := up.eval input
    let args := fun e => value fun j => g (.inl (.inr (.inl (e,j))))
    let fields := fun i e => value fun j => g (.inr (i,e,j))
    let D := T.directory owner args fields
    let nEq := (T.wordCapacity owner args fields).symm
    let mEq := T.referenceCapacity owner pin args fields
    GeometryOutput.Placement pub l base start a.dense src t →
    PhysicalInput pub mem f a L P l base start src t x → g (.inl (.inr (.inr ()))) = true →
    (∀ i, value (fun j => g (.inl (.inl (i,j)))) = (owner i).val) →
    (∀ c, (D.cellBoxes c).length < 2^w) → (∀ c, (D.cellRecords c).length < 2^w) →
    (∀ z : T.RowPin, ((tape (T.format z.1))[z.2.val]).Fits w (fields z.1)) →
    (∀ i : Fin T.atoms.length, ∀ n, T.atoms[i.val].2 = .literal n → n < 2^w) →
    ∃ es z mz, ∃ π : Equiv.Perm (Fin (2^p)), Runs pub mac reconstruct bank mem es z mz ∧
      traceCost es ≤ GeometryAdviceRate.ticks t.size u (Total p d) w w ∧
      Schema.Buffers D (nEq ▸ fit) (mEq ▸ space) l.dest H (fun i => ((D.referenceRows pin).get i).2)
        (fun i => ((D.referenceRows pin).get i).1) (T.arguments args fields) (readings mz) π ∧
      ∀ bits fs, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,bank⟩ mem bits = some fs ↔
        fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  intro t input g args fields D nEq mEq layout physical valid keys boxFit rowFit fits literals
  obtain ⟨words,owners,arg,accept⟩ := (T.exists_liveFrame up T.chunkLabels.get).choose_spec.2
    input owner keys keysFit boxFit rowFit fits literals
  have own (i : Fin T.chunkLabels.length) : value (fun j => (T.sourcePins up).eval input (.inr (.inl (i,j)))) =
      ((D.referenceRows pin).get (i.cast mEq)).1.val := by
    have eqn := congrArg (fun a : List (Fin C) => a[i.val]?) (T.chunkLabels_eval owner args fields pin)
    have hi : i.val < (D.referenceRows pin).length := (i.cast mEq).isLt
    simp only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,Option.map_some] at eqn
    change some _ = Option.map Prod.fst (D.referenceRows pin)[i.val]? at eqn
    rw [List.getElem?_eq_getElem hi,Option.map_some,Option.some.injEq] at eqn
    exact (owners i).trans (congrArg Fin.val eqn)
  obtain ⟨es,z,mz,π,run,time,buf,unique⟩ := Schema.execute_fixed fit space H (T.reference baseOwner pin)
    (T.sourcePins up) pub mac bank mem f a L P l base start src pins x frameFits stripeFits keysFit sourceFit hd
    header one D pin nEq mEq (T.fixedReference_get baseOwner owner pin args fields) layout physical
    (accept.trans valid) words own
  have he : (fun e => value fun j => (T.sourcePins up).eval input (.inr (.inr (.inl (e,j))))) =
      T.arguments args fields := funext arg
  exact ⟨es,z,mz,π,run,time,he ▸ buf,unique⟩

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI

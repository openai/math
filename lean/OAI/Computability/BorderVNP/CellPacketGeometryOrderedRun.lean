import OAI.Computability.BorderVNP.CellPacketGeometryOrderedPins

/-! # Native execution with exact physical site-major record order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open PackedHistogram ParseBatchSort Packing.Word Packing.BankPacket VPVNP.VerifierNetwork GeometryFrameEncoding
open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryAdvice RoutingISA.CellPacket

variable {σ E I Orig : Type} [Fintype σ] [Fintype E] [Fintype I] {s C p d b q k w u : ℕ}

/-- Literal gate table with the site sort, the cell sort, and the three-word
descriptor sort. It depends only on the public shape and static source frames. -/
noncomputable def Template.orderedGeometry (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields)
    (cap : T.recordSlots.length ≤ 2^b) (pad : s < 2^q) (d : ℕ) (fit : C+T.atoms.length+C ≤ 2^p)
    (dest H : ℕ) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) :=
  compile (joint (Schema.source C p d (T.orderedPins up anchors baseOwner cap pad))
    (Schema.expression C d fit dest H (T.reference baseOwner pin))) pins

/-- The total charged geometry, including both true source frames and the
extra sort of the compact chronological record stream. -/
theorem Template.orderedGeometry_size (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields)
    (cap : T.recordSlots.length ≤ 2^b) (pad : s < 2^q) (d : ℕ) (fit : C+T.atoms.length+C ≤ 2^p)
    (dest H : ℕ) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) :
    (T.orderedGeometry up anchors baseOwner pin cap pad d fit dest H pins).size ≤
      4*((T.sourcePins up).size+anchors.size+2^b*(q+(w+k))+(sortedFrame b q (w+k)).size+
        2^p*(k+w)+2^d*k+Fintype.card T.Fields*w+1+(sortedFrame p k w).size+(sortedFrame d k w).size+
        1+5*2^d*(100*(w+1)^2)) := by
  have first := T.orderedPins_size up anchors baseOwner cap pad
  have second := Schema.joint_budget (d := d) (T.orderedPins up anchors baseOwner cap pad) fit dest H
    (T.reference baseOwner pin)
  exact (GeometryFrameEncoding.size_le _ pins).trans (Nat.mul_le_mul_left 4 (second.trans (by omega)))

/-- On every genuine input branch, the same native gate table reconstructs the
true site-major records and the ordered physical descriptor buffer of each cell.
All stable tie ordinals, header addresses and reserved supplemental words agree
with the subsequent sparse cell initializer. -/
theorem Template.execute_orderedGeometry (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields)
    (cap : T.recordSlots.length ≤ 2^b) (pad : s < 2^q) (wide : 2^b ≤ 2^(w+k))
    (fit : C+T.atoms.length+C ≤ 2^p) (space : C+(Schema.coords T.chunkLabels.length).length+C ≤ 2^d) (H : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : RoutingISA.Bank w) (mem : Memory w)
    (f : BroadcastFrame) (a : Stripe) (L : RoutingISA.Pins.Layout) (P : RoutingISA.Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (frameFits : f.Fits w (pub 0).val) (stripeFits : a.Fits f w (pub 0).val)
    (keysFit : C < 2^k) (sourceFit : l.dest+2^p < 2^w) (hd : 2^d ≤ 2^w)
    (header : H < 2^w) (one : 1 < 2^w) (owner : Fin s → Fin C) (anchor : Fin s → Fin s)
    (linked : ∀ i, owner (anchor i) = owner i) :
    let t := T.orderedGeometry up anchors baseOwner pin cap pad d fit l.dest H pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    let g := up.eval input
    let args := fun e => value fun j => g (.inl (.inr (.inl (e,j))))
    let fields := fun i e => value fun j => g (.inr (i,e,j))
    let D := T.directory owner args fields
    let G := D.regroup anchor
    let nEq := ((D.regroup_wordCapacity anchor rfl linked).trans (T.wordCapacity owner args fields)).symm
    let mEq : T.chunkLabels.length = (G.referenceRows pin).length := by
      simpa only [List.length_map] using congrArg List.length
        ((T.chunkLabels_eval owner args fields pin).trans (D.regroup_owners anchor pin).symm)
    GeometryOutput.Placement pub l base start a.dense src t →
    PhysicalInput pub mem f a L P l base start src t x → g (.inl (.inr (.inr ()))) = true →
    (∀ i, value (fun j => anchors.eval input (i,j)) = (anchor i).val) →
    (∀ i, value (fun j => g (.inl (.inl (i,j)))) = (owner i).val) →
    (∀ c, (G.cellBoxes c).length < 2^w) → (∀ c, (G.cellRecords c).length < 2^w) →
    (∀ z : T.RowPin, ((tape (T.format z.1))[z.2.val]).Fits w (fields z.1)) →
    (∀ i : Fin T.atoms.length, ∀ n, T.atoms[i.val].2 = .literal n → n < 2^w) →
    ∃ es z mz, ∃ π : Equiv.Perm (Fin (2^p)), Runs pub mac reconstruct bank mem es z mz ∧
      traceCost es ≤ GeometryAdviceRate.ticks t.size u (Total p d) w w ∧
      Schema.Buffers G (nEq ▸ fit) (mEq ▸ space) l.dest H (fun i => ((G.referenceRows pin).get i).2)
        (fun i => ((G.referenceRows pin).get i).1) (T.arguments args fields) (readings mz) π ∧
      ∀ bits fs, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,bank⟩ mem bits = some fs ↔
        fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  intro t input g args fields D G nEq mEq layout physical valid actual keys boxFit rowFit fits lit
  have rows (c : Fin C) : (D.cellRecords c).length < 2^w := (D.regroup_counts anchor rfl linked c).symm.trans_lt (rowFit c)
  obtain ⟨_,labels,argsOk,ok⟩ := (T.exists_liveFrame up T.chunkLabels.get).choose_spec.2
    input owner keys keysFit boxFit rows fits lit
  obtain ⟨words,rest⟩ := T.orderedPins_values up anchors baseOwner cap pad wide input owner anchor linked actual
    keys keysFit boxFit rows fits lit
  let sorted := T.orderedPins up anchors baseOwner cap pad
  have ids (i : Fin T.chunkLabels.length) : value (fun j => sorted.eval input (.inr (.inl (i,j)))) =
      ((G.referenceRows pin).get (i.cast mEq)).1.val := by
    have eqn := congrArg (fun ys : List (Fin C) => ys[i.val]?)
      ((T.chunkLabels_eval owner args fields pin).trans (D.regroup_owners anchor pin).symm)
    have bound : i.val < (G.referenceRows pin).length := (i.cast mEq).isLt
    change (T.chunkLabels.map (Sum.elim owner id))[i.val]? = ((G.referenceRows pin).map Prod.fst)[i.val]? at eqn
    simp only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem bound,
      Option.map_some,Option.some.injEq] at eqn
    exact (congrArg value (funext fun j => rest (.inl (i,j)))).trans ((labels i).trans (congrArg Fin.val eqn))
  obtain ⟨es,z,mz,π,run,time,buf,unique⟩ := Schema.execute_fixed fit space H (T.reference baseOwner pin)
    sorted pub mac bank mem f a L P l base start src pins x frameFits stripeFits keysFit sourceFit hd
    header one G pin nEq mEq (T.fixedReference_regroup baseOwner owner pin args fields anchor linked) layout physical
    ((rest _).trans (ok.trans valid)) words ids
  have he : (fun e => value fun j => sorted.eval input (.inr (.inr (.inl (e,j))))) = T.arguments args fields :=
    funext fun e => (congrArg value (funext fun j => rest (.inr (.inl (e,j))))).trans (argsOk e)
  exact ⟨es,z,mz,π,run,time,he ▸ buf,unique⟩

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI

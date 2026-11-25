import OAI.Computability.BorderVNP.CellPacketGeometryLiveTemplate
import OAI.Computability.BorderVNP.CellPacketGeometryGateBudget

/-! # The record and scalar pin frame for the native sparse packet initializer

The public row tape is generated from its shared arithmetic record-code frame.
A second shared stage computes the two owner histograms. The circuit and its
output pin numbering are fixed before the owner and operand values are supplied.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open VPVNP.VerifierNetwork Packing.BankPacket Packing.Word ParseBatchSort
open CellSparse CellSparse.Packet

variable {σ E I Orig : Type} [Fintype σ] [Fintype E] [Fintype I] {s C k w M : ℕ}

/-- Input frame containing the actual site labels, local scalar operands, validation
bit, and the geometry fields used by each typed site record emitter. -/
abbrev Base (s k w : ℕ) (E I : Type) := Input s k w E ⊕ (Fin s × I × Fin w)

private def rowSelect (T : Template E I Orig s C) :
    Input s k w T.Fields → Base s k w E I ⊕ (T.RowPin × Fin w)
  | .inl a => .inl (.inl (.inl a))
  | .inr (.inl (.inl e,j)) => .inl (.inl (.inr (.inl (e,j))))
  | .inr (.inl (.inr z,j)) => .inr (z,j)
  | .inr (.inr u) => .inl (.inl (.inr (.inr u)))

/-- Generate all tagged record words in parallel, including their physical base and
stride operands. All owner pins, scalar fields and the validity wire survive. -/
theorem Template.emitRows (T : Template E I Orig s C) (up : Frame σ (Base s k w E I)) :
    ∃ f : Frame σ (Input s k w T.Fields),
      f.size ≤ up.size + 1 + (∑ z : T.RowPin, (tape (T.format z.1))[z.2].nodes)*(100*(w+1)^2) ∧
      ∀ x, let g := up.eval x
        let args := fun e => value fun j => g (.inl (.inr (.inl (e,j))))
        let fields := fun i a => value fun j => g (.inr (i,a,j))
        (∀ z : T.RowPin, ((tape (T.format z.1))[z.2.val]).Fits w (fields z.1)) →
        (∀ i j, f.eval x (.inl (i,j)) = g (.inl (.inl (i,j)))) ∧
        (∀ e, value (fun j => f.eval x (.inr (.inl (e,j)))) = T.arguments args fields e) ∧
        f.eval x (.inr (.inr ())) = g (.inl (.inr (.inr ()))) := by
  classical
  let selector := Frame.initial (Sum.inr : Fin s × I × Fin w → Base s k w E I)
  obtain ⟨words,size,eval⟩ := exists_tapeFrame T.format w selector
  let f := (words.withInput.select (rowSelect T)).subst up
  refine ⟨f,?_,?_⟩
  · simpa [f,selector,Frame.subst_size,Nat.add_assoc] using Nat.add_le_add_left size up.size
  · intro x g args fields fit
    refine ⟨fun i j => ?_,fun e => ?_,?_⟩
    · simp [f,g,rowSelect]
    · cases e with
      | inl e => simp [f,g,args,rowSelect,Template.arguments]
      | inr z =>
        have hfields : (fun i => value (fun j => selector.eval g (z.1,i,j))) = fields z.1 := by
          funext i; simp [selector,fields]
        have he := eval g z (hfields.symm ▸ fit z)
        rw [hfields,←tape_eval] at he
        simpa [f,g,rowSelect,Template.arguments,List.getElem?_eq_getElem z.2.isLt] using he
    · simp [f,g,rowSelect]

/-- One fixed live geometry frame for every runtime site assignment and fitted set
of operands. It exposes the genuine public stream, chunk owner keys, all site slot
operands and the original profile validity result. -/
theorem Template.exists_liveFrame (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (chunk : Fin M → Owner s C) :
    ∃ f : Frame σ (Schema.Pins T.atoms.length M k w T.Fields),
      f.size ≤ up.size + 1 + (∑ z : T.RowPin, (tape (T.format z.1))[z.2].nodes)*(100*(w+1)^2) +
        2*histogramBudget s C k w + T.atoms.length*(k+w) + M*k + Fintype.card T.Fields*w + 1 ∧
      ∀ x (owner : Fin s → Fin C), let g := up.eval x
        let args := fun e => value fun j => g (.inl (.inr (.inl (e,j))))
        let fields := fun i a => value fun j => g (.inr (i,a,j))
        let D := T.directory owner args fields
        (∀ i, value (fun j => g (.inl (.inl (i,j)))) = (owner i).val) → C < 2^k →
        (∀ c, (D.cellBoxes c).length < 2^w) → (∀ c, (D.cellRecords c).length < 2^w) →
        (∀ z : T.RowPin, ((tape (T.format z.1))[z.2.val]).Fits w (fields z.1)) →
        (∀ i : Fin T.atoms.length, ∀ n, T.atoms[i.val].2 = .literal n → n < 2^w) →
        (∀ i : Fin T.atoms.length, (D.words[i.val]?).map (fun t => (t.1.val,t.2)) =
          some (value (fun j => f.eval x (.inl (i,.inl j))),value (fun j => f.eval x (.inl (i,.inr j))))) ∧
        (∀ i, value (fun j => f.eval x (.inr (.inl (i,j)))) = ((chunk i).elim owner id).val) ∧
        (∀ e, value (fun j => f.eval x (.inr (.inr (.inl (e,j))))) = T.arguments args fields e) ∧
        f.eval x (.inr (.inr (.inr ()))) = g (.inl (.inr (.inr ()))) := by
  classical
  obtain ⟨pre,ps,rows⟩ := T.emitRows up
  let boxes := fun i => (T.boxes i).length
  let num := fun i => (T.format i).length
  let data := fun i : Fin T.atoms.length => T.atoms[i.val]
  let f := frame pre boxes num data chunk
  refine ⟨f,?_,?_⟩
  · have h := frame_size pre boxes num data chunk
    dsimp only [f]
    omega
  intro x owner g args fields D keys small bf rf fit lit
  obtain ⟨prKeys,prArgs,valid⟩ := rows x fit
  have key (i) : value (fun j => pre.eval x (.inl (i,j))) = (owner i).val :=
    (congrArg value (funext (prKeys i))).trans (keys i)
  have boxesFit (c) : total owner boxes c < 2^w := by
    rw [show total owner boxes c = (D.cellBoxes c).length from merged_length ..]; exact bf c
  have rowsFit (c) : total owner num c < 2^w := by
    have eqn := merged_length owner (fun i => (T.format i).map (RecordCode.read (fields i))) c
    simp only [List.length_map] at eqn
    exact eqn.trans_lt (rf c)
  obtain ⟨hk,hw,hr,kept⟩ := frame_values pre boxes num data chunk x owner key small boxesFit rowsFit lit
  have stream := T.atoms_eval owner args fields
  have args' : (fun e => value (fun j => pre.eval x (.inr (.inl (e,j))))) = T.arguments args fields := funext prArgs
  refine ⟨fun i => ?_,hr,fun e => ?_,?_⟩
  · have eqn := congrArg (fun ls : List (Fin C × ℕ) => ls[i.val]?) stream
    rw [List.getElem?_map,List.getElem?_eq_getElem i.isLt, Option.map_some] at eqn
    change (D.words[i.val]?).map _ = _
    rw [← eqn, Option.map_some,hk,hw,args']
    rfl
  · exact (congrArg value (funext fun j => kept (.inl (e,j)))).trans (prArgs e)
  · exact (kept (.inr ())).trans valid

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI

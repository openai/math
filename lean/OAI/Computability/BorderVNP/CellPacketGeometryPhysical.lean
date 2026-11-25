import OAI.Computability.BorderVNP.CellPacketGeometryRanges
import OAI.Computability.BorderVNP.GeometryAdviceFrame
import OAI.Computability.BorderVNP.CellPacketChunk

/-! # Reading sorted packet sections from the physical geometry return

A fixed Boolean frame combines public-word sorting and its validity wire, and the
shared RAM evaluates it from the actual literal stripes. Section base and word count
are obtained from two positions in the return's own memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryFrameEncoding GeometryAdvice RoutingISA.CellPacket

variable {σ : Type*} [Fintype σ] {b k w u : ℕ}

/-- Join the runtime key/payload pin rows and upstream validity flag with one sort.
The dense output is the sorted payload bank followed by the inverse-address bank. -/
noncomputable def geometry (source : Frame σ (Stable.Input b k w ⊕ Unit)) :
    Frame σ (Outputs (2^b+2^b) w) :=
  let sorted := (sortedFrame b k w).subst (Frame.initial (Sum.inl : Stable.Input b k w → _ ⊕ Unit))
  (sorted.withInput.select (fun i : Outputs (2^b+2^b) w => i.elim
    (fun p => .inr (finSumFinEquiv.symm p.1,p.2)) (fun _ => .inl (.inr ())))).subst source

/-- No extra logic is needed to retain the validity flag or to number the two banks. -/
theorem geometry_size (source : Frame σ (Stable.Input b k w ⊕ Unit)) :
    (geometry source).size = source.size + (sortedFrame b k w).size := by
  simp [geometry,Frame.subst_size]

/-- The geometry stage preserves the source's own profile validity check. -/
theorem geometry_valid (source : Frame σ (Stable.Input b k w ⊕ Unit)) (x : σ → Bool) :
    (geometry source).eval x (.inr ()) = source.eval x (.inr ()) := by simp [geometry]

private theorem geometry_word (source : Frame σ (Stable.Input b k w ⊕ Unit)) (x : σ → Bool)
    (p : Bank b) (j : Fin w) :
    (geometry source).eval x (.inl (finSumFinEquiv p,j)) =
      (sortedFrame b k w).eval (fun i => source.eval x (.inl i)) (p,j) := by
  simp only [geometry, Frame.subst_eval, Frame.select_eval, Sum.elim_inl, Equiv.symm_apply_apply, Frame.withInput_eval_inr]
  congr 1
  funext i
  exact Frame.initial_eval _ _ _

/-- The two scalar loads required to address one section of the geometry output. -/
def sectionRange (mem : ℕ → ℕ) (dest : ℕ) (lo hi : Fin (2^b)) : ℕ × ℕ :=
  let l := mem (dest + (2^b+lo.val))
  let r := mem (dest + (2^b+hi.val))
  (dest+l+1,r-l-1)

/-- Reading a selected cell section from any two physical sort-result banks. -/
theorem range_read (key payload : Fin (2^b) → ℕ) (mem : ℕ → ℕ) (dest : ℕ)
    (π : Equiv.Perm (Fin (2^b))) (rank : Monotone fun i => 2*key (π i)*2^b+(π i).val)
    (words : ∀ i, mem (dest+i.val) = payload (π i))
    (locations : ∀ i, mem (dest+(2^b+i.val)) = (π.symm i).val)
    (lo hi : Fin (2^b)) (same : key lo = key hi) :
    (sectionRange mem dest lo hi).2 = (inside (key) lo hi).length ∧
    WordsAt mem (sectionRange mem dest lo hi).1 ((inside (key) lo hi).map (payload)) := by
  simp only [sectionRange,locations]
  refine ⟨interval_count _ π rank lo hi same,?_⟩
  rw [← inside_sorted _ π rank lo hi same,List.map_ofFn]
  intro j
  let i : Fin ((π.symm hi).val-(π.symm lo).val-1) := ⟨j.val,by simpa using j.isLt⟩
  have hw := words (innerIndex (π.symm lo) (π.symm hi) i)
  simpa [innerIndex,i,Nat.add_assoc] using hw

set_option maxRecDepth 4000 in
/-- Actual accepted RAM execution places every compact public packet interval at the
addresses read from its original marker rows. The assumptions are the striped literal
input, profile validity, and allocation bounds of the existing physical evaluator. -/
theorem execute_sections (source : Frame σ (Stable.Input b k w ⊕ Unit)) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : RoutingISA.Bank w) (m : Memory w) (f : BroadcastFrame)
    (a : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L) (l : GeometryOutput.Layout)
    (base start : ℕ) (src : Fin u → ℕ) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (fit : f.Fits w (pub 0).val) (space : a.Fits f w (pub 0).val) (positionsFit : 2^b ≤ 2^w) :
    let g := geometry source
    let t := compile g pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    let raw := fun i => source.eval input (.inl i)
    GeometryOutput.Placement pub l base start a.dense src t →
    PhysicalInput pub m f a L P l base start src t x →
    source.eval input (.inr ()) = true →
    ∃ es z mz, Runs pub mac reconstruct s m es z mz ∧
      traceCost es ≤ GeometryAdviceRate.ticks t.size u (2^b+2^b) w w ∧
      (∀ lo hi : Fin (2^b), Stable.key raw lo = Stable.key raw hi →
        (sectionRange (readings mz) l.dest lo hi).2 = (inside (Stable.key raw) lo hi).length ∧
        WordsAt (readings mz) (sectionRange (readings mz) l.dest lo hi).1
          ((inside (Stable.key raw) lo hi).map (Stable.weight raw))) ∧
      ∀ bits fs, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
        fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  intro g t input raw layout physical valid
  have accept : g.eval input (.inr ()) = true := (geometry_valid ..).trans valid
  obtain ⟨es,z,mz,run,ticks,output,unique⟩ :=
    (frame_execute pub mac s m f a L P l base start src g pins x fit space layout physical).2 accept
  obtain ⟨π,rank,payload,position⟩ := sortedFrame_values raw positionsFit
  have read (p : Bank b) : readings mz (l.dest+(finSumFinEquiv p).val) =
      value (fun j => (sortedFrame b k w).eval raw (p,j)) := by
    rw [readings,output]
    simp only [g,geometry_word,word,Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (value_lt _)
  refine ⟨es,z,mz,run,ticks,fun lo hi same => range_read (Stable.key raw) (Stable.weight raw) (readings mz) l.dest π rank
    (fun i => (read (.inl i)).trans (payload i)) (fun i => (read (.inr i)).trans (position i)) lo hi same,unique⟩

end CellPacketGeometry

end BorderVNP
end Computability
end OAI

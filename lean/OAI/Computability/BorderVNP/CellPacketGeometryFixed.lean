import OAI.Computability.BorderVNP.CellPacketGeometryReserved

/-! # Executing a fixed geometry gate table against the branch's sparse directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.Schema

open PackedHistogram ParseBatchSort Packing.Word VPVNP.VerifierNetwork GeometryFrameEncoding
open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryAdvice RoutingISA.CellPacket

variable {σ E S Orig : Type} [Fintype σ] [Fintype E] {C N M p d k w u : ℕ}

/-- A fixed gate table can be validated directly against the typed directory on
each input. Only the static reference operands must agree between branches.
Owner labels and numeric operands are evaluated by the shared source circuit. -/
theorem execute_fixed (fit : C+N+C ≤ 2^p) (space : C+(coords M).length+C ≤ 2^d)
    (H : ℕ) (refs : Fin M → Reference N E) (up : Frame σ (Pins N M k w E))
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : RoutingISA.Bank w) (m : Memory w)
    (f : BroadcastFrame) (a : Stripe) (L : RoutingISA.Pins.Layout) (P : RoutingISA.Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (frameFits : f.Fits w (pub 0).val) (stripeFits : a.Fits f w (pub 0).val)
    (keysFit : C < 2^k) (sourceFit : l.dest+2^p < 2^w) (hd : 2^d ≤ 2^w)
    (header : H < 2^w) (one : 1 < 2^w)
    (D : SiteWords.Directory S Orig C) (pin : Orig → E)
    (nEq : N = D.words.length) (mEq : M = (D.referenceRows pin).length)
    (same : ∀ i, (cast (congrArg (fun n => Reference n E) nEq) (refs i)) =
      ((D.referenceRows pin).get (i.cast mEq)).2) :
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    let t := compile (joint (source C p d up) (expression C d fit l.dest H refs)) pins
    GeometryOutput.Placement pub l base start a.dense src t →
    PhysicalInput pub m f a L P l base start src t x →
    up.eval input (.inr (.inr (.inr ()))) = true →
    (∀ i : Fin N, (D.words[i.val]?).map (fun z => (z.1.val,z.2)) =
      some (value (fun j => up.eval input (.inl (i,.inl j))),value (fun j => up.eval input (.inl (i,.inr j))))) →
    (∀ i : Fin M, value (fun j => up.eval input (.inr (.inl (i,j)))) =
      ((D.referenceRows pin).get (i.cast mEq)).1.val) →
    ∃ es z mz, ∃ π : Equiv.Perm (Fin (2^p)),
      Runs pub mac reconstruct s m es z mz ∧ traceCost es ≤ GeometryAdviceRate.ticks t.size u (Total p d) w w ∧
      Buffers D (nEq ▸ fit) (mEq ▸ space) l.dest H (fun i => ((D.referenceRows pin).get i).2)
        (fun i => ((D.referenceRows pin).get i).1)
        (fun e => value fun j => up.eval input (.inr (.inr (.inl (e,j))))) (readings mz) π ∧
      ∀ bits fs, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
        fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  subst N
  subst M
  have refs_eq : refs = fun i => ((D.referenceRows pin).get i).2 := funext same
  subst refs
  intro input t layout physical valid words owners
  have both i := words i
  simp only [List.getElem?_eq_getElem (Fin.isLt _),Option.map_some,Option.some.injEq,Prod.mk.injEq] at both
  exact execute_buffers D fit space H _ _ up pub mac s m f a L P l base start src pins x frameFits
    stripeFits keysFit sourceFit hd header one layout physical valid (fun i => (both i).1.symm)
    (fun i => (both i).2.symm) owners

end CellPacketGeometry.Schema

end BorderVNP
end Computability
end OAI

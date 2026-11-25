import OAI.Computability.BorderVNP.PackedBundleSort

/-! # Reading whole bottom-bundle headers from the geometry evaluator's return

The two marker ranks come from the RAM written by the physical geometry program.
Each cell's section contains exactly the six fields of its assigned source rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open CellPacketGeometry PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryFrameEncoding GeometryAdvice RoutingISA.CellPacket
open private geometry_word from OAI.Computability.BorderVNP.CellPacketGeometryPhysical

variable {σ : Type*} [Fintype σ] {C N b k w u : ℕ}

/-- The true output section bounds and words, read from physical returned memory. -/
structure SectionSpec (fit : C+6*N+C ≤ 2^b) (owner : Fin N → Fin C) (header : Fin N → BundleHeader)
    (mem : ℕ → ℕ) (dest : ℕ) : Prop where
  /-- All inverse rank words are legal addresses inside the returned payload bank. -/
  rankBound : ∀ i : Fin (2^b), mem (dest+(2^b+i.val)) < 2^b
  /-- The two rank words are strictly ordered even when the cell owns no bundles. -/
  markerOrder : ∀ c, mem (dest+(2^b+(Markers.start fit c).val)) < mem (dest+(2^b+(Markers.stop fit c).val))
  /-- Both bounds and all stored words agree with the stable cell subsequence. -/
  cell : ∀ c, let range := sectionRange mem dest (Markers.start fit c) (Markers.stop fit c)
    range.2 = (selected owner header c).length ∧ WordsAt mem range.1 (selected owner header c)

/-- Gate count of the full shared frame, including both forward sorting and restoring
marker addresses to source order. -/
theorem geometry_size_le (C b : ℕ) (up : Frame σ (Pins N k w)) :
    (geometry (source C b up)).size ≤ up.size + 2^b*(k+w) + 1 +
      (1 + 2^b * (((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) + (w+b) + b^2*(24*(w+b)+1))) :=
  (geometry_size _).le.trans (Nat.add_le_add (source_size C b up) (sortedFrame_size b k w))

/-- Read the same complete sections when the stable sort is one output block of a
larger joint geometry run. The hypothesis concerns only the physical scalar outputs. -/
theorem SectionSpec.of_words (up : Frame σ (Pins N k w)) (x : σ → Bool)
    (owner : Fin N → Fin C) (header : Fin N → BundleHeader)
    (rect : C+6*N+C ≤ 2^b) (keysFit : C < 2^k) (positionsFit : 2^b ≤ 2^w)
    (keys : ∀ i, value (fun j => up.eval x (.inl (i,.inl j))) = (owner i).val)
    (payload : ∀ i f, value (fun j => up.eval x (.inl (i,.inr (f,j)))) = scalar (header i) f)
    (mem : ℕ → ℕ) (dest : ℕ)
    (result : ∀ i : Fin (2^b+2^b), mem (dest+i.val) =
      value (fun j => (geometry (source C b up)).eval x (.inl (i,j)))) :
    SectionSpec rect owner header mem dest := by
  let raw := fun i => (source C b up).eval x (.inl i)
  obtain ⟨pk,pv,_⟩ := source_values (b := b) up x owner header keysFit keys payload
  obtain ⟨π,rank,values,positions⟩ := sortedFrame_values raw positionsFit
  have read (p : CellPacketGeometry.Bank b) : mem (dest+(finSumFinEquiv p).val) =
      value (fun j => (sortedFrame b k w).eval raw (p,j)) := by
    rw [result]
    simp only [geometry_word,raw]
  have loc (i : Fin (2^b)) : mem (dest+(2^b+i.val)) = (π.symm i).val :=
    (read (.inr i)).trans (positions i)
  have markerOrder (c : Fin C) : mem (dest+(2^b+(Markers.start rect c).val)) <
      mem (dest+(2^b+(Markers.stop rect c).val)) := by
    rw [loc,loc]
    apply Markers.start_lt_stop rect (fun z => owner (coord z).1) c π
    change Stable.key raw = _ at pk
    simpa only [pk] using rank
  refine ⟨fun i => (loc i).trans_lt (π.symm i).isLt,markerOrder,fun c => ?_⟩
  have same : Stable.key raw (Markers.start rect c) = Stable.key raw (Markers.stop rect c) := by
    change Stable.key raw = _ at pk
    rw [pk]; simp [Markers.key]
  obtain ⟨size,stored⟩ := range_read (Stable.key raw) (Stable.weight raw) mem dest π rank
    (fun i => (read (.inl i)).trans (values i)) loc (Markers.start rect c) (Markers.stop rect c) same
  let range := sectionRange mem dest (Markers.start rect c) (Markers.stop rect c)
  change range.2 = (inside (Stable.key raw) _ _).length at size
  change WordsAt mem range.1 ((inside (Stable.key raw) _ _).map (Stable.weight raw)) at stored
  change Stable.key raw = _ at pk
  change Stable.weight raw = _ at pv
  rw [pk,pv,inside_words rect owner header] at stored
  rw [pk] at size
  have len := congrArg List.length (inside_words rect owner header c)
  simp only [List.length_map] at len
  exact ⟨size.trans len,stored⟩

set_option maxRecDepth 4000 in
/-- The common geometry evaluator writes all stable bottom-bundle header sections and
their true marker addresses, with the usual unique accepted path and tick bound. -/
theorem execute_sections (up : Frame σ (Pins N k w)) (owner : Fin N → Fin C) (header : Fin N → BundleHeader)
    (rect : C+6*N+C ≤ 2^b) (keysFit : C < 2^k)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : RoutingISA.Bank w) (m : Memory w) (f : BroadcastFrame)
    (a : Stripe) (L : RoutingISA.Pins.Layout) (P : RoutingISA.Pins.ProcessorFields L) (l : GeometryOutput.Layout)
    (base start : ℕ) (src : Fin u → ℕ) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (fit : f.Fits w (pub 0).val) (space : a.Fits f w (pub 0).val) (positionsFit : 2^b ≤ 2^w) :
    let t := compile (geometry (source C b up)) pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    GeometryOutput.Placement pub l base start a.dense src t →
    PhysicalInput pub m f a L P l base start src t x →
    up.eval input (.inr ()) = true →
    (∀ i, value (fun j => up.eval input (.inl (i,.inl j))) = (owner i).val) →
    (∀ i f, value (fun j => up.eval input (.inl (i,.inr (f,j)))) = scalar (header i) f) →
    ∃ es z mz, Runs pub mac reconstruct s m es z mz ∧
      traceCost es ≤ GeometryAdviceRate.ticks t.size u (2^b+2^b) w w ∧
      SectionSpec rect owner header (readings mz) l.dest ∧
      ∀ bits fs, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
        fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  intro t input layout physical accepted keys values
  have hv := (source_values (b := b) up input owner header keysFit keys values).2.2
  let g := geometry (source C b up)
  have accept : g.eval input (.inr ()) = true := (geometry_valid ..).trans (hv.trans accepted)
  obtain ⟨es,z,mz,run,ticks,output,unique⟩ :=
    (frame_execute pub mac s m f a L P l base start src g pins x fit space layout physical).2 accept
  refine ⟨es,z,mz,run,ticks,SectionSpec.of_words up input owner header rect keysFit positionsFit keys values
    (readings mz) l.dest (fun i => ?_),unique⟩
  rw [readings,output]
  exact Nat.mod_eq_of_lt (value_lt _)

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI

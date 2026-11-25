import OAI.Computability.BorderVNP.CellPacketGeometryArrays

/-! # Physical geometry reconstruction for the typed packet source layout

One evaluation from the striped geometry tape constructs both arrays. Each cell's
natural words and its chunk table have actual absolute RAM addresses obtained from
its two fixed marker pairs. The validity input and accepted trace are the original
geometry frame's, and the cost counts both sorts and every addressed output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.Schema

open PackedHistogram ParseBatchSort Packing.Word VPVNP.VerifierNetwork GeometryFrameEncoding
open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryAdvice RoutingISA.CellPacket

variable {σ E S Orig : Type} [Fintype σ] [Fintype E] {C p d k w u M : ℕ}

/-- Rank, source data, descriptor data, and lengths of the geometry output in one
team's true RAM. All word fields include their actual current owner key. -/
structure Buffers (D : SiteWords.Directory S Orig C) (fit : C+D.words.length+C ≤ 2^p)
    (space : C+(coords M).length+C ≤ 2^d) (dest H : ℕ) (refs : Fin M → Reference D.words.length E)
    (own : Fin M → Fin C) (arg : E → ℕ) (mem : ℕ → ℕ) (π : Equiv.Perm (Fin (2^p))) : Prop where
  /-- The forward permutation preserves stable source order. -/
  sorted : Monotone fun i => 2*Markers.key (fun z : Fin D.words.length => D.words[z.val].1)
    (Markers.row C D.words.length (π i).val)*2^p+(π i).val
  /-- Inverse positions used by the private chunk address encoder. -/
  positions : ∀ i, mem (dest+(2^p+i.val)) = (π.symm i).val
  /-- The sorted natural-word stream before private strings are inserted. -/
  publicWords : ∀ c, let range := sectionRange mem dest (Markers.start fit c) (Markers.stop fit c)
    let words := (CellSparse.Packet.Source.plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c)
      (D.reports c)).flatMap CellSparse.Packet.Source.Part.publicBuffer
    range.2 = words.length ∧ WordsAt mem range.1 words
  /-- Actual ordered three-word chunk records; the final reservations are present. -/
  chunks : ∀ c, let range := sectionRange mem (descriptorBank dest p) (Markers.start space c) (Markers.stop space c)
    let selected := ((List.finRange M).filter fun i => decide (own i=c)).map refs
    let rows := selected.flatMap (Reference.values fit dest H (Sum.elim arg (fun j => (π.symm j).val)))
    range.2 = 3*selected.length ∧ WordsAt mem range.1 rows

omit [Fintype E] in
private theorem values_length {N : ℕ} (fit : C+N+C ≤ 2^p) (dest H : ℕ)
    (op : E ⊕ Fin (2^p) → ℕ) (xs : List (Reference N E)) :
    (xs.flatMap (Reference.values fit dest H op)).length = 3*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Reference.values]; omega

set_option maxRecDepth 5000 in
/-- Execute the shared public frame with the concrete marker and descriptor wiring.
The source hypotheses refer only to the individual upstream geometry pins. In
particular the team starts without either completed packet-source RAM array. -/
theorem execute_buffers (D : SiteWords.Directory S Orig C) (fit : C+D.words.length+C ≤ 2^p)
    (space : C+(coords M).length+C ≤ 2^d) (H : ℕ) (refs : Fin M → Reference D.words.length E)
    (own : Fin M → Fin C) (upstream : Frame σ (Pins D.words.length M k w E)) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : RoutingISA.Bank w) (m : Memory w) (f : BroadcastFrame)
    (a : Stripe) (L : RoutingISA.Pins.Layout) (P : RoutingISA.Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (frameFits : f.Fits w (pub 0).val) (stripeFits : a.Fits f w (pub 0).val)
    (keysFit : C < 2^k) (sourceFit : l.dest+2^p < 2^w) (hd : 2^d ≤ 2^w)
    (header : H < 2^w) (one : 1 < 2^w) :
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    let srcFrame := source C p d upstream
    let expressions := expression C d fit l.dest H refs
    let t := compile (joint srcFrame expressions) pins
    GeometryOutput.Placement pub l base start a.dense src t →
    PhysicalInput pub m f a L P l base start src t x →
    upstream.eval input (.inr (.inr (.inr ()))) = true →
    (∀ i : Fin D.words.length, value (fun j => upstream.eval input (.inl (i,.inl j))) = D.words[i.val].1.val) →
    (∀ i : Fin D.words.length, value (fun j => upstream.eval input (.inl (i,.inr j))) = D.words[i.val].2) →
    (∀ i : Fin M, value (fun j => upstream.eval input (.inr (.inl (i,j)))) = (own i).val) →
    ∃ es z mz, ∃ π : Equiv.Perm (Fin (2^p)),
      Runs pub mac reconstruct s m es z mz ∧
      traceCost es ≤ GeometryAdviceRate.ticks t.size u (Total p d) w w ∧
      Buffers D fit space l.dest H refs own
        (fun e => value fun j => upstream.eval input (.inr (.inr (.inl (e,j))))) (readings mz) π ∧
      ∀ bits fs, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
        fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  intro input srcFrame expressions t layout physical accepted pw words pr
  let up := srcFrame.eval input
  let raw := fun i => up (.inl i)
  let owner := fun i : Fin D.words.length => D.words[i.val].1
  let down := fun q : Fin (coords M).length => own ((coords M)[q.val]).1
  let arg := fun e => value (fun j => upstream.eval input (.inr (.inr (.inl (e,j)))))
  obtain ⟨pkey,pword,dkey,rest⟩ := source_values (p := p) (d := d) upstream input owner own keysFit pw pr
  have hp : 2^p ≤ 2^w := by omega
  have valid : up (.inr (.inr (.inr ()))) = true := (rest _).trans accepted
  have safe (π : Equiv.Perm (Fin (2^p))) (i : Fin (2^d)) := expression_fits fit l.dest H refs up π i sourceFit header one
  obtain ⟨es,z,mz,π,run,ticks,rank,pos,pu,de,unique⟩ := execute_directory srcFrame expressions
    pub mac s m f a L P l base start src pins x frameFits stripeFits hp hd layout physical valid safe
  have pk : Stable.key raw = fun i => Markers.key owner (Markers.row C D.words.length i.val) := funext pkey
  have pv : Stable.weight raw = fun i => Markers.word (fun j : Fin D.words.length => D.words[j.val].2)
      (Markers.row C D.words.length i.val) := funext fun i => (pword i).trans
        (congrArg (fun g => Markers.word g (Markers.row C D.words.length i.val)) (funext words))
  have dk : (fun i : Fin (2^d) => value fun j => up (.inr (.inl (i,j)))) =
      fun i => Markers.key down (Markers.row C (coords M).length i.val) := funext dkey
  change Monotone (fun i => 2*Stable.key raw (π i)*2^p+(π i).val) at rank
  rw [pk] at rank
  have op : operands up π = Sum.elim arg (fun j => (π.symm j).val) := by
    funext e
    cases e with
    | inl a => exact congrArg value (funext fun j => rest (.inl (a,j)))
    | inr j => rfl
  refine ⟨es,z,mz,π,run,ticks,⟨rank,pos,?_,?_⟩,unique⟩
  · intro c
    have same : Stable.key raw (Markers.start fit c) = Stable.key raw (Markers.stop fit c) := by rw [pk]; simp [Markers.key]
    obtain ⟨size,stored⟩ := pu _ _ same
    change WordsAt (readings mz) _ ((inside (Stable.key raw) _ _).map (Stable.weight raw)) at stored
    change _ = (inside (Stable.key raw) _ _).length at size
    rw [pk,pv,publicArray] at stored
    rw [pk] at size
    have len := congrArg List.length (publicArray D fit c)
    simp only [List.length_map] at len
    exact ⟨size.trans len,stored⟩
  · intro c
    let K := fun i : Fin (2^d) => value (fun j => up (.inr (.inl (i,j))))
    let A := Markers.start space c
    let B := Markers.stop space c
    change K = _ at dk
    have same : K A = K B := by rw [dk]; simp [A,B,Markers.key]
    obtain ⟨size,stored⟩ := de A B same
    change WordsAt (readings mz) _ ((inside K A B).map (fun i => (expressions i).eval (operands up π))) at stored
    change _ = (inside K A B).length at size
    rw [dk,op] at stored
    have selected := descriptorSection fit space l.dest H own refs c (Sum.elim arg (fun j => (π.symm j).val))
    rw [selected] at stored
    rw [dk] at size
    have len := congrArg List.length selected
    simp only [List.length_map,values_length] at len
    exact ⟨by simpa only [List.length_map] using size.trans len,stored⟩

end CellPacketGeometry.Schema

end BorderVNP
end Computability
end OAI

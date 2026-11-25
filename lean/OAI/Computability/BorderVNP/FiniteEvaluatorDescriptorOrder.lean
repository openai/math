import OAI.Computability.BorderVNP.CellPacketGeometryOrderedBuffer

/-! # The real inverse descriptor-sort ranks respect the physical cell order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open PackedHistogram ParseBatchSort Packing.Word VPVNP.VerifierNetwork GeometryFrameEncoding
open private field keyPin natBit from OAI.Computability.BorderVNP.CellPacketGeometrySchema
open private key_mono from OAI.Computability.BorderVNP.CellPacketGeometryRanges

/-- Ranks in the returned inverse chunk sort, at the two marker indices for
every cell (including the spare). -/
structure DescriptorRanks (C stops db bank : ℕ) (mem : ℕ → ℕ) : Prop where
  startBound : ∀ c : Fin C, mem (bank+(2^db+c.val))<2^db
  stopBound : ∀ c : Fin C, mem (bank+(2^db+(stops+c.val)))<2^db
  separate : ∀ a b : Fin C, a<b →
    mem (bank+(2^db+(stops+a.val))) < mem (bank+(2^db+b.val))

/-- Both physical inverse-sort banks, including the public-word bound needed
when scanning the immutable public buffer up to the descriptor bank. -/
structure PacketRanks (C stops p d dest : ℕ) (mem : ℕ → ℕ) : Prop
    extends DescriptorRanks C stops d (descriptorBank dest p) mem where
  publicBound : ∀ j : Fin (2^p), mem (dest+(2^p+j.val))<2^p

/-- The complete ranks survive later writes when the real inverse-sort words
are retained. The only capacity used here is the fixed size of that sort. -/
theorem DescriptorRanks.readback {C stops d bank : ℕ} {first last : ℕ → ℕ}
    (rank : DescriptorRanks C stops d bank first) (space : stops+C≤2^d)
    (agree : ∀ j : Fin (2^d), last (bank+(2^d+j.val))=first (bank+(2^d+j.val))) :
    DescriptorRanks C stops d bank last := by
  have start (c : Fin C) := agree ⟨c.val,by have := c.isLt; omega⟩
  have stop (c : Fin C) := agree ⟨stops+c.val,by have := c.isLt; omega⟩
  refine ⟨fun c => (start c).trans_lt (rank.startBound c),fun c => (stop c).trans_lt (rank.stopBound c),?_⟩
  intro a b less
  exact (stop a).trans_lt ((rank.separate a b less).trans_eq (start b).symm)

namespace Schema

variable {σ E : Type} [Fintype σ] [Fintype E] {C N M k w p d : ℕ}

/-- Marker keys are hardwired to the cell ordinal. No hypothesis on the
data keys or the private descriptors is needed for their inverse ranks. -/
theorem packet_marker_ranks_of_output (fit : C+N+C≤2^p) (space : C+(coords M).length+C≤2^d)
    (dest H : ℕ) (refs : Fin M → Reference N E) (upstream : Frame σ (Pins N M k w E)) (x : σ → Bool)
    (keysFit : C<2^k) (sourceFit : dest+2^p<2^w) (hd : 2^d≤2^w) (header : H<2^w) (one : 1<2^w)
    (mem : ℕ → ℕ)
    (output : ∀ i : Fin (Total p d), mem (dest+i.val)=value (fun j =>
      (joint (source C p d upstream) (expression C d fit dest H refs)).eval x (.inl (i,j)))) :
    PacketRanks C (C+(coords M).length) p d dest mem := by
  let frame := source C p d upstream
  let up := frame.eval x
  let key := fun i : Fin (2^d) => value fun j => up (.inr (.inl (i,j)))
  obtain ⟨π,_,_,publicRanks,second⟩ := joint_values frame (expression C d fit dest H refs) x (by omega) hd
  obtain ⟨τ,order,_,inverse⟩ := second (fun i => expression_fits fit dest H refs up π i sourceFit header one)
  have ranks (i : Fin (2^d)) : mem (descriptorBank dest p+(2^d+i.val))=(τ.symm i).val := by
    simpa only [descriptorBank,Nat.add_assoc,outputIndex,Sum.map_inr,finSumFinEquiv_apply_right,Fin.val_natAdd]
      using (output (outputIndex (.inr (.inr i)))).trans (inverse i)
  have left (c : Fin C) : key (Markers.start space c)=c.val := by
    simp [key,up,frame,source,Frame.step_eval,field,keyPin,natBit,
      BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval,
      Nat.mod_eq_of_lt (c.isLt.trans keysFit)]
  have right (c : Fin C) : key (Markers.stop space c)=c.val := by
    simp [key,up,frame,source,Frame.step_eval,field,keyPin,natBit,
      BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval,
      Nat.mod_eq_of_lt (c.isLt.trans keysFit)]
  constructor
  swap
  · intro j
    exact ((output (outputIndex (.inl (.inr j)))).trans (publicRanks j)).trans_lt (π.symm j).isLt
  refine ⟨fun c => (ranks (Markers.start space c)) ▸ (τ.symm (Markers.start space c)).isLt,
    fun c => (ranks (Markers.stop space c)) ▸ (τ.symm (Markers.stop space c)).isLt,?_⟩
  intro a b less
  change mem (_+(2^d+(Markers.stop space a).val)) < mem (_+(2^d+(Markers.start space b).val))
  rw [ranks,ranks]
  by_contra! bad
  have rev := key_mono key τ order (show τ.symm (Markers.start space b)≤τ.symm (Markers.stop space a) from bad)
  simp only [Function.comp_apply,Equiv.apply_symm_apply,left,right] at rev
  exact (Nat.not_le_of_gt less) rev

end Schema

namespace LiveWords

open Packing.BankPacket

variable {σ E I Orig : Type} [Fintype σ] [Fintype E] [Fintype I] {s C q k w : ℕ}

/-- The native site-major directory inherits these ranks without assumptions on
the current branch's records, strings, or owners. -/
theorem Template.ordered_descriptor_ranks (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields)
    (pad : s<2^q) (dest H : ℕ) (x : σ → Bool) (keysFit : C<2^k)
    (sourceFit : dest+2^T.publicDepth<2^w) (hd : 2^T.chunkDepth≤2^w) (header : H<2^w) (one : 1<2^w)
    (mem : ℕ → ℕ) (output : ∀ i : Fin (Total T.publicDepth T.chunkDepth), mem (dest+i.val)=
      value (fun j => (T.orderedFrame up anchors baseOwner pin pad dest H).eval x (.inl (i,j)))) :
    PacketRanks C (C+(Schema.coords T.chunkLabels.length).length) T.publicDepth T.chunkDepth dest mem :=
  Schema.packet_marker_ranks_of_output T.sort_rooms.1 T.sort_rooms.2.1 dest H (T.reference baseOwner pin)
    (T.orderedPins up anchors baseOwner T.sort_rooms.2.2 pad) x keysFit sourceFit hd header one mem output

end LiveWords

namespace History.Native

open Packing.Inherited FrozenTape LiveWords CellSparse Packet GeometryFrameEncoding

variable {a C cap k w d t q : ℕ} {R B U V E Orig σ : Type}
variable [Fintype R] [Fintype B] [Fintype U] [Fintype V] [Fintype E] [Fintype σ]

/-- Read the sorted descriptor ranks from the same retained terminal bus that
produces the finite evaluator's cell packet. The record payload and the
private geometry may vary arbitrarily between returned histories. -/
theorem Feeds.ordered_descriptor_ranks (F : Feeds σ R B U V E a d t k w)
    (S : FrozenTape.Schema R B) (L : FrozenTape.Schema U V) (boxes : Fin a → List (Source.Box Orig))
    (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ u, (L.tags u).length≤cap)
    (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E))
    (hd : d≤q) (ht : t≤q) (room : a<2^q) (keysFit : C+1<2^k)
    (hs : ∀ r, S.width r≤w) (hl : ∀ u, L.width u≤w)
    (base : Fin (roster a S L).length → Fin (C+1)) (pointer : Orig → (template S L boxes sh lh priv rep).Fields)
    (pad : (roster a S L).length<2^q) (dest H : ℕ) (x : σ → Bool) (mem : ℕ → ℕ)
    (sourceFit : dest+2^(template S L boxes sh lh priv rep).publicDepth<2^w)
    (descFit : 2^(template S L boxes sh lh priv rep).chunkDepth≤2^w) (header : H<2^w) (one : 1<2^w)
    (output : ∀ i : Fin (Total (template S L boxes sh lh priv rep).publicDepth (template S L boxes sh lh priv rep).chunkDepth),
      mem (dest+i.val)=value (fun j => (F.ordered S L boxes sh lh priv rep hd ht room
        (Nat.lt_trans (Nat.lt_succ_self C) keysFit) hs hl base pointer pad dest H).eval x (.inl (i,j)))) :
    let T := template S L boxes sh lh priv rep
    PacketRanks (C+1) (C+1+(CellPacketGeometry.Schema.coords T.chunkLabels.length).length)
      T.publicDepth T.chunkDepth dest mem := by
  let croom := Nat.lt_trans (Nat.lt_succ_self C) keysFit
  let upstream := source (cap := cap) S L (access : Access R B U V E (Bundle R B U V E a d t k w) a d t k w)
    hd ht room croom hs hl
  let origin := anchors S L (access : Access R B U V E (Bundle R B U V E a d t k w) a d t k w) hd ht room
  apply (template S L boxes sh lh priv rep).ordered_descriptor_ranks upstream origin base pointer pad dest H
    (F.frame.eval x) keysFit sourceFit descFit header one mem
  intro i
  exact (output i).trans (congrArg value (funext fun j => F.ordered_eval S L boxes sh lh priv rep hd ht room
    (Nat.lt_trans (Nat.lt_succ_self C) keysFit) hs hl base pointer pad dest H x (.inl (i,j))))

end History.Native

end CellPacketGeometry

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.CellPacketGeometryBufferedOutput
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryFeeds

/-! # Site-major typed buffers in a combined native geometry output -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open PackedHistogram ParseBatchSort Packing.Word Packing.BankPacket VPVNP.VerifierNetwork GeometryFrameEncoding
open private field from OAI.Computability.BorderVNP.CellPacketGeometrySchema

variable {σ E I Orig : Type} [Fintype σ] [Fintype E] [Fintype I] {s C q k w : ℕ}
variable (T : Template E I Orig s C) (up : Frame σ (Base s k w E I)) (anchors : Frame σ (Fin s × Fin q))
variable (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields) (pad : s<2^q) (dest H : ℕ) (x : σ → Bool)
variable (owner : Fin s → Fin C) (anchor : Fin s → Fin s) (linked : ∀ i, owner (anchor i)=owner i)

private noncomputable abbrev runtimeArgs (e : E) := value fun j : Fin w => up.eval x (.inl (.inr (.inl (e,j))))
private noncomputable abbrev runtimeFields (i : Fin s) (e : I) := value fun j : Fin w => up.eval x (.inr (i,e,j))
private noncomputable abbrev branchDirectory := (T.directory owner (runtimeArgs up x) (runtimeFields up x)).regroup anchor

local notation3 "g₀" => up.eval x
local notation3 "args₀" => fun (e : E) => value fun (j : Fin w) => (g₀) (.inl (.inr (.inl (e,j))))
local notation3 "fields₀" => fun (i : Fin s) (e : I) => value fun (j : Fin w) => (g₀) (.inr (i,e,j))
local notation3 "D₀" => T.directory owner (args₀) (fields₀)
local notation3 "G₀" => (D₀).regroup anchor
local notation3 "sorted₀" => T.orderedPins up anchors baseOwner T.sort_rooms.2.2 pad

include linked in
private theorem wordExtent : T.atoms.length=(G₀).words.length :=
  (((D₀).regroup_wordCapacity anchor rfl linked).trans (T.wordCapacity owner (args₀) (fields₀))).symm

private theorem chunkExtent : T.chunkLabels.length=((G₀).referenceRows pin).length := by
  simpa only [List.length_map] using congrArg List.length
    ((T.chunkLabels_eval owner (args₀) (fields₀) pin).trans ((D₀).regroup_owners anchor pin).symm)

variable (wide : 2^T.recordDepth ≤ 2^(w+k)) (keysFit : C<2^k)
variable (actual : ∀ i : Fin s, value (fun j : Fin q => anchors.eval x (i,j))=(anchor i).val)
variable (keys : ∀ i : Fin s, value (fun j : Fin k => up.eval x (.inl (.inl (i,j))))=(owner i).val)
variable (boxFit : ∀ c : Fin C, ((branchDirectory T up x owner anchor).cellBoxes c).length<2^w)
variable (rowFit : ∀ c : Fin C, ((branchDirectory T up x owner anchor).cellRecords c).length<2^w)
variable (fits : ∀ z : T.RowPin, ((tape (T.format z.1))[z.2.val]).Fits w (runtimeFields up x z.1))
variable (lit : ∀ i : Fin T.atoms.length, ∀ n, T.atoms[i.val].2=.literal n → n<2^w)

include linked wide keysFit actual keys boxFit rowFit fits lit in
private theorem ordered_inputs :
    (∀ i : Fin T.atoms.length, ((G₀).words[i.val]?).map (fun z => (z.1.val,z.2)) =
      some (SiteSort.pair ((sorted₀).eval x) i)) ∧
    (∀ i : Fin T.chunkLabels.length, value (fun j => (sorted₀).eval x (.inr (.inl (i,j)))) =
      (((G₀).referenceRows pin).get (i.cast (chunkExtent T up pin x owner anchor))).1.val) ∧
    (fun e => value fun j => (sorted₀).eval x (.inr (.inr (.inl (e,j))))) = T.arguments (args₀) (fields₀) ∧
    (sorted₀).eval x (.inr (.inr (.inr ()))) = (g₀) (.inl (.inr (.inr ()))) := by
  have rows (c : Fin C) := ((D₀).regroup_counts anchor rfl linked c).symm.trans_lt (rowFit c)
  obtain ⟨_,labels,argsOk,ok⟩ := (T.exists_liveFrame up T.chunkLabels.get).choose_spec.2
    x owner keys keysFit boxFit rows fits lit
  obtain ⟨words,rest⟩ := T.orderedPins_values up anchors baseOwner T.sort_rooms.2.2 pad wide x owner anchor linked
    actual keys keysFit boxFit rows fits lit
  refine ⟨words,?_,funext (fun e => (congrArg value (funext fun j => rest (.inr (.inl (e,j))))).trans (argsOk e)),
    (rest _).trans ok⟩
  intro i
  have h := congrArg (fun ys : List (Fin C) => ys[i.val]?)
    ((T.chunkLabels_eval owner (args₀) (fields₀) pin).trans ((D₀).regroup_owners anchor pin).symm)
  have bound : i.val < ((G₀).referenceRows pin).length := (i.cast (chunkExtent T up pin x owner anchor)).isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem bound,
    Option.map_some,Option.some.injEq] at h
  exact (congrArg value (funext fun j => rest (.inl (i,j)))).trans ((labels i).trans (congrArg Fin.val h))

include linked wide keysFit actual keys boxFit rowFit fits lit in
/-- The validity output of the site-major frame is the validity bit of the real
upstream geometry. It is available even before its word banks are emitted. -/
theorem Template.ordered_valid :
    (T.orderedFrame up anchors baseOwner pin pad dest H).eval x (.inr ()) = (g₀) (.inl (.inr (.inr ()))) := by
  have h := (ordered_inputs T up anchors baseOwner pin pad x owner anchor linked wide keysFit actual keys
    boxFit rowFit fits lit).2.2.2
  unfold Template.orderedFrame
  rw [joint_valid]
  exact (Frame.step_eval ..).trans h

include linked wide keysFit actual keys boxFit rowFit fits lit in
/-- A combined native emitter which publishes every word of this one Boolean
frame at the stated addresses supplies the genuine typed site-major buffers,
with the canonical three sort depths of the template. -/
theorem Template.ordered_buffers (sourceFit : dest+2^T.publicDepth<2^w) (hd : 2^T.chunkDepth≤2^w)
    (header : H<2^w) (one : 1<2^w) (mem : ℕ → ℕ)
    (output : ∀ i : Fin (Total T.publicDepth T.chunkDepth), mem (dest+i.val) =
      value (fun j => (T.orderedFrame up anchors baseOwner pin pad dest H).eval x (.inl (i,j)))) :
    ∃ π : Equiv.Perm (Fin (2^T.publicDepth)), Schema.Buffers (G₀)
      (wordExtent T up x owner anchor linked ▸ T.sort_rooms.1) (chunkExtent T up pin x owner anchor ▸ T.sort_rooms.2.1)
      dest H (fun i => (((G₀).referenceRows pin).get i).2) (fun i => (((G₀).referenceRows pin).get i).1)
      (T.arguments (args₀) (fields₀)) mem π := by
  obtain ⟨words,ids,argsEq,_⟩ := ordered_inputs T up anchors baseOwner pin pad x owner anchor linked wide keysFit
    actual keys boxFit rowFit fits lit
  obtain ⟨π,buf⟩ := Schema.fixed_buffers_of_output T.sort_rooms.1 T.sort_rooms.2.1 dest H
    (T.reference baseOwner pin) (sorted₀) x keysFit sourceFit hd header one (G₀) pin
    (wordExtent T up x owner anchor linked) (chunkExtent T up pin x owner anchor)
    (T.fixedReference_regroup baseOwner owner pin (args₀) (fields₀) anchor linked) words ids mem output
  exact ⟨π,argsEq ▸ buf⟩

end CellPacketGeometry.LiveWords

namespace CellPacketGeometry.History.Native

open Packing.Inherited FrozenTape VPVNP.VerifierNetwork LiveWords CellSparse Packet GeometryFrameEncoding

variable {a C cap k w d t q : ℕ} {R B U V E Orig σ : Type}
variable [Fintype R] [Fintype B] [Fintype U] [Fintype V] [Fintype E] [Fintype σ]

/-- Read any published word bit or the validity bit of the ordered packet bank
from the true retained feed frame of the single native emitter. -/
theorem Feeds.ordered_eval (F : Feeds σ R B U V E a d t k w)
    (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
    (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ u, (L.tags u).length≤cap)
    (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E))
    (hd : d≤q) (ht : t≤q) (room : a<2^q) (croom : C<2^k)
    (hs : ∀ r, S.width r≤w) (hl : ∀ u, L.width u≤w)
    (base : Fin (roster a S L).length → Fin (C+1)) (pointer : Orig → (template S L boxes sh lh priv rep).Fields)
    (pad : (roster a S L).length<2^q) (dest H : ℕ) (x : σ → Bool) (z) :
    (F.ordered S L boxes sh lh priv rep hd ht room croom hs hl base pointer pad dest H).eval x z =
    ((template S L boxes sh lh priv rep).orderedFrame
      (source (cap := cap) S L access hd ht room croom hs hl) (anchors S L access hd ht room)
      base pointer pad dest H).eval (F.frame.eval x) z :=
  Frame.subst_eval ..

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI

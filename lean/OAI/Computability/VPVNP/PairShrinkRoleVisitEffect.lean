import OAI.Computability.VPVNP.PairShrinkRoleScheduledSuffix

/-!
# Private memory of a scheduled shrinking visit

On the encoding of a kernel witness, the field readers write the preceding
sites' argument packets and then the owned hidden words. The resident maps run
on the projection of these two native store sequences, with an arbitrary tape
suffix and arbitrary initial private memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression Compression.ShrinkMotif CompressorRecords NetworkKernel
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess
open private stored from OAI.Computability.VPVNP.PairShrinkRoleHidden
open private layout supplyWidth from OAI.Computability.VPVNP.PairShrinkRoleMapWitness

variable {w n : ℕ}

/-- The hidden reader's scratch is the projection of the ordered native row stores
for any full private memory representing its entry scratch. -/
theorem hiddenReader_stores (arg : Args w) (m : Memory w) (seed : List Row) (node : Word w)
    (priv : Word w → Word w) (bits tail : List Bool) (out : Outcome w n (List Row))
    (hit : hiddenReader arg m seed node (scratch n priv) bits = some (out, tail)) :
    out.updated = scratch n (storeRows arg.scratchBase arg.slotStride out.value priv) := by
  unfold hiddenReader at hit
  split at hit
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hit)
    rw [stored, scratch_storePackets]
  · contradiction

variable {a g : ℕ} {X : State a g}

private theorem visit_effect (A : Arena) (inc : IncidenceDirectory w) (m : Memory w)
    (older cap : ℕ) (desc : Word w → ChildArguments.Descriptor w X)
    (arg : Args w) (seed : List Row)
    (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w n))
    (cs hs ms : Setup w n) (node : Word w) (priv : Word w → Word w)
    (xs : List (Child X)) (qs : List Packet) (es : List Row) (bits hidBits tail : List Bool)
    (c : Outcome w n (List (Child X))) (h : Outcome w n (List Row))
    (childRead : ChildArguments.reader A inc m older cap desc node (scratch n priv)
      bits = some (c, hidBits))
    (childValue : c.value = xs) (childStore : c.updated = scratch n (storePackets A qs priv))
    (hiddenRead : hiddenReader arg m seed node (scratch n (storePackets A qs priv)) hidBits =
      some (h, tail)) (hiddenValue : h.value = es)
    (childSetup : cs.updated node (scratch n priv) = scratch n priv)
    (hiddenSetup : hs.updated node c.updated = c.updated)
    (mapSetup : ms.updated node h.updated = h.updated) :
    ((hook (visitReader A inc m older cap desc (fun _ => arg) (fun _ => seed) maps
      cs (fun _ => hs) (fun _ _ => ms))).read node (scratch n priv) bits).map
        (fun (j, rest) => (j.update (scratch n priv), rest)) =
      (ResidentMapLoop.Exact.scan node (maps xs es)
        (scratch n (storeRows arg.scratchBase arg.slotStride es (storePackets A qs priv)))).map
          (fun (_, final) => (final, tail)) := by
  have written := hiddenReader_stores arg m seed node (storePackets A qs priv) hidBits tail h
    hiddenRead
  rw [hiddenValue] at written
  have hid : hiddenReader arg m seed node c.updated hidBits = some (h, tail) :=
    childStore ▸ hiddenRead
  simp only [hook, visitReader, bind, Setup.reader, childSetup, childRead, hiddenSetup, hid,
    childValue, hiddenValue, mapSetup, ResidentMapLoop.Exact.mapReader, Option.map_map]
  rw [written]
  cases ResidentMapLoop.Exact.scan node (maps xs es)
    (scratch n (storeRows arg.scratchBase arg.slotStride es (storePackets A qs priv))) <;> rfl

variable {K R : Type*} [Field K] [CommRing R] {S : BlockSchedule K} (B : S.Templates)
  (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
  (Z : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
  (sel : Z.ShrinkSelection B.shrink)
  (v : (Z.Base × BitWord (packingTagBits (2 ^ S.degreeExponent i.castSucc))) × BitWord g)

private noncomputable abbrev term := (B.shrinkPassAt f hf i rfl Z).step.term sel
local notation "Tr" => term B f hf i Z sel
private noncomputable abbrev parser := (shrinkPassReaders B f hf i rfl Z).termParsers sel
local notation "rdr" => parser B f hf i Z sel
private noncomputable abbrev childOrder := (rdr).order.children v
local notation "ord" => childOrder B f hf i Z sel v
local notation "rowsAt" => ShrinkHiddenSlots.rows Z (layout B i Z sel) (supplyWidth B i Z sel) v

set_option maxHeartbeats 2000000 in
-- Identifying the encoded kernel reduces its dependent scheduled witness and reader.
/-- The scratch returned by the physical hook on a witness prefix is exactly the
resident scan's output on that witness's child packets and absorbed field rows.
This equality covers rejection by any map in the scan. -/
theorem scheduledVisitEffect (old : Placed (Tr).place Z.network.Half v)
    (new : (Tr).output.Half v) (k : ((rdr).witness v old new).Choice)
    (placeholder : Placed (Z.packingData.shrinkInternalOwner (layout B i Z sel))
      (internalLabel (supplyWidth B i Z sel) (layout B i Z sel)) v)
    (A : Arena) (inc : IncidenceDirectory w) (m : Memory w) (older cap : ℕ)
    (desc : Word w → ChildArguments.Descriptor w Z) (arg : Args w)
    (maps : List (Child Z) → List Row → List (ResidentMapLoop.Exact.Action w n))
    (cs hs ms : Setup w n) (node : Word w) (priv : Word w → Word w) (tail : List Bool)
    (order : (desc node).sites = List.ofFn fun j => ((ord).entries j).val)
    (childSetup : ∀ s, cs.updated node s = s) (hiddenSetup : ∀ s, hs.updated node s = s)
    (mapSetup : ∀ s, ms.updated node s = s) :
    let xs := children (t := Tr) Z v ord old
    let qs := (rdr).childPackets (childNode Z older cap) v old
    let es := rowsAt k.1
    let after := storeRows arg.scratchBase arg.slotStride es (storePackets A qs priv)
    let visit := visitReader A inc m older cap desc (fun _ => arg)
      (fun _ => rowsAt placeholder) maps cs (fun _ => hs) (fun _ _ => ms)
    ((hook visit).read node (scratch n priv) ((rdr).nodeBits v old new k ++ tail)).map
      (fun (j, rest) => (j.update (scratch n priv), rest)) =
        (ResidentMapLoop.Exact.scan node (maps xs es) (scratch n after)).map
          (fun (_, final) => (final, tail)) := by
  intro xs qs es after visit
  let hidBits := stream es ++ tail
  let c := ChildArguments.outcome A inc m older cap desc node (scratch n priv) xs
  have packets : xs.map (Child.packet Z older cap) = qs := by
    have halves (u z) : (rdr).halfBits u z = packed Z u z := (packed_eq_encode Z u z).symm
    simp only [xs, qs, children, List.map_ofFn, Function.comp_def, TermParsers.childPackets,
      Child.packet, Child.payload_ofHalf, halves]
    rfl
  have childStore : c.updated = scratch n (storePackets A qs priv) := by
    rw [scratch_storePackets, ← packets]
    rfl
  have input : (rdr).nodeBits v old new k ++ tail =
      (ChildArguments.placedReader (t := Tr) v ord).encode old ++ hidBits := by
    change ((ChildArguments.placedReader (t := Tr) v ord).encode old ++
      ((shrinkPassReaders B f hf i rfl Z).kernel sel v old new).encode k) ++ tail = _
    rw [ShrinkHiddenSlots.kernel_encode B f hf i Z sel v old new k, List.append_assoc]
    rfl
  obtain ⟨h, hiddenRead, hiddenValue⟩ := hiddenReader_encoded Z (layout B i Z sel)
    (supplyWidth B i Z sel) v arg m placeholder k.1 node
    (scratch n (storePackets A qs priv)) tail
  apply visit_effect A inc m older cap desc arg (rowsAt placeholder) maps cs hs ms node priv
    xs qs es
    _ hidBits tail c h _ rfl childStore hiddenRead hiddenValue (childSetup _) (hiddenSetup _)
    (mapSetup _)
  rw [input]
  exact ChildArguments.reader_placed (t := Tr) A inc m older cap desc v ord node _ order old hidBits

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI

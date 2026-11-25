import OAI.Computability.BorderVNP.CubeScatterCableAddress
import OAI.Computability.BorderVNP.CubeDirectedIntervalTables

/-! # Owned packet banks and the original padded host ends

A team needs only the bits at its own endpoint labels. The directed interval
table marks the beginning of the unused suffix of each ordered label pair.
Consequently checking those suffix words in the actual owner banks gives the
two zero factors of the physical host contraction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostAddress

open Crossing Physical NativeIntervals Tally VPVNP.MotifBase

variable {n d blocks b h K s : ℕ} {Team : Type*}

/-- Physical owner of the original endpoint, at the chosen grouping coordinate. -/
def endOwner (i : Fin (n+1)) (team : Fin d → Team) (dst : Bool)
    (u : Label (n+1) d × Label (n+1) d) : Team := team (if dst then u.2 i else u.1 i)

/-- The actual words supplied by the singleton and owned packet scatters at both endpoint labels. -/
structure EndBanks (i : Fin (n+1)) (team : Fin d → Team) (pack singles : Team → ℕ)
    (mem : Team → ℕ → ℕ) (single : SingleSlot n d blocks (h*b) → Bool)
    (ends : Packet n d blocks → Ends n → Fin (h*b) → Bool) (K s : ℕ) : Prop where
  /-- A retained singleton is available to each of its endpoint owners. -/
  singleton : ∀ (q : SingleSlot n d blocks (h*b)) (side : Bool),
    let t := endOwner i team side q.1.val
    mem t (singles t + (code q.1.val.1*d^(n+1)+code q.1.val.2)*(blocks*(h*b))+q.2.val) = (single q).toNat
  /-- A packet's demand bit is available in the group owning its attached cube vertex. -/
  demand : ∀ (p : Packet n d blocks) (v : Vertex n) (side : Bool) (j : Fin (h*b)),
    let t := team (vertexLabel p (if side then stop v else start v) i)
    mem t (pack t + Owned.packetIndex p*bankWidth n b h K s + demandOffset n b h K (v,side) j) =
      (ends p (v,side) j).toNat

/-- The public three-field directory and native arithmetic access the actual source bit of an original endpoint. -/
theorem EndBanks.read {i : Fin (n+1)} {team : Fin d → Team} {pack singles : Team → ℕ}
    {mem : Team → ℕ → ℕ} {single : SingleSlot n d blocks (h*b) → Bool}
    {ends : Packet n d blocks → Ends n → Fin (h*b) → Bool}
    (banks : EndBanks i team pack singles mem single ends K s)
    (u v : Label (n+1) d) (ord : Fin (blocks*(h*b))) (side : Bool) :
    let t := endOwner i team side (u,v)
    mem t (address d (n+1) blocks (h*b) (pack t) (bankWidth n b h K s) (selectorWidth n K h)
      (singles t) (code u) (code v) ord.val side) =
      (readEnd single ends side ((u,v),ord)).toNat := by
  intro t
  rw [address_eq_split,readEnd]
  cases hs : splitSlot n d blocks (h*b) ((u,v),ord) with
  | inr q =>
    have back := congrArg (splitSlot n d blocks (h*b)).symm hs
    rw [Equiv.symm_apply_apply] at back
    have hp : (u,v) = q.1.val := congrArg Prod.fst back
    simpa only [t,hp] using banks.singleton q side
  | inl z =>
    obtain ⟨p,v',j⟩ := z
    have back := congrArg (splitSlot n d blocks (h*b)).symm hs
    rw [Equiv.symm_apply_apply] at back
    have labels := (congrArg Prod.fst back).trans (inverseSlot_labels p v' j)
    change (u,v) = _ at labels
    have own : t = team (vertexLabel p (if side then stop v' else start v') i) := by
      change endOwner i team side (u,v) = _
      rw [labels]
      cases side <;> rfl
    rw [own]
    exact banks.demand p v' side j

/-- The native zero tests for all teams, on the actual shared-memory table of directed live widths. -/
def TailTests (i : Fin (n+1)) (team : Fin d → Team) (pack singles : Team → ℕ) (K s h b blocks : ℕ)
    (mem : Team → ℕ → ℕ) (used : ℕ → ℕ) : Prop :=
  ∀ t (u v : Label (n+1) d) (side : Bool), endOwner i team side (u,v) = t →
    ∀ j : Fin (blocks*(h*b)), used (code u*d^(n+1)+code v) ≤ j.val →
      mem t (address d (n+1) blocks (h*b) (pack t) (bankWidth n b h K s) (selectorWidth n K h)
        (singles t) (code u) (code v) j.val side) = 0

/-- Physical zero tests are exactly the host's two pins for every unoccupied padded slot.
The width readout is the result of the verified native interval pass. -/
theorem tailTests_iff {D m : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
    {N : Network D P bits} {cell : N.Site → Cell} {l : NativeIntervals.Layout}
    {before dir : ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m} {row : Fin m ↪o Fin l.count}
    {cells : Cell ↪ ℕ} {label : Cell → Label (n+1) d} {hz : d^(n+1) = l.alphabet}
    (rows : PhysicalRows N cell l before ord row cells label (productCode n d l.alphabet hz))
    (image : l.Image before l.count dir) (cap)
    {i : Fin (n+1)} {team : Fin d → Team} {pack singles : Team → ℕ}
    {mem : Team → ℕ → ℕ} {single : SingleSlot n d blocks (h*b) → Bool}
    {ends : Packet n d blocks → Ends n → Fin (h*b) → Bool} (banks : EndBanks i team pack singles mem single ends K s) :
    TailTests i team pack singles K s h b blocks mem (fun k => dir (l.widths+k)) ↔
      ∀ q ∉ Set.range (packedSlotEmbedding N cell ord label blocks (h*b) cap),
        readEnd single ends false q = false ∧ readEnd single ends true q = false := by
  have missing (u v : Label (n+1) d) (j : Fin (blocks*(h*b))) :
      ((u,v),j) ∉ Set.range (packedSlotEmbedding N cell ord label blocks (h*b) cap) ↔
        dir (l.widths + (code u*d^(n+1)+code v)) ≤ j.val := by
    rw [mem_range_packedSlot_iff,not_lt,← rows.image_load image (u,v)]
    have he : pairCode (productCode n d l.alphabet hz) (u,v) = code u*d^(n+1)+code v := by
      change (finFunctionFinEquiv u).val*l.alphabet+(finFunctionFinEquiv v).val = _
      rw [← hz]
      rfl
    rw [he]
  constructor
  · intro tests q hq
    obtain ⟨⟨u,v⟩,j⟩ := q
    have both (side : Bool) : readEnd single ends side ((u,v),j) = false := by
      have hz := (banks.read u v j side).symm.trans (tests _ u v side rfl j ((missing u v j).mp hq))
      simpa using hz
    exact ⟨both false,both true⟩
  · intro pins t u v side own j hj
    subst t
    rw [banks.read]
    obtain ⟨src,dst⟩ := pins ((u,v),j) ((missing u v j).mpr hj)
    cases side <;> simp [src,dst]

end Cube.HostAddress

end BorderVNP
end Computability
end OAI

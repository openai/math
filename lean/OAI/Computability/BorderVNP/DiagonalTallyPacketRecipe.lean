import OAI.Computability.BorderVNP.DiagonalTallyPacketBank

/-! # Fixed per-selector and per-vertex packet address recipes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Tally

open VPVNP.BurstRAM VPVNP.RAMSerialization VPVNP.MotifBase
open DiagonalResidueRAM DiagonalTallyGather

/-- One source for a lookup digit, given before the packet placement is known. -/
inductive Reference
  | literal (b : Bool)
  | packet (offset : ℕ)
  deriving DecidableEq

/-- A literal uses one of the two shared constant words. A packet offset is relative to
the actual packet bank selected by the current team's ownership record. -/
def Reference.address (base zeroAddr oneAddr : ℕ) : Reference → ℕ
  | .literal false => zeroAddr
  | .literal true => oneAddr
  | .packet k => base+k

/-- Compact native encoding in one public word. -/
def Reference.code : Reference → ℕ
  | .literal b => b.toNat
  | .packet k => k+2

variable {n b h K s D w : ℕ}

/-- The fixed numeric argument length of every lookup for this identity. -/
noncomputable def argumentWidth (n b h K s : ℕ) : ℕ :=
  selectorWidth n K h+Nat.clog 2 (Fintype.card (Vertex (n+1)))+maximumWidth n b h K s

/-- Static relative addresses, padding and vertex digits for one finite lookup template. -/
noncomputable def recipe (u : Selector n K h) (v : Vertex (n+1)) (b s : ℕ) : List Reference :=
  (List.ofFn fun j : Fin (selectorWidth n K h) => Reference.packet j.val).reverse ++
  (prefixDigits (vertexOrder _) v).map Reference.literal ++
  List.replicate (maximumWidth n b h K s-rowWidth u v b s) (.literal false) ++
  (List.ofFn fun k => Reference.packet (rowOffset u v ((bitOrder u v b s).symm k))).reverse

theorem recipe_length (u : Selector n K h) (v : Vertex (n+1)) (b s : ℕ) :
    (recipe u v b s).length = argumentWidth n b h K s := by
  have h := rowWidth_le u v b s
  simp [recipe,argumentWidth,prefixDigits]; omega

/-- Field values actually resident at the indicated physical packet base. Every
selector word has the finite radix encoding, and the reads of all supply endpoints
agree because they use the shared address for the edge. -/
structure BankAt (m : Memory w) (base : ℕ) (u : Selector n K h)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) : Prop where
  /-- The common packet selector in the fixed prefix. -/
  selector : ∀ j : Fin (selectorWidth n K h), (m (base+j.val)).val =
    ((VPVNP.RAMSerialization.wordBits _ ⟨(selectorOrder n K h u).val,
      (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩) j).toNat
  /-- Both demand endpoint banks. -/
  demand : ∀ e j, (m (base+demandOffset n b h K e j)).val = (x e j).toNat
  /-- One supply word per directed edge. -/
  supply : ∀ e j, (m (base+supplyOffset n b h K s e j.val)).val = (z e j).toNat

/-- Local condition on the words a single owned cube vertex can actually read. Remote
ends and nonincident supply cables may occupy no initialized words on this team. -/
structure VertexAt (m : Memory w) (base : ℕ) (u : Selector n K h) (v : Vertex (n+1))
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) : Prop where
  /-- The common selector is available at the owner. -/
  selector : ∀ j : Fin (selectorWidth n K h), (m (base+j.val)).val =
    ((VPVNP.RAMSerialization.wordBits _ ⟨(selectorOrder n K h u).val,
      (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩) j).toNat
  /-- The attached demand ends are local to the vertex. -/
  demand : ∀ e : Ends n, (if e.2 then stop e.1 else start e.1) = v → ∀ j,
    (m (base+demandOffset n b h K e j)).val = (x e j).toNat
  /-- Incident supply bits come either from the same group or the shared cut. -/
  supply : ∀ e : Edge (n+1), e.1=v ∨ head e=v → ∀ j,
    (m (base+supplyOffset n b h K s e j.val)).val = (z e j).toNat

/-- A complete physical packet bank induces every one of its local views. -/
theorem BankAt.atVertex {m : Memory w} {base : ℕ} {u : Selector n K h}
    {x : Ends n → Fin (h*b) → Bool} {z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool}
    (h : BankAt m base u x z) (v : Vertex (n+1)) : VertexAt m base u v x z :=
  ⟨h.selector,fun e _ => h.demand e,fun e _ => h.supply e⟩

/-- Concrete arguments to the table at a vertex of this physical packet. -/
def packetEntry (D b s : ℕ) (u : Selector n K h) (v : Vertex (n+1))
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    TableEntry n b h K s := ⟨u,v,packetRow D b s u v (fun i => z i.val) (fun i => x i.val)⟩

/-- Native reference words read exactly the bits of the actual packet table position. -/
theorem recipe_reads_at (m : Memory w) (base zeroAddr oneAddr : ℕ) (u : Selector n K h)
    (v : Vertex (n+1)) (x : Ends n → Fin (h*b) → Bool)
    (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool)
    (hb : VertexAt m base u v x z) (hzero : (m zeroAddr).val = 0) (hone : (m oneAddr).val = 1) :
    ((recipe u v b s).map fun r => (m (r.address base zeroAddr oneAddr)).val) =
      (lookupDigits (selectorOrder n K h) (vertexOrder _) (packetEntry D b s u v x z)).map Bool.toNat := by
  have lit (b : Bool) : (m ((Reference.literal b).address base zeroAddr oneAddr)).val = b.toNat := by
    cases b <;> assumption
  have selectorEq :
      (List.ofFn fun j : Fin (selectorWidth n K h) => (m (base+j.val)).val) =
        List.ofFn (fun j : Fin (selectorWidth n K h) => ((VPVNP.RAMSerialization.wordBits _
          ⟨(selectorOrder n K h u).val,(selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩) j).toNat) :=
    congrArg List.ofFn (funext hb.selector)
  have rowEq (k : RowBit u v b s) :
      (m (base+rowOffset u v k)).val = (rowBits u v b s (packetEntry D b s u v x z).2.2 k).toNat := by
    change _ = (rowBits u v b s (packetRow D b s u v (fun i => z i.val) (fun i => x i.val)) k).toNat
    rw [packetRow_bits (D := D) (s := s) (b := b) u v (fun i => z i.val) (fun i => x i.val) k]
    cases k with
    | inl j =>
      cases j with
      | inl j => exact hb.demand (j.1.val,false) j.1.property j.2
      | inr j => exact hb.demand (j.1.val,true) j.1.property j.2
    | inr j =>
      cases j with
      | inl j => exact hb.supply _ (.inl j.1.property) j.2
      | inr j => exact hb.supply _ (.inr j.1.property) j.2
  have atPacket (i : ℕ) : (Reference.packet i).address base zeroAddr oneAddr = base+i := rfl
  simp only [recipe,lookupDigits,packetEntry,List.map_append,List.map_reverse,List.map_ofFn,
    Function.comp_def,atPacket,List.map_replicate,lit,prefixDigits,
    VPVNP.BurstRAM.wordBits,physicalDigits,selectorEq]
  simp only [rowEq,packetEntry]
  rfl

/-- A complete bank also realizes every vertex's recipe. -/
theorem recipe_reads (m : Memory w) (base zeroAddr oneAddr : ℕ) (u : Selector n K h)
    (v : Vertex (n+1)) (x : Ends n → Fin (h*b) → Bool)
    (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool)
    (hb : BankAt m base u x z) (hzero : (m zeroAddr).val = 0) (hone : (m oneAddr).val = 1) :
    ((recipe u v b s).map fun r => (m (r.address base zeroAddr oneAddr)).val) =
      (lookupDigits (selectorOrder n K h) (vertexOrder _) (packetEntry D b s u v x z)).map Bool.toNat :=
  recipe_reads_at m base zeroAddr oneAddr u v x z (hb.atVertex v) hzero hone

/-- Fixed size of the row-ID directory: no lookup index exceeds this many slots. -/
theorem lookupIndex_lt (e : TableEntry n b h K s) :
    lookupIndex (selectorOrder n K h) (vertexOrder _) e < 2^argumentWidth n b h K s := by
  rw [← lookupDigits_index]
  let bs := lookupDigits (selectorOrder n K h) (vertexOrder _) e
  have hv := VPVNP.TapeWord.value_lt bs.reverse
  have hr := readDigits_reverse bs.reverse
  simp only [List.reverse_reverse,List.length_reverse] at hv hr
  have len : bs.length = argumentWidth n b h K s := by
    have h := rowWidth_le e.1 e.2.1 b s
    simp [bs,lookupDigits,prefixDigits,physicalDigits,argumentWidth,selectorWidth]; omega
  rw [← hr,len] at hv
  exact hv

end Cube.Tally

end BorderVNP
end Computability
end OAI

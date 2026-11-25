import OAI.Computability.BorderVNP.CellPacketGeometryHistoryBus
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryFits

/-! # The physical output of the retained emitter gives the exact sorted network directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open Crossing Shortening Packing Packing.Inherited FrozenTape VPVNP.VerifierNetwork ParseBatchSort
open CellSparse Packet LiveWords SiteWords Packing.BankPacket
open private branchDirectory runtimeArgs runtimeFields from OAI.Computability.BorderVNP.CellPacketGeometryOrderedBuffer

/-- The two checked static marker capacities together with a real physical
forward permutation and its complete per-cell RAM image. -/
def Published {A O E : Type} {c : ℕ} (G : SiteWords.Directory A O c) (p d dest H : ℕ)
    (pointer : O → E) (arg : E → ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ hf : c+G.words.length+c≤2^p, ∃ hs : c+(CellPacketGeometry.Schema.coords (G.referenceRows pointer).length).length+c≤2^d,
  ∃ π : Equiv.Perm (Fin (2^p)), CellPacketGeometry.Schema.Buffers G hf hs dest H
    (fun i => ((G.referenceRows pointer).get i).2) (fun i => ((G.referenceRows pointer).get i).1) arg mem π

private theorem published {A O E : Type} {c : ℕ} {G : SiteWords.Directory A O c} {p d dest H : ℕ}
    (pointer : O → E) {arg : E → ℕ} {mem : ℕ → ℕ} {hf : c+G.words.length+c≤2^p}
    {hs : c+(CellPacketGeometry.Schema.coords (G.referenceRows pointer).length).length+c≤2^d} {π : Equiv.Perm (Fin (2^p))}
    (h : CellPacketGeometry.Schema.Buffers G hf hs dest H
      (fun i => ((G.referenceRows pointer).get i).2) (fun i => ((G.referenceRows pointer).get i).1) arg mem π) :
    Published G p d dest H pointer arg mem := ⟨hf,hs,π,h⟩

variable {a C cap k w d t q : ℕ} {R B U V E Orig σ : Type}
variable [Fintype R] [Fintype B] [Fintype U] [Fintype V] [Fintype E] [Fintype σ]
variable (F : Feeds σ R B U V E a d t k w) (S : Schema R B) (L : Schema U V)
variable (boxes : Fin a → List (Source.Box Orig)) (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ u, (L.tags u).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E))
variable (x : σ → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
variable {D n p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → ℕ) (sid : N.Site ↪ Fin a) (edges : N.Edge ↪ Fin n) (ports : P ↪ Fin p) (state : N.Site → Site)
local notation3 "T₀" => template S L boxes sh lh priv rep
local notation3 "args₀" => F.arguments x
local notation3 "hist₀" => F.history.eval x
local notation3 "bind₀" => F.binding.eval x
local notation3 "G₀" => directory S L boxes sh lh priv rep args₀ hist₀ bind₀ cells off box
local notation3 "fields₀" => fun (i : Fin (roster a S L).length) => scalarArgs (cap := cap) S L hist₀ bind₀ off box ((roster a S L).get i)
variable (hd : d≤q) (ht : t≤q) (room : a<2^q) (keysFit : C+1<2^k)
variable (hs : ∀ r, S.width r≤w) (hl : ∀ u, L.width u≤w)
variable (baseOwner : Fin (roster a S L).length → Fin (C+1))
variable (pointer : Orig → (template S L boxes sh lh priv rep).Fields)
variable (pad : (roster a S L).length < 2^q) (dest H : ℕ)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
/-- One true joint geometry output supplies both ordered RAM buffers of every
cell. Source arithmetic and range validity are derived from physical field,
factor and network-record bounds; no per-slot sorted-data hypotheses enter. -/
theorem Feeds.buffers (fs : Orig → List Factor)
    (historical : S.Image hist₀ (sid.trans Fin.valEmbedding) state)
    (last : L.Section bind₀ (sid.trans Fin.valEmbedding) (FinalCell.binding N cell sid edges ports state))
    (resolved : ∀ i, (boxes i).map (Source.factors fs)=FinalCell.slots sid (fun v => (state v).boxes) i)
    (bitBase : ∀ v, off (sid v) = CellAddresses.siteBase N cell (cell v) sid (fun u => (state u).size) ⟨v,rfl⟩)
    (boxBase : ∀ v, box (sid v) = FinalCell.firstBox sid (fun i => (cells i).val) state v)
    (tc : ∀ i, value (fun j => F.table.eval x (i,.inl j))=(cells i).val)
    (ts : ∀ i b, value (fun j => F.table.eval x (i,.inr (b,j)))=(if b then box else off) i)
    (wide : 2^(T₀).recordDepth ≤ 2^(w+k)) (boxRoom : (∑ i, (boxes i).length)<2^w)
    (rowRoom : S.rows.length+L.rows.length<2^w) (capRoom : cap<2^w) (three : 3<2^w)
    (known : ∀ i n, n∈boxWords (boxes i) → n<2^w)
    (reportRows : ∀ c, (rep c).length<2^w) (vectors : ∀ c r, r∈rep c → r.length<2^w)
    (limit : Fin C → ℕ) (limitRoom : ∀ c, limit c<2^w)
    (bounds : ∀ c : Fin C, ∀ r ∈ (FinalCell.directory (fun i => (cells i).val) N cell sid edges ports state
      c.val ((G₀).reports c.castSucc)).records, RecordFields r (limit c))
    (sourceRoom : dest+2^(T₀).publicDepth<2^w) (descRoom : 2^(T₀).chunkDepth≤2^w) (header : H<2^w)
    (mem : ℕ → ℕ) (read : ∀ i : Fin (Total (T₀).publicDepth (T₀).chunkDepth),
      mem (dest+i.val)=value (fun j => (F.ordered S L boxes sh lh priv rep hd ht room
        (Nat.lt_trans (Nat.lt_succ_self C) keysFit) hs hl baseOwner pointer pad dest H).eval x (.inl (i,j)))) :
    Published (G₀) (T₀).publicDepth (T₀).chunkDepth dest H pointer ((T₀).arguments args₀ fields₀) mem := by
  let croom : C<2^k := Nat.lt_trans (Nat.lt_succ_self C) keysFit
  let up := source (cap := cap) S L (access : Access R B U V E (Bundle R B U V E a d t k w) a d t k w)
    hd ht room croom hs hl
  let keys := anchors S L (access : Access R B U V E (Bundle R B U V E a d t k w) a d t k w) hd ht room
  let owner := cellOf S L hist₀ bind₀ cells
  let anch := anchor (a := a) S L hist₀ bind₀
  let input := F.frame.eval x
  obtain ⟨ha,hc,ea,ef⟩ := F.bus S L x cells off box sid state _ historical last hd ht room croom hs hl tc ts
  change runtimeArgs up input = args₀ at ea
  change runtimeFields up input = fields₀ at ef
  have linked : ∀ i, owner (anch i)=owner i := anchored S L hist₀ bind₀ cells
  have dEq : branchDirectory (T₀) up input owner anch = G₀ := by
    change ((T₀).directory owner _ _).regroup anch = _
    rw [ea,ef]
    rfl
  have cnt := cell_counts_fit S L boxes sh lh priv rep args₀ hist₀ bind₀ cells off box boxRoom rowRoom
  have fit z := rowPin_fits_final S L boxes sh lh priv rep args₀ hist₀ bind₀ cells off box N cell sid edges ports state fs
    historical last resolved bitBase boxBase hs hl capRoom three limit limitRoom bounds z
  have rfit (z : (T₀).RowPin) : ((tape ((T₀).format z.1))[z.2.val]).Fits w (runtimeFields up input z.1) :=
    by rw [ef]; exact fit z
  have literals := History.literal_fits S L boxes sh lh priv rep known reportRows vectors
  have outputs (i) : mem (dest+i.val) = value (fun j => ((T₀).orderedFrame up keys baseOwner pointer pad dest H).eval input (.inl (i,j))) :=
    (read i).trans (congrArg value (funext fun j => F.ordered_eval S L boxes sh lh priv rep hd ht room croom hs hl
      baseOwner pointer pad dest H x (.inl (i,j))))
  obtain ⟨π,out⟩ := (T₀).ordered_buffers up keys baseOwner pointer pad dest H input owner anch linked wide keysFit
    ha hc (fun c => dEq.symm ▸ (cnt c).1) (fun c => dEq.symm ▸ (cnt c).2) rfit literals
    sourceRoom descRoom header (by omega) mem outputs
  have image : Published (branchDirectory (T₀) up input owner anch) (T₀).publicDepth (T₀).chunkDepth dest H pointer
      ((T₀).arguments (runtimeArgs up input) (runtimeFields up input)) mem := published pointer out
  rw [dEq,ea,ef] at image
  exact image

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI

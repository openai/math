import OAI.Hierarchy.DescentTerminalPointerOrigin
import OAI.Hierarchy.DescentTerminalOperandSlots
import OAI.Hierarchy.DescentTerminalPointerSource
import OAI.Hierarchy.DescentTerminalBoundaryPointer
import OAI.Hierarchy.DescentTerminalRoleChannel

namespace OAI
/-! # Physical terminal pointer emission for the numbered, restricted scalar recipe -/
namespace Hierarchy.DescentTerminalPointerIssue
open Computability.BorderVNP.Crossing DescentSixParty DescentSharedCableNames DescentKernelHistory DescentTerminalPortChart
open DescentBundleHistory DescentTerminalBoundaryBasis DescentCompiler DescentColonies DescentLocalPrivateNames
open DescentOperandStateBanks DescentTerminalPointerDigits DescentTerminalChronologicalBooks
open ThreeFlat.Routing DescentTerminalVertexFields
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

section Slots
variable {Tag B : Type} {N A D cap : ℕ} (r:Recipe Tag B) (birth:r.Node↪ℕ)
    (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤A)
local notation "nr" => row r birth nodes
local notation "whereAt" => slot r birth nodes arity
variable (t : CellInputs D cap N A)
theorem inactive (head:t.n=Fintype.card r.Node) (cols:∀u,t.arity (nr u)=r.arity u) (i:Fin (N*A))
    (away:∀s,whereAt s≠i) : ¬t.active i := by
  obtain ⟨⟨u,j⟩,rfl⟩:=finProdFinEquiv.surjective i
  intro active
  unfold CellInputs.active at active
  rw [Equiv.symm_apply_apply] at active
  let k : Fin (Fintype.card r.Node):=⟨u.val,head ▸ active.1⟩
  let node:=(ordinal birth).symm k
  have eqn : nr node = u := by
    apply Fin.ext
    change ((ordinal birth) ((ordinal birth).symm k)).val = k.val
    exact congrArg (fun j : Fin (Fintype.card r.Node) => j.val) ((ordinal birth).apply_symm_apply k)
  have bound:j.val<r.arity node:=by rw [←cols,eqn];exact active.2
  let arg:Fin (r.arity node):=⟨j.val,bound⟩
  apply away ⟨node,arg⟩
  change finProdFinEquiv (nr node,arg.castLE _)=_
  rw [eqn]
  rfl
end Slots

section Sources
variable {P Tag : Type} [Fintype P] {d p D cap N A K : ℕ} {bits:P→ℕ}
    (G:Network d P bits) (v:G.Site) (r:Recipe Tag (BlockRef p (boundaryWidth G v)))
    (birth:r.Node↪ℕ) (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤A) (aliases:Slot r↪Fin K)
    (rk:Boundary G v↪ℕ) (port:Attached G v↪ℕ) (t:CellInputs D cap N A)
local notation "loc" => slot r birth nodes arity
local notation "alias" => firstAlias r aliases
variable (origin:Origin G v r birth nodes arity aliases rk port t)
include origin in
theorem Origin.privateSource (s:Slot r) : t.privateAt (loc s)=privateName r aliases s := by
  symm
  rw [privateName, CellInputs.privateAt, ite_eq_left (live_slot r birth nodes arity t origin.population origin.arities s)]
  split
  · rename_i b hit
    rcases b with ⟨e | z, j, clip⟩
    · obtain ⟨_, _, key, _⟩ := origin.cable s e j clip hit
      rw [key]
    · obtain ⟨_, key, _⟩ := origin.exterior s z j clip hit
      rw [key]
  · rename_i w hit
    rw [origin.privateWord s ⟨w, s.1, s.2, hit⟩ hit]

include origin in
theorem Origin.gap (i:Fin (N*A)) (away:∀s,loc s≠i) : t.privateAt i=none := by
  rw [CellInputs.privateAt,ite_eq_right (inactive r birth nodes arity t origin.population origin.arities i away)]
end Sources

theorem reindexed_private {D cap N M:ℕ} (t:CellInputs D cap N M) (index:ℕ→ℕ) :
    (reindexed t index).privateAt=t.privateAt := by
  funext i
  unfold CellInputs.privateAt
  change (if t.active i then _ else _)=(if t.active i then _ else _)
  by_cases on:t.active i
  · rw [ite_eq_left on,ite_eq_left on]
    cases h:t.pointer i <;> simp [reindexed,reindex,h]
  · simp [on]

section Reader
variable {q tags hid N A p groups blocks shops wb:ℕ}
local notation "bits" => Nat.clog 2 (q+hid+1)
local notation "reader" => measured (q:=q) (t:=tags) (H:=hid) (N:=N) (A:=A) (w:=p) (groups:=groups)

/-- The masked shelf reads exactly the addressed group and operand slice of its physical family-seven word. -/
theorem family_digit (machine:MaskedShelf blocks) (m:Memory wb) (base:ℕ) (b:Fin blocks)
    (placed:(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).base=base)
    (keep:shops≤(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).size) (hostWord:shops≤2^wb)
    (h:Fin shops) (g:Fin groups) (u:Fin N) (j:Fin A) :
    venueField (cellAt (reader machine m h) (finProdFinEquiv (g,b))) (nodeArg u j)=
      digit bits (finProdFinEquiv (u,j)).val (digit (bits*(N*A)) g.val (m (base+h.val)).val) := by
  rw [venue_digit]
  change digit bits (finProdFinEquiv (u,j)).val ((cellAt (reader machine m h) (finProdFinEquiv (g,b))) 7).val=_
  rw [cell_digit, measured_channel]
  change digit bits (finProdFinEquiv (u,j)).val (digit ((N*A)*bits) g.val
    (((machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).read m (h.val:Computability.VPVNP.BurstRAM.Word wb)).val%2^((N*A)*bits*groups)))=_
  rw [digit_clip,Nat.mul_comm (N*A) bits,Bank.read,Fin.val_cast_of_lt (h.isLt.trans_le hostWord),
    Nat.mod_eq_of_lt (h.isLt.trans_le keep),placed]
end Reader

section Output
variable {q tags hid N A p groups blocks shops wb D cap scale psize d0:ℕ}
    (config:Widths) (index:ℕ→ℕ→ℕ→ℕ) (base:ℕ) (src:Fin (columns cap N A)→Bank)
    (before:Memory wb) (machine:MaskedShelf blocks)
    (room:DescentTerminalPointerFrame.Room src base d0 shops wb)
    (board:Fin shops→Source cap N A d0) (source:∀h j,before ((src j).base+h.val)=((board h j).val:Computability.VPVNP.BurstRAM.Word wb))
local notation "digitBits" => Nat.clog 2 (q+hid+1)
local notation "done" => DescentTerminalPointerFrame.result base src shops
  (output cap N A D groups d0 (Nat.clog 2 (q+hid+1)) q scale psize config index) before
local notation "current" => measured (q:=q) (t:=tags) (H:=hid) (N:=N) (A:=A) (w:=p) (groups:=groups)
variable (fits:(Nat.clog 2 (q+hid+1)*(N*A))*groups≤wb) (b:Fin blocks)
    (atBase:(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).base=base+DescentTerminalPointerFrame.size (columns cap N A) d0)
    (keep:shops≤(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).size) (hostWord:shops≤2^wb)

include room source fits atBase keep hostWord in
/-- The native row issue simultaneously supplies the real word in family seven and
its numerical slot at the actual masked hardware reader. The seven other families are
irrelevant to this read. -/
theorem printed_operand (h:Fin shops) (g:Fin groups) (u:Fin N) (j:Fin A)
    (small:(decode D config index (board h) g.val).argument q scale psize (finProdFinEquiv (u,j))<2^digitBits) :
    venueField (cellAt (current machine done h) (finProdFinEquiv (g,b))) (nodeArg u j)=
      (decode D config index (board h) g.val).argument q scale psize (finProdFinEquiv (u,j)) := by
  have issue:=DescentTerminalPointerDigits.issued cap N A D groups digitBits q scale psize config index base src before room board source fits
  have observed:=issue.2.2.2.1 h g (finProdFinEquiv (u,j)) small
  exact (family_digit (q:=q) (hid:=hid) (tags:=tags) (p:=p) machine done
    (base+DescentTerminalPointerFrame.size (columns cap N A) d0) b atBase keep hostWord h g u j).trans observed
end Output

section Reached
variable {F P J V Tag : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i p q N M K tags : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S i)
    (names:Stage.Host J V k↪ℕ) (v:W.graph.Site) (coords:Function.Injective (fun s=>(A.pos s,A.block s)))
    (port:Attached W.graph v↪ℕ) (hp:0<p) (scale psize:ℕ) (whole:A.z*G.b=scale*p)
    (common:∀z:Attached W.graph v,poolBatchCount (bits z.val) p=psize)
    (r:Recipe Tag (BlockRef p (boundaryWidth W.graph v))) (code:Tag→Fin tags)
    (birth:r.Node↪ℕ) (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤M) (aliases:Slot r↪Fin K)
    (t:CellInputs A.degree A.cap N M)
local notation "rk" => rank A native S ready names v port
local notation "loc" => slot r birth nodes arity
local notation "chart" => Function.Embedding.trans (firstAlias r aliases) Fin.valEmbedding
local notation "G'" => W.graph
local notation "sparse" => Origin G' v r birth nodes arity aliases rk port t
local notation "sig" => Stage.signedPanel A native S ready names (Stage.home A v)

include coords whole common in
/-- The decoder word at each actual node and argument is the exact `PrimitiveReceipts.operand`
integer of the whole boundary basis and the restricted hidden variables. -/
theorem reference (origin:sparse) (chips:t.chips=sig) (u:r.Node) (j:Fin (r.arity u)) :
    t.argument q scale psize (loc ⟨u,j⟩)=
      DescentTerminalBoundaryPointer.num (q:=q) G' hp v rk r code chart u j := by
  let s:Slot r:=⟨u,j⟩
  rw [CellInputs.at_slot _ _ _ _ _ (live_slot r birth nodes arity t origin.population origin.arities s)]
  refine DescentTerminalBoundaryPointer.operand_read (q := q) G' hp v rk r code chart u j _ ?_ ?_
  · rintro ⟨edge|pin,n,clip⟩ hit
    · obtain ⟨peer,serial,read,located⟩:=origin.cable s edge n clip hit
      rw [read,chips]
      have actual:=cable_digit A native S ready names v coords port hp scale whole q psize (present t.privateAt)
        edge n clip peer serial located
      simpa only [address_val,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using actual
    · obtain ⟨ord,read,dense⟩:=origin.exterior s pin n clip hit
      rw [read,chips]
      have actual:=exterior_digit A native S ready names v coords port hp scale whole q psize (present t.privateAt)
        pin ord n dense common clip
      simpa only [address_val,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using actual
  · intro h hit
    rw [origin.privateWord s h hit]
    have actual:=private_digit r aliases loc t.privateAt
      (Origin.privateSource G' v r birth nodes arity aliases rk port t origin)
      (Origin.gap G' v r birth nodes arity aliases rk port t origin) q A.cap scale psize (grains t.chips) h
    simpa only [ordinal_val,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using actual

include coords whole common in
/-- Native physical fields are certified before the original public-copy label is
sent through the measured frozen permutation. Its image is used only on the pin case. -/
theorem reached_argument {d0:ℕ} (config:Widths) (raw:Source A.cap N M d0) (g:ℕ)
    (index:ℕ→ℕ→ℕ→ℕ) (read:SourceRead config raw g t)
    (origin:Origin G' v r birth nodes arity aliases rk port (reindexed t (index (raw mcol).val (raw fcol).val)))
    (chips:t.chips=sig) (u:r.Node) (j:Fin (r.arity u)) :
    (decode A.degree config index raw g).argument q scale psize (loc ⟨u,j⟩)=
      DescentTerminalBoundaryPointer.num (q:=q) G' hp v rk r code chart u j := by
  let idx:=index (raw mcol).val (raw fcol).val
  have on:t.active (loc ⟨u,j⟩):=live_slot r birth nodes arity t origin.population origin.arities _
  have actual:=actual_argument config raw g t index read q scale psize _ on
  have semantic:=reference (q := q) A native S ready names v coords port hp scale psize whole common r code birth nodes arity
    aliases (reindexed t idx) origin chips u j
  rw [CellInputs.at_slot _ _ _ _ _ (show (reindexed t idx).active (loc ⟨u,j⟩) from on),reindexed_private] at semantic
  exact actual.trans semantic

theorem reference_fits {H:ℕ} (publicRoom:DescentTerminalGraphRows.arity G' p v≤q) (privateRoom:Fintype.card r.UsedWord≤H)
    (u:r.Node) (j:Fin (r.arity u)) :
    DescentTerminalBoundaryPointer.num (q:=q) G' hp v rk r code chart u j<2^(Nat.clog 2 (q+H+1)) := by
  have size:=Nat.le_pow_clog (by decide : 1<2) (q+H+1)
  unfold DescentTerminalBoundaryPointer.num
  cases hit:(numbered G' hp v rk r.restricted code).operand u j with
  | inl b=>
    change b.val+1<_
    have bound:b.val<DescentTerminalGraphRows.arity G' p v:=b.isLt
    omega
  | inr h=>
    change q+(ordinal chart h).val+1<_
    have bound : (ordinal chart h).val < Fintype.card r.UsedWord := (ordinal chart h).isLt
    omega

section Word
variable {hid groups blocks shops wb d0:ℕ} (config:Widths) (index:ℕ→ℕ→ℕ→ℕ) (base:ℕ)
    (src:Fin (columns A.cap N M)→Bank) (before:Memory wb)
    (room:DescentTerminalPointerFrame.Room src base d0 shops wb)
local notation "ob" => DescentTerminalPointerDigits.low (H:=shops) (d:=d0) src before
local notation "sz" => Nat.clog 2 (q+hid+1)
local notation "cs" => columns A.cap N M
local notation "f7" => output A.cap N M A.degree groups d0 (Nat.clog 2 (q+hid+1)) q scale psize config index
local notation "after" => DescentTerminalPointerFrame.result base src shops
  (output A.cap N M A.degree groups d0 (Nat.clog 2 (q+hid+1)) q scale psize config index) before
local notation "first" => base+DescentTerminalPointerFrame.size (columns A.cap N M) d0
variable (h:Fin shops) (g:Fin groups) (fits:(Nat.clog 2 (q+hid+1))*(N*M)*groups≤wb)
    (publicRoom:DescentTerminalGraphRows.arity W.graph p v≤q) (privateRoom:Fintype.card r.UsedWord≤hid)
    (read:SourceRead config (DescentTerminalPointerDigits.low (H:=shops) (d:=d0) src before h) g.val t)
    (origin:Origin W.graph v r birth nodes arity aliases
      (DescentTerminalPortChart.rank A native S ready names v port) port
      (reindexed t (index
        (DescentTerminalPointerDigits.low (H:=shops) (d:=d0) src before h (mcol (cap:=A.cap) (N:=N) (A:=M))).val
        (DescentTerminalPointerDigits.low (H:=shops) (d:=d0) src before h (fcol (cap:=A.cap) (N:=N) (A:=M))).val)))
    (chips:t.chips=Stage.signedPanel A native S ready names (Stage.home A v))

include coords whole common room fits publicRoom privateRoom read origin chips in
theorem primitive_word :
    (DescentTerminalPointerFrame.program wb base src shops f7).Exec before after
      ((4+10*DescentTerminalPointerFrame.size cs d0)+(4+shops*(16+26*cs))) ∧
    CheapCode (DescentTerminalPointerFrame.program wb base src shops f7) ∧
    (∀u (j:Fin (r.arity u)),digit sz (loc ⟨u,j⟩).val (digit (sz*(N*M)) g.val (after (first+h.val)).val)=
      DescentTerminalBoundaryPointer.num (q:=q) G' hp v rk r code chart u j) ∧
    ∀z,z<base ∨ first+shops≤z→after z=before z := by
  have receipt:=DescentTerminalPointerDigits.issue_memory (d:=d0) (H:=shops) (w:=wb)
    A.degree A.cap N M groups sz q scale psize config index base src before room fits
  refine ⟨receipt.1,receipt.2.1,?_,receipt.2.2.2⟩
  intro u j
  have actual:=reached_argument (q:=q) A native S ready names v coords port hp scale psize whole common r code birth nodes arity
    aliases t config (ob h) g.val index read origin chips u j
  have cap:=reference_fits (q:=q) (H:=hid) A native S ready names v port hp r code aliases publicRoom privateRoom u j
  have on:t.active (loc ⟨u,j⟩):=live_slot r birth nodes arity t origin.population origin.arities _
  have decoded:=DescentTerminalPointerDigits.actual_argument config (ob h) g.val t index read q scale psize (loc ⟨u,j⟩) on
  have written:=receipt.2.2.1 h g (loc ⟨u,j⟩) t read on (decoded.symm.trans_lt (actual.trans_lt cap))
  exact written.trans (decoded.symm.trans actual)
end Word

section Physical
variable {hid groups blocks shops wb d0:ℕ} (config:Widths) (index:ℕ→ℕ→ℕ→ℕ) (base:ℕ)
    (src:Fin (columns A.cap N M)→Bank) (before:Memory wb) (machine:MaskedShelf blocks)
    (room:DescentTerminalPointerFrame.Room src base d0 shops wb)
local notation "ob" => DescentTerminalPointerDigits.low (H:=shops) (d:=d0) src before
local notation "sz" => Nat.clog 2 (q+hid+1)
local notation "cs" => columns A.cap N M
local notation "f7" => output A.cap N M A.degree groups d0 (Nat.clog 2 (q+hid+1)) q scale psize config index
local notation "after" => DescentTerminalPointerFrame.result base src shops
  (output A.cap N M A.degree groups d0 (Nat.clog 2 (q+hid+1)) q scale psize config index) before
local notation "first" => base+DescentTerminalPointerFrame.size (columns A.cap N M) d0
local notation "meas" => measured (q:=q) (t:=tags) (H:=hid) (N:=N) (A:=M) (w:=p) (groups:=groups)
variable (b:Fin blocks) (h:Fin shops) (g:Fin groups) (fits:(Nat.clog 2 (q+hid+1))*(N*M)*groups≤wb)
    (atBase:(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).base=(base+DescentTerminalPointerFrame.size (columns A.cap N M) d0))
    (keep:shops≤(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).size)
    (publicRoom:DescentTerminalGraphRows.arity W.graph p v≤q) (privateRoom:Fintype.card r.UsedWord≤hid)
    (read:SourceRead config (DescentTerminalPointerDigits.low (H:=shops) (d:=d0) src before h) g.val t)
    (origin:Origin W.graph v r birth nodes arity aliases
      (DescentTerminalPortChart.rank A native S ready names v port) port
      (reindexed t (index
        (DescentTerminalPointerDigits.low (H:=shops) (d:=d0) src before h (mcol (cap:=A.cap) (N:=N) (A:=M))).val
        (DescentTerminalPointerDigits.low (H:=shops) (d:=d0) src before h (fcol (cap:=A.cap) (N:=N) (A:=M))).val)))
    (chips:t.chips=Stage.signedPanel A native S ready names (Stage.home A v))

include coords whole common room fits atBase keep publicRoom privateRoom read origin chips in
/-- In the CPU's actual final state, the live seventh-family operand digit sought by
`PrimitiveReceipts` is the true block/alias reference of the restricted numbered recipe.
The input words come straight from the previous hardware state. -/
theorem primitive_operand :
    (DescentTerminalPointerFrame.program wb base src shops f7).Exec before after
      ((4+10*DescentTerminalPointerFrame.size cs d0)+(4+shops*(16+26*cs))) ∧
    CheapCode (DescentTerminalPointerFrame.program wb base src shops f7) ∧
    (∀u (j:Fin (r.arity u)),
      venueField (cellAt (meas machine after h) (finProdFinEquiv (g,b)))
        (nodeArg (row r birth nodes u) (j.castLE (arity u)))=
      (((numbered G' hp v rk r.restricted code).operand u j).elim (fun a=>a.val+1) (fun a=>q+(ordinal chart a).val+1))) ∧
    ∀z,z<base ∨ first+shops≤z→after z=before z := by
  have full:=primitive_word (q:=q) (hid:=hid) A native S ready names v coords port hp scale psize whole common r code birth nodes arity
    aliases t config index base src before room h g fits publicRoom privateRoom read origin chips
  refine ⟨full.1,full.2.1,?_,full.2.2.2⟩
  intro u j
  have span:=room.limit
  have hostWord:shops≤2^wb:=by omega
  exact (family_digit (q:=q) (hid:=hid) (tags:=tags) (p:=p) machine after first b atBase keep hostWord h g
    (row r birth nodes u) (j.castLE (arity u))).trans (full.2.2.1 u j)

end Physical

section AllBlocks
variable {hid groups blocks shops wb d0:ℕ} (config:Widths) (index:ℕ→ℕ→ℕ→ℕ) (base:ℕ)
    (src:Fin (columns A.cap N M)→Bank) (before:Memory wb) (machine:MaskedShelf blocks)
    (room:DescentTerminalPointerFrame.Room src base d0 (blocks*shops) wb)
local notation "ob" => DescentTerminalPointerDigits.low (H:=blocks*shops) (d:=d0) src before
local notation "sz" => Nat.clog 2 (q+hid+1)
local notation "cs" => columns A.cap N M
local notation "f7" => output A.cap N M A.degree groups d0 (Nat.clog 2 (q+hid+1)) q scale psize config index
local notation "after" => DescentTerminalPointerFrame.result base src (blocks*shops)
  (output A.cap N M A.degree groups d0 (Nat.clog 2 (q+hid+1)) q scale psize config index) before
local notation "first" => base+DescentTerminalPointerFrame.size (columns A.cap N M) d0
local notation "meas" => measured (q:=q) (t:=tags) (H:=hid) (N:=N) (A:=M) (w:=p) (groups:=groups)
variable (b:Fin blocks) (h:Fin shops) (g:Fin groups) (fits:(Nat.clog 2 (q+hid+1))*(N*M)*groups≤wb)
    (atBase:(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).base=(base+DescentTerminalPointerFrame.size (columns A.cap N M) d0)+b.val*shops)
    (keep:shops≤(machine.channel (finProdFinEquiv (b,(7:Fin 8).succ))).size)
    (publicRoom:DescentTerminalGraphRows.arity W.graph p v≤q) (privateRoom:Fintype.card r.UsedWord≤hid)
    (read:SourceRead config (DescentTerminalPointerDigits.low (H:=(blocks*shops)) (d:=d0) src before (finProdFinEquiv (b,h))) g.val t)
    (origin:Origin W.graph v r birth nodes arity aliases
      (DescentTerminalPortChart.rank A native S ready names v port) port
      (reindexed t (index
        (DescentTerminalPointerDigits.low (H:=(blocks*shops)) (d:=d0) src before (finProdFinEquiv (b,h)) (mcol (cap:=A.cap) (N:=N) (A:=M))).val
        (DescentTerminalPointerDigits.low (H:=(blocks*shops)) (d:=d0) src before (finProdFinEquiv (b,h)) (fcol (cap:=A.cap) (N:=N) (A:=M))).val)))
    (chips:t.chips=Stage.signedPanel A native S ready names (Stage.home A v))

include coords whole common room fits atBase keep publicRoom privateRoom read origin chips in
/-- A single dictionary serves every block and every physical host in block-major order.
Its invoice charges the dictionary once and one scan step per block/host pair. -/
theorem primitive_rows :
    (DescentTerminalPointerFrame.program wb base src (blocks*shops) f7).Exec before after
      ((4+10*DescentTerminalPointerFrame.size cs d0)+(4+(blocks*shops)*(16+26*cs))) ∧
    CheapCode (DescentTerminalPointerFrame.program wb base src (blocks*shops) f7) ∧
    (∀u (j:Fin (r.arity u)),
      venueField (cellAt (meas machine after h) (finProdFinEquiv (g,b)))
        (nodeArg (row r birth nodes u) (j.castLE (arity u)))=
      (((numbered G' hp v rk r.restricted code).operand u j).elim (fun a=>a.val+1) (fun a=>q+(ordinal chart a).val+1))) ∧
    ∀z,z<base ∨ first+blocks*shops≤z→after z=before z := by
  have full:=primitive_word (q:=q) (hid:=hid) A native S ready names v coords port hp scale psize whole common r code birth nodes arity
    aliases t config index base src before room (finProdFinEquiv (b,h)) g fits publicRoom privateRoom read origin chips
  refine ⟨full.1,full.2.1,?_,full.2.2.2⟩
  intro u j
  have span:=room.limit
  have bound:shops≤blocks*shops:=by
    simpa using Nat.mul_le_mul_right shops (Nat.succ_le_of_lt (Nat.zero_lt_of_lt b.isLt))
  have hostWord:shops≤2^wb:=by omega
  have address : first+b.val*shops+h.val=first+(finProdFinEquiv (b,h)).val:=by
    rw [finProdFinEquiv_apply_val]
    ring
  have observed:=family_digit (q:=q) (hid:=hid) (tags:=tags) (p:=p) machine after (first+b.val*shops) b atBase keep hostWord h g
    (row r birth nodes u) (j.castLE (arity u))
  rw [address] at observed
  exact observed.trans (full.2.2.1 u j)

end AllBlocks

end Reached


end
end Hierarchy.DescentTerminalPointerIssue

end OAI

import OAI.Hierarchy.DescentIssuedGoodHeaders
import OAI.Hierarchy.DescentResetLocalRoster
import OAI.Hierarchy.DescentRotorWindowBases

namespace OAI
/-! # Select the portable root from the attained signed port and its two earlier endpoint stencils -/
namespace Hierarchy.DescentSenderRootStencil
open DescentResetLocalRoster DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open DescentPacking.PackedMatch.Local.Gather DescentSharedCableNames DescentFallbackShapeTable DescentHostDirectory
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M w field : ℕ}

def choose (r Y first peer : ℕ) : Option (Root r Y) :=
  if first%2=0 ∧ peer%2=0 then
    let raw:=first/2/(Y+1)
    let key:=(raw/2^r,raw%2^r)
    if inside : key∈codes r then some (.inl ⟨key,inside⟩) else none
  else
    let z:=decode r Y (first/2)
    if inside : z.1∈codes r then some (.inr (⟨z.1,inside⟩,z.2)) else none

def owner (r Y : ℕ) (x : Fin 3→Cell field) : Cell (Packed.bits (rootSlots r Y)) :=
  if (x 0).val=0 then 0 else Packed.token ((choose r Y (x 1).val (x 2).val).map (rootId r Y))

theorem paid {r Y : ℕ} (q : code r) (x : Fin 3→Cell field) (live : (x 0).val≠0)
    (use : (x 1).val%2=0 ∧ (x 2).val%2=0) (observed : (x 1).val/2/(Y+1)=q.val.1*2^r+q.val.2)
    (low : q.val.2<2^r) : (owner r Y x).val=(rootId r Y (.inl q)).val+1 := by
  rcases q with ⟨⟨a,b⟩,hq⟩
  dsimp only at observed low
  have high : (a*2^r+b)/2^r=a := by
    rw [Nat.mul_comm a,Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt low,Nat.add_zero]
  simp [owner,live,choose,use,observed,high,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt low,hq,Packed.token]

theorem tree {r Y : ℕ} (q : code r×Option (Fin Y)) (x : Fin 3→Cell field) (live : (x 0).val≠0)
    (unused : ¬((x 1).val%2=0 ∧ (x 2).val%2=0))
    (observed : (x 1).val/2=cell r (q.1.val,q.2)) (depth : q.1.val.1≤r) (small : q.1.val.2<2^q.1.val.1) :
    (owner r Y x).val=(rootId r Y (.inr q)).val+1 := by
  simp [owner,live,choose,unused,observed,decode_cell r (q.1.val,q.2) depth small,q.1.property,Packed.token]

theorem issue (r Y : ℕ)
    (tables : Fin 3→Tables) (reads : Fin 3→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 3→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*3) (Packed.bits (rootSlots r Y)) M H G w out.base)
    (rom : resident (owner r Y ∘ (encode field 3).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*3)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>owner r Y (x a g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words (owner r Y) tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentSenderRootStencil

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentResetAttachments DescentRelativeContacts DescentFallbackShapeTable DescentCanonicalPorts
open DescentRotorWindowScore DescentPackedTicketChronology DescentSIMDLookup DescentPacking
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k)
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site =>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "r" => (Z.k-c)
local notation "Y" => (2^Z.n:ℕ)
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "endAt" => DescentIssuedFallbackPanel.endSite (W:=W) A
local notation "use" => useRotor (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "headAt" => base (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "wireWord" => peerShapeWord A S ready digits Z T frm


open DescentSenderRootStencil
local notation "wireAt" => fun s e=>wireWord s (home A (endAt s e))
local notation "expt" => exceptionalCell A S ready digits Z T frm

theorem sender_mode (s : Bool) (e : E) : (wireAt s e%2=0 ∧ wireAt (!s) e%2=0) ↔ use e := by
  have compare:=cell_mode A S ready digits Z T frm s e
  cases ha : expt (home A (endAt s e)) <;> cases hb : expt (home A (endAt (!s) e)) <;>
    simp [peerShapeWord,ha,hb] at compare ⊢ <;> tauto

theorem paid_stencil_root {field : ℕ} (s : Bool) (p : {e : E // use e}) (x : Fin 3→Cell field)
    (live : (x 0).val≠0) (atOwn : (x 1).val=wireAt s p.val) (atPeer : (x 2).val=wireAt (!s) p.val) :
    (DescentSenderRootStencil.owner r Y x).val=
      (DescentResetLocalRoster.rootId r Y (.inl (Z.goodLabel T (headAt p s)))).val+1 := by
  apply paid _ x live
  · rw [atOwn,atPeer]
    exact (sender_mode A S ready digits Z T frm s p.val).mpr p.property
  · rw [atOwn]
    exact rotorInterval A S ready digits Z T frm p s
  · exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide)
      (Nat.sub_le_sub_right ((R).depth _) _))

theorem fallback_stencil_root {field : ℕ} (s : Bool) (e : E) (t : Z.Fallback)
    (miss : ¬use e) (here : falls A S ready Z s t e) (x : Fin 3→Cell field)
    (live : (x 0).val≠0) (atOwn : (x 1).val=wireAt s e) (atPeer : (x 2).val=wireAt (!s) e) :
    (DescentSenderRootStencil.owner r Y x).val=
      (DescentResetLocalRoster.rootId r Y (Z.rootTicket T (.inr t))).val+1 := by
  apply tree (Z.fallLabel T t,(T.code t).2.2) x live
  · rw [atOwn,atPeer]
    exact mt (sender_mode A S ready digits Z T frm s e).mp miss
  · rw [atOwn]
    have half (v : Bool) (z : ℕ) : (2*z+v.toNat)/2=z := by
      cases v <;> simp [Bool.toNat]
      all_goals omega
    simp only [peerShapeWord,half]
    exact congrArg (fun t => (chartShape A S ready Z T t).val)
      ((cell_home A S ready digits Z T frm s e).trans (falls_home A S ready Z T here))
  · exact Nat.sub_le_sub_right (T.codeLegal t).2.1 _
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)

end
end Hierarchy.DescentSixParty.GroupStage

end OAI

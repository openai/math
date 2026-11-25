import OAI.Hierarchy.DescentPackedMatchShape
import OAI.Hierarchy.DescentDatedMatcherRead
import OAI.Hierarchy.DescentDatedOriginRoom
import OAI.Hierarchy.DescentDonorTerrain
import OAI.Hierarchy.DescentDonorParts

namespace OAI
/-! # Resolve the earlier matcher at the old source's actual winner leaf -/
namespace Hierarchy.DescentOperandPriorIncidence.TerrainAnchor
open DescentSIMDLookup DescentRawCablePanel.DepotRAM DescentPackedZip
open DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
abbrev Format := DescentRawCablePanel.DepotRAM.Shape

/-- A page has a fixed possible source block. The query contains only the
old outgoing position and the target flag, even at a stage with many blocks. -/
def ticket (f : Format) (s : Fin f.cap) (target : Bool) : Cell (originBits f) :=
  ((1+2*s.val+target.toNat:ℕ):Cell (originBits f))

theorem ticket_val (f : Format) (s : Fin f.cap) (target : Bool) :
    (ticket f s target).val=1+2*s.val+target.toNat := by
  apply Fin.val_cast_of_lt
  have big:=origin_role_fits f s (1:Fin 11)
  cases target <;> simp only [Bool.toNat] <;> norm_num at big ⊢ <;> omega

/-- This is the same 12-column matcher transform as the original topology
bank. Its leaf comes from the named old source block's saved winner. -/
def records (f : Format) (profile : ℕ) (x : Fin f.blocks) (data : Parts f) :=
  let u:=(ParentIncidence.splitTerrain data.terrain).2
  let s:=shape f.blocks f.degree (2*f.cap) profile
  let inp:=inputs s f.cap (leaf (u.winner x).val) u (fun _=>0)
  fun j i=>((DescentPacking.PackedMatch.transform inp).row j i).val

def field (f : Format) (profile outBits : ℕ) (x : Fin f.blocks) (i : Fin 5)
    (data : Cell (totalBits f)) (key : Cell (originBits f)) : Cell outBits :=
  if key.val=0 then 0 else
    let rest:=key.val-1
    let old:=x.val*(2*f.cap)+rest/2
    let chosen:=Stage.retarget (records f profile x (separate f data)) (decide (rest%2=1)) old
    ((Stage.anchorColumns f.cap chosen i:ℕ):Cell outBits)

theorem field_empty (f : Format) (profile outBits : ℕ) (x : Fin f.blocks) (i : Fin 5) (data : Cell (totalBits f)) :
    field f profile outBits x i data 0=0 := by simp [field]

theorem field_read (f : Format) (profile outBits : ℕ) (x : Fin f.blocks) (i : Fin 5)
    (data : Parts f) (old : Fin f.cap) (target : Bool) :
    field f profile outBits x i (combine f data) (ticket f old target)=
      (Stage.anchorColumns f.cap (Stage.retarget (records f profile x data) target (x.val*(2*f.cap)+old.val)) i:Cell outBits) := by
  have seen:=ticket_val f old target
  have live : (ticket f old target).val≠0 := by omega
  simp only [field,seen,separate_combine]
  have odd : (1+(old.val)*2)/2=old.val := by omega
  cases target <;> simp [Bool.toNat,Nat.mul_comm 2 old.val,odd]

def gate (f : Format) (profile outBits : ℕ) (x : Fin f.blocks) (i : Fin 5) : Book.Gate :=
  ⟨totalBits f,originBits f,outBits,field f profile outBits x i⟩

theorem paid (f : Format) (profile outBits : ℕ) (x : Fin f.blocks) (i : Fin 5) (old : Fin f.cap)
    (unit M w : ℕ) (funded : 2*totalBits f+1≤unit) (lanes : M*unit≤w/2) :
    let g:=gate f profile outBits x i
    (g.left+g.right)*M≤w/2 :=
  (origin_lookup_paid f (Nat.zero_lt_of_lt x.isLt) (Nat.zero_lt_of_lt old.isLt) unit M w funded lanes).2

theorem run {H G M w : ℕ} (f : Format) (profile outBits : ℕ) (block : Fin f.blocks) (i : Fin 5)
    (tables : Tables) (parts select : Bank) (out : ℕ) (m : Memory w)
    (x : Fin H → Fin G → Parts f) (keys : Fin H → Fin G → Cell (originBits f))
    (fit : DescentPackedZip.Fits tables (.lookup parts .row) (.lookup select .row) (totalBits f) (originBits f) M out w)
    (safe : out+H*chunks G M<2^w) (rom : Static tables (field f profile outBits block i) M m)
    (before : Source (.lookup parts .row) (fun h g=>combine f (x h g)) M m)
    (query : Source (.lookup select .row) keys M m) :
    let term:=tables.read (.lookup parts .row) (.lookup select .row)
    let final:=image out (H*chunks G M) term m
    (scan w out (H*chunks G M) term).Exec m final (4+(H*chunks G M)*(2*term.work+4)) ∧
      (∀p : Row H G M,final (out+(row H G M p).val)=((data (fun h g=>
        field f profile outBits block i (combine f (x h g)) (keys h g)) p).val:Word w)) ∧
      (∀j,j<out ∨ out+H*chunks G M≤j → final j=m j) ∧ CheapCode (scan w out (H*chunks G M) term) :=
  lookup_run _ (field_empty f profile outBits block i 0) _ _ _ _ _ _ _ fit safe rom before query

end
end Hierarchy.DescentOperandPriorIncidence.TerrainAnchor

end OAI

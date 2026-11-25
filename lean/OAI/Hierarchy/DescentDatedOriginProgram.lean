import OAI.Hierarchy.DescentDatedOriginCodes
import OAI.Hierarchy.DescentDatedOperandDigits
import OAI.Hierarchy.DescentDonorParts
import OAI.Hierarchy.DescentDatedOperandLookup

namespace OAI
/-! # Numeric old-wire queries from the earlier three operand columns -/
namespace Hierarchy.DescentOperandPriorIncidence.Origin
open DescentSIMDLookup DescentPackedZip DescentRawCablePanel.DepotRAM
open DescentTerminalSignedGrainWord DescentSharedCableNames
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- Positive peer token. The zero word also covers a private operand or pin. -/
def peerWord {s : ℕ} (kind peer : Cell s) : Cell (s+1) :=
  if kind.val=1 then ((1+peer.val : ℕ):Cell (s+1)) else 0

theorem peer_on {s : ℕ} (kind peer : Cell s) (hit : kind.val=1) : (peerWord kind peer).val=1+peer.val := by
  have bd:=peer.isLt
  have low:=Nat.two_pow_pos s
  have fits : 1+peer.val<2^(s+1) := by rw [pow_succ];omega
  rw [peerWord,ite_eq_left hit]
  exact Fin.val_cast_of_lt fits

@[simp] theorem peer_off (s : ℕ) : peerWord (0:Cell s) 0=0 := by simp [peerWord]

/-- Assemble the prior local name using the original cap, regardless of which
bit-word of the old cable the current gate uses. -/
def oldKey (cap outBits : ℕ) {a s : ℕ} (tag : Cell a) (first : Cell s) : Cell outBits :=
  if tag.val=0 then 0 else ((1+(tag.val-1)*cap+first.val : ℕ):Cell outBits)

@[simp] theorem oldKey_hole (cap outBits a s : ℕ) : oldKey cap outBits (0:Cell a) (0:Cell s)=0 := by
  simp [oldKey]

theorem key_of_header {s : ℕ} (cap outBits : ℕ) (kind peer first : Cell s)
    (cable : kind.val=1) (small : 1+peer.val*cap+first.val<2^outBits) :
    (oldKey cap outBits (peerWord kind peer) first).val=1+peer.val*cap+first.val := by
  have positive : 1+peer.val≠0:=by omega
  have untag : 1+peer.val-1=peer.val:=by omega
  rw [oldKey,peer_on kind peer cable,ite_eq_right positive,untag]
  exact Fin.val_cast_of_lt small

def signedWord (f : Shape) (block : Fin f.blocks) (v : Parts f) (j : Fin (2*f.cap)) :
    Cell (DescentSignedCableCodec.width f.degree f.cap) :=
  (encode _ (f.blocks*(2*f.cap))).symm v.cables (finProdFinEquiv (block,j))

/-- The records supply the old outgoing ordinal, its source/target orientation
and old peer. The latter fields locate the original positive donor’s page
when the old operand was attached to its target. -/
def readOrigin (f : Shape) (block : Fin f.blocks) (s outBits : ℕ) (role : Fin 11) (field : Fin 4)
    (data : Cell (totalBits f)) (key : Cell s) : Cell outBits :=
  if key.val=0 then 0 else
  let record:=origin (D:=f.degree) (cap:=f.cap) (signedWord f block (separate f data)) (key.val-1,0)
  record.elim 0 (fun r=>
    let values : Fin 4→ℕ:=![Operand.ticket r.sourceWire role,1+r.neighbor.val,r.target.toNat,1+r.sourceWire.val]
    (values field:Cell outBits))

theorem readOrigin_empty (f : Shape) (block : Fin f.blocks) (s outBits : ℕ) (role : Fin 11) (field : Fin 4)
    (v : Cell (totalBits f)) : readOrigin f block s outBits role field v 0=0 := by simp [readOrigin]

theorem readOrigin_real (f : Shape) (block : Fin f.blocks) (s outBits : ℕ) (role : Fin 11)
    (v : Parts f) (key : Cell s) (name : ℕ) (r : Stage.Live f.degree f.cap)
    (pointer : key.val=1+name) (hit : origin (D:=f.degree) (cap:=f.cap) (signedWord f block v) (name,0)=some r) :
    readOrigin f block s outBits role 0 (combine f v) key=(Operand.ticket r.sourceWire role:Cell outBits) ∧
      readOrigin f block s outBits role 1 (combine f v) key=((1+r.neighbor.val : ℕ):Cell outBits) ∧
      readOrigin f block s outBits role 2 (combine f v) key=(r.target.toNat:Cell outBits) ∧
      readOrigin f block s outBits role 3 (combine f v) key=((1+r.sourceWire.val : ℕ):Cell outBits) := by
  have yes : key.val≠0 := by omega
  have pred : key.val-1=name := by omega
  simp [readOrigin,yes,pred,separate_combine,hit]

/-- The three original projections are read by two packed scans. A following
scan joins the resulting key with the earlier finite local donor window. All
three tables are independent of the operand data in private memory. -/
def gates (f : Shape) (block : Fin f.blocks) (s keyBits outBits : ℕ) (role : Fin 11) (field : Fin 4) : Fin 3→Book.Gate :=
  ![⟨s,s,s+1,peerWord⟩,⟨s+1,s,keyBits,oldKey f.cap keyBits⟩,
    ⟨totalBits f,keyBits,outBits,readOrigin f block keyBits outBits role field⟩]

theorem run {H G M w : ℕ} (f : Shape) (block : Fin f.blocks) (s outBits : ℕ) (role : Fin 11) (field : Fin 4)
    (tables : Tables) (prior select : Bank) (out : ℕ) (m : Memory w)
    (x : Fin H→Fin G→Parts f) (key : Fin H→Fin G→Cell s)
    (fit : DescentPackedZip.Fits tables (.lookup prior .row) (.lookup select .row) (totalBits f) s M out w)
    (safe : out+H*chunks G M<2^w) (rom : Static tables (readOrigin f block s outBits role field) M m)
    (before : Source (.lookup prior .row) (fun h g=>combine f (x h g)) M m)
    (query : Source (.lookup select .row) key M m) :
    let term:=tables.read (.lookup prior .row) (.lookup select .row)
    let last:=image out (H*chunks G M) term m
    (scan w out (H*chunks G M) term).Exec m last (4+(H*chunks G M)*(2*term.work+4)) ∧
      (∀p : Row H G M,last (out+(row H G M p).val)=((data (fun h g=>
        readOrigin f block s outBits role field (combine f (x h g)) (key h g)) p).val:Word w)) ∧
      (∀i,i<out ∨ out+H*chunks G M≤ i → last i=m i) ∧ CheapCode (scan w out (H*chunks G M) term) :=
  lookup_run _ (readOrigin_empty f block s outBits role field 0) _ _ _ _ _ _ _ fit safe rom before query

end
end Hierarchy.DescentOperandPriorIncidence.Origin

end OAI

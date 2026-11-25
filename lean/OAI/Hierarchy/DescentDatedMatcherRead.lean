import OAI.Hierarchy.DescentPackedMatchingCell
import OAI.Hierarchy.DescentDatedOperandLookup

namespace OAI
/-! # Native bounded read of the old matched target's true donor and role -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
def matchColumn (thick : Bool) : Fin 12 := if thick then 8 else 5

/-- A target on either replaced demand arm must use the first original wire
of the pair. Field eight contains that handle on both sides of the match. -/
def matchingRow {n : ℕ} (records : Fin n→Fin 12→ℕ) (thick : Bool) (key : ℕ) :=
  (List.finRange n).find? (fun j=>decide (records j 0=1 ∧ records j (matchColumn thick)=key))

def selectedAnchor {n : ℕ} (records : Fin n→Fin 12→ℕ) (thick : Bool) (key : ℕ) :=
  (matchingRow records thick key).map (fun j=>(records j 8,if thick then (1:ℕ) else 2))

/-- A source incidence keeps its original label, including on a signed loop.
A replaced target reads its pair's first donor and its own arm number. -/
def retarget {n : ℕ} (records : Fin n→Fin 12→ℕ) (target : Bool) (key : ℕ) : ℕ×ℕ :=
  if target then
    ((selectedAnchor records true key).orElse (fun _=>selectedAnchor records false key)).getD (key,0)
  else (key,0)

@[simp] theorem retarget_source {n : ℕ} (records : Fin n→Fin 12→ℕ) (key : ℕ) :
    retarget records false key=(key,0) := rfl

/-- The field indices and digit order of the stored physical topology word. -/
def topologyRecord (s : Shape) (packet : Cell s.outputBits) (j : Fin s.pairs) (f : Fin 12) :=
  digit s.digit (1+(finProdFinEquiv (j,f)).val) packet.val

/-- Zero denotes a padded lane. On real lanes the query holds the old
source-block/outgoing-slot handle and the direction of the actual incidence. -/
def anchorQuery (d key : ℕ) (target : Bool) : Cell (d+2) := ((1+2*key+target.toNat : ℕ):Cell (d+2))

theorem query_val {d key : ℕ} (small : key<2^d) (target : Bool) :
    (anchorQuery d key target).val=1+2*key+target.toNat := by
  apply Fin.val_cast_of_lt
  have one:=Nat.two_pow_pos d
  cases target <;> simp only [Bool.toNat, pow_add] <;> norm_num <;> omega

def anchorColumns (cap : ℕ) (v : ℕ×ℕ) : Fin 5→ℕ :=
  let block:=v.1/(2*cap)
  let old:=v.1%(2*cap)
  ![1+block,1+old,v.2,1+11*old+v.2,1+11*(block*cap+old)+v.2]

def anchorField (s : Shape) (cap : ℕ) (field : Fin 5)
    (packet : Cell s.outputBits) (q : Cell (s.digit+2)) : Cell (s.digit+4) :=
  if q.val=0 then 0 else
    let k:=q.val-1
    let a:=retarget (topologyRecord s packet) (decide (k%2=1)) (k/2)
    ((anchorColumns cap a field:ℕ):Cell (s.digit+4))

theorem anchor_padding (s : Shape) (cap : ℕ) (i : Fin 5) (v : Cell s.outputBits) :
    anchorField s cap i v 0=0 := by simp [anchorField]

theorem anchor_read (s : Shape) (cap key : ℕ) (i : Fin 5) (v : Cell s.outputBits)
    (target : Bool) (small : key<2^s.digit) :
    anchorField s cap i v (anchorQuery s.digit key target)=
      (anchorColumns cap (retarget (topologyRecord s v) target key) i:Cell (s.digit+4)) := by
  have q:=query_val small target
  have nz : (anchorQuery s.digit key target).val≠0 := by omega
  simp only [anchorField,q]
  have odd : (1+(key)*2)/2=key := by omega
  cases target <;> simp [Bool.toNat, Nat.mul_comm 2 key,odd]

def anchorGate (s : Shape) (cap : ℕ) (field : Fin 5) : Book.Gate :=
  ⟨s.outputBits,s.digit+2,s.digit+4,anchorField s cap field⟩

/-- The bank contains the actual registered topology packet at each source
colony. All rows use the same fixed read circuit, including partial batches. -/
theorem anchor_run {H G M w : ℕ} (s : Shape) (cap : ℕ) (i : Fin 5) (tables : Tables)
    (packet query : Expr) (out : ℕ) (m : Memory w) (v : Fin H→Fin G→Cell s.outputBits)
    (q : Fin H→Fin G→Cell (s.digit+2))
    (fit : Fits tables packet query s.outputBits (s.digit+2) M out w)
    (room : out+H*chunks G M<2^w) (rom : Static tables (anchorField s cap i) M m)
    (read : Source packet v M m) (key : Source query q M m) :
    let term:=tables.read packet query
    let last:=image out (H*chunks G M) term m
    (scan w out (H*chunks G M) term).Exec m last (4+(H*chunks G M)*(2*term.work+4)) ∧
      (∀r : Row H G M,last (out+(row H G M r).val)=
        ((data (fun h g=>anchorField s cap i (v h g) (q h g)) r).val:Word w)) ∧
      (∀n,n<out ∨ out+H*chunks G M≤ n → last n=m n) ∧ CheapCode (scan w out (H*chunks G M) term) :=
  lookup_run (anchorField s cap i) (anchor_padding s cap i 0) tables packet query out m v q fit room rom read key

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI

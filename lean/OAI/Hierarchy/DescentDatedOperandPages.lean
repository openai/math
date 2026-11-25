import OAI.Hierarchy.DescentDatedTerrainSibling
import OAI.Hierarchy.DescentDatedOriginProgram
import OAI.Hierarchy.DescentSignedRoleScans
import OAI.Hierarchy.DescentActorRechunk
import OAI.Hierarchy.DescentDatedOverlapAperture
import OAI.Hierarchy.DescentOverlapBooks

namespace OAI
/-! # Original operand fields computed at the donor, before the change of lane count

All fields are evaluated on the same retained physical parts word. The
first family searches a prior signed name at the old actor. The second
family reads the genuine match at the old source. Only short numerical
results enter the shared overlap pass.
-/
namespace Hierarchy.DescentDatedOperandPages
open DescentSIMDLookup DescentPackedColony DescentRawCablePanel.DepotRAM
open DescentOperandPriorIncidence DescentSixParty.Chronology DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (f : Shape)

def headerCount := f.blocks*(f.degree*(f.cap*4))
def anchorCount := f.blocks*(f.cap*(3*5))
def count := headerCount f+anchorCount f

def header (x : Fin f.blocks) (peer : Fin f.degree) (first : Fin f.cap) (j : Fin 4) : Fin (count f) :=
  Fin.castAdd (anchorCount f) (finProdFinEquiv (x,finProdFinEquiv (peer,finProdFinEquiv (first,j))))

def anchor (x : Fin f.blocks) (old : Fin f.cap) (target : Fin 2) (j : Fin 5) : Fin (count f) :=
  Fin.natAdd (headerCount f) (finProdFinEquiv (x,finProdFinEquiv (old,finProdFinEquiv (target.castLE (by decide : 2≤3),j))))

def sibling (x : Fin f.blocks) (old : Fin f.cap) (j : Fin 5) : Fin (count f) :=
  Fin.natAdd (headerCount f) (finProdFinEquiv (x,finProdFinEquiv (old,finProdFinEquiv ((2:Fin 3),j))))

def law (profile b : ℕ) (i : ℕ) (source : Cell (totalBits f)) : Cell b :=
  if h : i<count f then
    Fin.addCases (fun lo : Fin (headerCount f)=>
      let (x,rest):=finProdFinEquiv.symm lo
      let (peer,tail):=finProdFinEquiv.symm rest
      let (first,j):=finProdFinEquiv.symm tail
      let key : Cell (originBits f):=((1+peer.val*f.cap+first.val:ℕ):Cell _)
      Origin.readOrigin f x (originBits f) b 0 j source key)
    (fun hi : Fin (anchorCount f)=>
      let (x,rest):=finProdFinEquiv.symm hi
      let (old,tail):=finProdFinEquiv.symm rest
      let (target,j):=finProdFinEquiv.symm tail
      if target.val=2 then TerrainAnchor.siblingField f profile b x old j source
      else TerrainAnchor.field f profile b x j source (TerrainAnchor.ticket f old (decide (target.val=1))))
    (⟨i,h⟩ : Fin (count f))
  else 0

theorem header_value (profile b : ℕ) (x : Fin f.blocks) (peer : Fin f.degree) (first : Fin f.cap) (j : Fin 4)
    (v : Parts f) :
    law f profile b (header f x peer first j).val (combine f v)=
      Origin.readOrigin f x (originBits f) b 0 j (combine f v) ((1+peer.val*f.cap+first.val:ℕ):Cell _) := by
  rw [law,dite_eq_left (header f x peer first j).isLt]
  simp only [Fin.eta]
  simp only [header,count,headerCount,anchorCount]
  rw [Fin.addCases_left]
  simp only [Equiv.symm_apply_apply]

theorem anchor_value_data (profile b : ℕ) (x : Fin f.blocks) (old : Fin f.cap) (target : Fin 2) (j : Fin 5)
    (data : Cell (totalBits f)) :
    law f profile b (anchor f x old target j).val data=
      TerrainAnchor.field f profile b x j data (TerrainAnchor.ticket f old (decide (target.val=1))) := by
  rw [law,dite_eq_left (anchor f x old target j).isLt]
  have two:target.val≠2:=Nat.ne_of_lt target.isLt
  simp only [Fin.eta]
  simp only [anchor,count,headerCount,anchorCount]
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply,Fin.val_castLE,ite_eq_right two]

theorem sibling_value_data (profile b : ℕ) (x : Fin f.blocks) (old : Fin f.cap) (j : Fin 5) (data : Cell (totalBits f)) :
    law f profile b (sibling f x old j).val data=TerrainAnchor.siblingField f profile b x old j data := by
  rw [law,dite_eq_left (sibling f x old j).isLt]
  simp only [Fin.eta]
  simp only [sibling,count,headerCount,anchorCount]
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply,
    ite_eq_left (show (2 : Fin 3).val=2 from rfl)]

theorem anchor_value (profile b : ℕ) (x : Fin f.blocks) (old : Fin f.cap) (target : Fin 2) (j : Fin 5)
    (v : Parts f) :
    law f profile b (anchor f x old target j).val (combine f v)=
      TerrainAnchor.field f profile b x j (combine f v) (TerrainAnchor.ticket f old (decide (target.val=1))) :=
  anchor_value_data f profile b x old target j (combine f v)

theorem sibling_value (profile b : ℕ) (x : Fin f.blocks) (old : Fin f.cap) (j : Fin 5) (v : Parts f) :
    law f profile b (sibling f x old j).val (combine f v)=TerrainAnchor.siblingField f profile b x old j (combine f v) :=
  sibling_value_data f profile b x old j (combine f v)

structure Layout where
  hosts : ℕ
  groups : ℕ
  old : ℕ
  newLanes : ℕ
  bits : ℕ
  profile : ℕ

variable (l : Layout)
local notation "H₀" => l.hosts
local notation "G₀" => l.groups
local notation "L₀" => l.old
local notation "L₁" => l.newLanes
local notation "b" => l.bits
local notation "n" => H₀*chunks G₀ L₀
local notation "N" => count f
local notation "calcLaw" => law f l.profile l.bits

def sourceRows (base : ℕ) : Bank :=
  ⟨RoleScans.home (totalBits f) H₀ G₀ L₀ N base,Nat.clog 2 (N*n+1)⟩

def scratch (base : ℕ) := (sourceRows f l base).base+(sourceRows f l base).size
def repack (base : ℕ) : Overlap.Job := ⟨sourceRows f l base,N*H₀,G₀,L₀,L₁,b⟩
def dataEnd (base : ℕ) := (repack f l base).limit (scratch f l base)
def lastAddress (base : ℕ) := dataEnd f l base+2^Nat.clog 2 (H₀*chunks G₀ L₁)
def resultBank (base : ℕ) (j : Fin N) : Bank :=
  ⟨((repack f l base).target (scratch f l base)).base+j.val*(H₀*chunks G₀ L₁),
    Nat.clog 2 (H₀*chunks G₀ L₁)⟩

def evaluate (base w : ℕ) (src : Bank) : NativePhase w :=
  ⟨RoleScans.cpu calcLaw H₀ G₀ L₀ w base N src,RoleScans.ticks (totalBits f) H₀ G₀ L₀ N,
    RoleScans.image calcLaw H₀ G₀ L₀ base N src,
    cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@ProtocolRAM.program_cheap _ _)⟩
def phase (base w : ℕ) (src : Bank) : NativePhase w :=
  (evaluate f l base w src).seq ((repack f l base).phase (scratch f l base) w)

theorem affine (base : ℕ) : lastAddress f l base=base+lastAddress f l 0 := by
  have atBase:=Overlap.address_affine (scratch f l base) (N*H₀) G₀ L₀ L₁ b
  have atZero:=Overlap.address_affine (scratch f l 0) (N*H₀) G₀ L₀ L₁ b
  change Overlap.endAddress (scratch f l base) (N*H₀) G₀ L₀ L₁ b + _ =
    base + (Overlap.endAddress (scratch f l 0) (N*H₀) G₀ L₀ L₁ b + _)
  rw [atBase,atZero]
  simp [scratch,sourceRows,RoleScans.home,Bank.size,Nat.add_assoc]

theorem scratch_bounds (base : ℕ) :
    RoleScans.limit (totalBits f) H₀ G₀ L₀ base N ≤ scratch f l base ∧
      N*H₀*chunks G₀ L₀ ≤ (sourceRows f l base).size := by
  have h : N*n ≤ 2^Nat.clog 2 (N*n+1) := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  exact ⟨Nat.add_le_add_left h _,by simpa only [sourceRows,Bank.size,Nat.mul_assoc] using h⟩

theorem returned_room {w : ℕ} (base : ℕ) (space : lastAddress f l base<2^w) (j : Fin N) :
    (resultBank f l base j).Fits w (lastAddress f l base) ∧ H₀*chunks G₀ L₁≤(resultBank f l base j).size := by
  let tiles:=H₀*chunks G₀ L₁
  let top:=((repack f l base).target (scratch f l base)).base
  have tail : dataEnd f l base ≤ lastAddress f l base:=Nat.le_add_right ..
  have roof:=Overlap.output_fits (scratch f l base) (N*H₀) G₀ L₀ L₁ b w (tail.trans_lt space)
  have whole:top+N*tiles ≤ dataEnd f l base := by
    simpa only [dataEnd,Overlap.Job.limit,Overlap.Job.target,Overlap.outputBank,Overlap.finish,
      repack,top,tiles,Overlap.rows,Nat.mul_assoc] using roof.2.2
  have addr:top+j.val*tiles ≤ dataEnd f l base:=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt.le) _).trans whole
  have cap : 2^Nat.clog 2 tiles < 2^w:=
    (Nat.le_add_left _ (dataEnd f l base)).trans_lt space
  exact ⟨⟨Nat.two_pow_pos _,cap,Nat.add_le_add_right addr _⟩,Nat.le_pow_clog (by decide) _⟩

theorem any {w : ℕ} (base : ℕ) (src : Bank) (m : Memory w) (below : src.base+src.size≤base)
    (rows : n≤ src.size) (lanes : L₀*max (totalBits f) b≤w/2) (space : lastAddress f l base<2^w) :
    let run:=phase f l base w src
    run.Runs m ∧ (∀i,i<base ∨ lastAddress f l base ≤ i → run.image m i=m i) := by
  let end₀:=scratch f l base
  let j:=repack f l base
  let first:=evaluate f l base w src
  have start : base ≤ end₀ := by simp [end₀,scratch,sourceRows,RoleScans.home,Nat.add_assoc]
  have middle : end₀ ≤ dataEnd f l base := by
    change end₀≤Overlap.endAddress end₀ _ _ _ _ _
    rw [Overlap.address_affine]
    omega
  have tail : dataEnd f l base ≤ lastAddress f l base:=Nat.le_add_right ..
  have up:=middle.trans tail
  have bounds:=scratch_bounds f l base
  have seen:=RoleScans.any_run calcLaw base N src m below rows lanes (bounds.1.trans_lt (up.trans_lt space))
  have low : j.src.Fits w end₀:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (up.trans_lt space),le_rfl⟩
  have roof:=Overlap.output_fits end₀ (N*H₀) G₀ L₀ L₁ b w (tail.trans_lt space)
  have moved:=Overlap.any end₀ (N*H₀) G₀ L₀ L₁ b j.src (first.image m) low (roof.2.2.trans_lt (tail.trans_lt space))
  refine ⟨NativePhase.seq_runs first (j.phase end₀ w) m seen.1 moved.1,?_⟩
  rintro i (pre|post)
  · exact (moved.2.1 i (.inl (pre.trans_le start))).trans (seen.2.1 i (.inl pre))
  · exact (moved.2.1 i (.inr (roof.2.2.trans (tail.trans post)))).trans (seen.2.1 i (.inr (bounds.1.trans (up.trans post))))

theorem issued {w : ℕ} (base : ℕ) (src : Bank) (m : Memory w) (v : Fin H₀ → Fin G₀ → Parts f)
    (positive : 0<L₀) (below : src.base+src.size≤base) (rows : n≤ src.size)
    (lanes : L₀*max (totalBits f) b≤w/2) (space : lastAddress f l base<2^w)
    (old : Reads src (fun h g=>combine f (v h g)) L₀ m) :
    let run:=phase f l base w src
    run.Runs m ∧ (∀j : Fin N,Reads (resultBank f l base j) (fun h g=>calcLaw j.val (combine f (v h g))) L₁ (run.image m)) ∧
      (∀i,i<base ∨ lastAddress f l base ≤ i → run.image m i=m i) := by
  let end₀:=scratch f l base
  let j:=repack f l base
  let first:=evaluate f l base w src
  have start : base ≤ end₀ := by simp [end₀,scratch,sourceRows,RoleScans.home,Nat.add_assoc]
  have middle : end₀ ≤ dataEnd f l base := by
    change end₀≤Overlap.endAddress end₀ _ _ _ _ _
    rw [Overlap.address_affine]
    omega
  have tail : dataEnd f l base ≤ lastAddress f l base:=Nat.le_add_right ..
  have up:=middle.trans tail
  have room₀: end₀<2^w:=up.trans_lt space
  have bounds:=scratch_bounds f l base
  have safe:RoleScans.limit (totalBits f) H₀ G₀ L₀ base N<2^w:=bounds.1.trans_lt room₀
  have seen:=RoleScans.any_run calcLaw base N src m below rows lanes safe
  have low : j.src.Fits w end₀:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt room₀,le_rfl⟩
  have roof:=Overlap.output_fits end₀ (N*H₀) G₀ L₀ L₁ b w (tail.trans_lt space)
  have prior (k : Fin N) (p : Row H₀ G₀ L₀) :=
    RoleScans.read calcLaw base N src m below rows lanes safe (fun h g=>combine f (v h g)) old k p
  let fields:=fun (k : Fin N) h g=>calcLaw k.val (combine f (v h g))
  have changed:=DescentActorRaster.change_pitch fields end₀ j.src (first.image m) positive low bounds.2 (roof.2.2.trans_lt (tail.trans_lt space)) prior
  refine ⟨NativePhase.seq_runs _ _ m seen.1 changed.1,fun k p=>changed.2.1 k p,?_⟩
  rintro i (pre|post)
  · exact (changed.2.2.1 i (.inl (pre.trans_le start))).trans (seen.2.1 i (.inl pre))
  · exact (changed.2.2.1 i (.inr (roof.2.2.trans (tail.trans post)))).trans (seen.2.1 i (.inr (bounds.1.trans (up.trans post))))

end
end Hierarchy.DescentDatedOperandPages

end OAI

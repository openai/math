import OAI.Hierarchy.TaggedWideDatedROM

namespace OAI
/-! # Exact original static data for every sparse and dense numerical page -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing BigOperators
variable {W T : ℕ}

private theorem find_hit {α : Type*} (xs : List (Option α)) (a : α) (present : some a∈xs)
    (each : ∀x∈xs,x=none ∨ x=some a) : xs.findSome? id=some a := by
  induction xs with
  | nil=>simp at present
  | cons x xs ih=>
    obtain hz|hz:=each x (List.mem_cons_self ..)
    · rw [List.findSome?_cons,hz]
      apply ih (by simpa [hz] using present)
      exact fun i hi=>each i (List.mem_cons_of_mem _ hi)
    · simp [hz]

private theorem choice {α : Type*} {n : ℕ} (f : Fin n→Option α) (i : Fin n) (a : α) (h : f i=some a)
    (off : ∀j,j≠i→f j=none) : (List.ofFn f).findSome? id=some a := by
  apply find_hit _ _ (List.mem_ofFn.mpr ⟨i,h⟩)
  intro x hx
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx
  by_cases eq:j=i
  · exact Or.inr (eq ▸ h)
  · exact Or.inl (off j eq)

open private emptyFn from OAI.Hierarchy.TaggedWideDatedROM in
private theorem absent {α : Type*} {n : ℕ} (f : Fin n→Option α) (h : ∀j,f j=none) :
    (List.ofFn f).findSome? id=none := emptyFn f h

private theorem blockAway (b n a : ℕ) (i j : ℕ) (ij : i≠j) (ha : a<n) :
    b+i*n+a<b+j*n ∨ b+j*n+n≤b+i*n+a := by
  rcases Nat.lt_or_gt_of_ne ij with h|h
  · left
    have step:=Nat.mul_le_mul_right n h
    rw [Nat.succ_mul] at step;omega
  · right
    have step:=Nat.mul_le_mul_right n h
    rw [Nat.succ_mul] at step;omega

theorem Shape.rawWord (g : Shape) (sites base : ℕ) (i : Fin 3) (j : Fin g.count) :
    g.word (W:=W) sites base (base+i.val*g.count+j.val)=
      some ((SiteScatter.directory g.candidates g.parties g.columns i j):Word W) := by
  unfold Shape.word
  rw [choice _ i _ (romAt_hit ..)]
  · rfl
  · intro t ne
    exact romAt_away _ (blockAway _ _ _ _ _ (fun eq=>ne (Fin.ext eq.symm)) j.isLt)

theorem Shape.multiplier (g : Shape) (sites base : ℕ) (s : Fin sites) :
    g.word (W:=W) sites base (base+3*g.count+s.val)=some ((s.val*g.columns:ℕ):Word W) := by
  unfold Shape.word
  rw [absent]
  · exact romAt_hit (base+3*g.count) sites (fun i => i.val*g.columns) s
  · intro t
    apply romAt_away _ (Or.inr ?_)
    have h:=Nat.mul_le_mul_right g.count t.isLt
    rw [Nat.succ_mul] at h
    omega

private theorem offset_before (b : ℕ) (sz : Fin T→ℕ) {i j : Fin T} (ht : i<j) :
    offset b sz i+sz i≤offset b sz j := by
  have part : sz i≤ stride sz := Finset.single_le_sum (fun t _=>Nat.zero_le (sz t)) (Finset.mem_univ i)
  have h:=Nat.mul_le_mul_right (stride sz) ht
  rw [Nat.succ_mul] at h
  unfold offset
  omega

/-- Each true leaf of a finite date directory is visible on its own interval.
The other dates either start later or end earlier. -/
theorem dated_choice (form : Fin T→Shape) (sites b : ℕ) (i : Fin T) (a : ℕ) (word : Word W)
    (lo : offset b (fun j=>(form j).advice sites) i≤a)
    (hi : a<offset b (fun j=>(form j).advice sites) i+(form i).advice sites)
    (data : (form i).word sites (offset b (fun j=>(form j).advice sites) i) a=some word) :
    (List.ofFn fun j=>(form j).word sites (offset b (fun t=>(form t).advice sites) j) a).findSome? id=some word := by
  refine choice _ i _ data ?_
  intro j ne
  apply Shape.word_away
  rcases lt_or_gt_of_ne ne with less|more
  · exact Or.inr ((offset_before b _ less).trans lo)
  · exact Or.inl (hi.trans_le (offset_before b _ more))

variable (p : Dated T) (rom : ℕ) (table : Fin p.siteDirectorySize→ℕ) (transport : Fin p.rawEdges→Bool)
    (m : Memory W)
local notation "image" => p.words rom table transport m

theorem Dated.stride_mounted : RoleROM.Mounted rom (fun i : Fin p.sites=>i.val*p.roleCount) image := by
  intro i
  simp [Dated.words,romAt_hit]

theorem Dated.site_mounted : RoleROM.Mounted (p.siteROM rom) table image := by
  intro i
  have off : rom+p.sites≤p.siteROM rom+i.val := Nat.le_add_right ..
  simp [Dated.words,romAt_away _ (Or.inr off),romAt_hit]

theorem Dated.mask_mounted :
    RoleROM.Mounted (p.maskROM rom) (fun i : Fin p.rawEdges=>(transport i).toNat) image := by
  intro i
  let a:=p.maskROM rom+i.val
  have plant : p.firstROM rom≤p.controlROMStart rom := Nat.le_add_right ..
  have final : p.controlROMStart rom≤p.maskROM rom := Nat.le_add_right ..
  have maskBound : p.maskROM rom ≤ a := Nat.le_add_right ..
  have ballotsBound := final.trans maskBound
  have b1 : p.siteROM rom+p.siteDirectorySize ≤ a := plant.trans ballotsBound
  have b0 : rom+p.sites ≤ a :=
    (show p.siteROM rom ≤ p.firstROM rom from Nat.le_add_right ..).trans b1
  have ba j : (p.ballot j).word (W:=W) p.sites (p.ballotROM rom j) a=none := by
    exact Shape.word_away _ _ _ _ (Or.inr ((extent (p.firstROM rom) _ j).trans ballotsBound))
  have ca j : (p.control j).word (W:=W) p.sites (p.controlROM rom j) a=none := by
    exact Shape.word_away _ _ _ _ (Or.inr ((extent (p.controlROMStart rom) _ j).trans maskBound))
  change image a=_
  simp only [Dated.words,romAt_away _ (Or.inr b0),romAt_away _ (Or.inr b1),absent _ ba,absent _ ca]
  simp only [a,romAt_hit]; rfl

theorem Dated.ballot_word (j : Fin T) (a : ℕ) (w : Word W)
    (lo : p.ballotROM rom j≤a) (hi : a<p.ballotROM rom j+(p.ballot j).advice p.sites)
    (owned : (p.ballot j).word p.sites (p.ballotROM rom j) a=some w) : image a=w := by
  have location : p.firstROM rom≤p.ballotROM rom j := Nat.le_add_right ..
  have afterSite : p.siteROM rom+p.siteDirectorySize≤a := location.trans lo
  have afterStride : rom+p.sites≤a := by have step:p.siteROM rom≤p.firstROM rom:=Nat.le_add_right ..;exact step.trans (location.trans lo)
  have picked:=dated_choice p.ballot p.sites (p.firstROM rom) j a w lo hi owned
  simp only [Dated.words,romAt_away _ (Or.inr afterStride),romAt_away _ (Or.inr afterSite),
    Dated.ballotROM,picked]; rfl

theorem Dated.control_word (j : Fin T) (a : ℕ) (w : Word W)
    (lo : p.controlROM rom j≤a) (hi : a<p.controlROM rom j+(p.control j).advice p.sites)
    (owned : (p.control j).word p.sites (p.controlROM rom j) a=some w) : image a=w := by
  have afterBallots : p.controlROMStart rom≤a := (Nat.le_add_right ..).trans lo
  have afterSite : p.siteROM rom+p.siteDirectorySize≤a := (Nat.le_add_right ..).trans afterBallots
  have afterStride : rom+p.sites≤a := by have h : p.siteROM rom≤p.firstROM rom:=Nat.le_add_right ..;exact h.trans afterSite
  have blank i : (p.ballot i).word (W:=W) p.sites (p.ballotROM rom i) a=none :=
    Shape.word_away _ _ _ _ (Or.inr ((extent (p.firstROM rom) _ i).trans afterBallots))
  have picked:=dated_choice p.control p.sites (p.controlROMStart rom) j a w lo hi owned
  simp only [Dated.words,romAt_away _ (Or.inr afterStride),romAt_away _ (Or.inr afterSite),
    absent _ blank,Dated.controlROM,picked]; rfl

structure Shape.Origin (g : Shape) (sites base : ℕ) (m : Memory W) : Prop where
  directory : ∀i : Fin 3,RoleROM.Mounted (base+i.val*g.count) (SiteScatter.directory g.candidates g.parties g.columns i) m
  strides : RoleROM.Mounted (base+3*g.count) (fun i : Fin sites=>i.val*g.columns) m

theorem Shape.origin (g : Shape) (sites base : ℕ) (m : Memory W)
    (on : ∀a w,base≤a→a<base+g.advice sites → g.word (W:=W) sites base a=some w→m a=w) :
    g.Origin sites base m := by
  constructor
  · intro i j
    have bound:=Nat.mul_le_mul_right g.count i.isLt
    rw [Nat.succ_mul] at bound
    have small : j.val < g.count := j.isLt
    have up : base+i.val*g.count+j.val < base+3*g.count := by omega
    exact on _ _ (by omega) (by dsimp only [Shape.advice];omega) (g.rawWord sites base i j)
  · intro s
    exact on _ _ (by omega) (by dsimp [Shape.advice];have:=s.isLt;omega) (g.multiplier sites base s)

theorem Dated.ballot_origin (j : Fin T) : (p.ballot j).Origin p.sites (p.ballotROM rom j) image :=
  Shape.origin (p.ballot j) p.sites (p.ballotROM rom j) image
    (fun a w lo hi h=>p.ballot_word rom table transport m j a w lo hi h)

theorem Dated.control_origin (j : Fin T) : (p.control j).Origin p.sites (p.controlROM rom j) image :=
  Shape.origin (p.control j) p.sites (p.controlROM rom j) image
    (fun a w lo hi h=>p.control_word rom table transport m j a w lo hi h)

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI

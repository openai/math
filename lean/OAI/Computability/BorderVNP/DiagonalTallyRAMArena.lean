import OAI.Computability.BorderVNP.DiagonalTallyRAMClear
import OAI.Computability.BorderVNP.DiagonalTallyCellOperands

/-!
# Physical allocation for the generated sparse pairs and the subtotal buffers

Starting immediately after the existing source data, the program writes the pairs,
clears the local counters, decodes the common rows, computes the global totals and
writes the machine-word bits. One spare word separates the totals and their bit output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyScatter
open DiagonalTallyMaterialize (Operand storeAll storeAll_before)
open private resident_congr from OAI.Computability.BorderVNP.DiagonalTallyRAMLayout
open private recordsAt_congr from OAI.Computability.BorderVNP.DiagonalTallyScatterLoop
open private supplied_fits from OAI.Computability.BorderVNP.DiagonalTallyMaterializeLoop

/-- Runtime sizes and the fresh starting address for the tally workspace. -/
structure Arena where
  /-- First word after existing source buffers, including selected cube IDs. -/
  fresh : ℕ
  /-- Start of the subtotal fields in the common prefix. -/
  raw : ℕ
  /-- Number of parameters and gadget coordinates combined. -/
  dim : ℕ
  /-- Number of local weighted-use and checked scalar-count operands. -/
  count : ℕ
  /-- Number of teams sharing the common prefix. -/
  teams : ℕ
  /-- This team's position in the common prefix. -/
  team : ℕ
  /-- Fixed bit width of each common subtotal. -/
  width : ℕ

/-- A packed allocation of the four word arrays used by the tally table. -/
def Arena.frame (a : Arena) : Frame :=
  let localBase := a.fresh+2*a.count
  let claims := localBase+a.dim
  let totals := claims+a.teams*a.dim+a.dim
  {dim := a.dim, teams := a.teams,claims := claims,totals := totals,localBase := localBase,
   records := a.fresh,count := a.count,rawBits := a.raw,team := a.team,width := a.width}

/-- Address range for the Fourier query's little-endian bits. -/
def Arena.bitFrame (a : Arena) (w : ℕ) : DiagonalTallyUnpack.Frame :=
  {src := a.frame.totals, width := w, dst := a.frame.totals+a.dim+1,total := a.dim*w}

/-- The only initial bounds on the new memory and the common prefix. -/
structure Arena.Fits (a : Arena) (w directory : ℕ) : Prop where
  /-- Initial directory precedes the first writable output. -/
  dir : directory+45 ≤ a.fresh
  /-- Raw subtotal bits are already in the common header. -/
  raw : a.raw+(a.teams*a.dim)*a.width ≤ a.fresh
  /-- The end sentinel of the last allocated array fits. -/
  room : (a.bitFrame w).dst+a.dim*w < 2^w
  /-- This team's rectangular row exists. -/
  team : a.team<a.teams
  /-- The broadcast loop counter fits even for a zero-dimensional table. -/
  teams : a.teams<2^w
  /-- Common fields fit in a physical word. -/
  width : a.width≤w
  /-- Physical serialization has a positive digit width. -/
  positive : 0<w

theorem Arena.Fits.frameFit {a : Arena} {w directory : ℕ} (h : a.Fits w directory) :
    a.frame.addressesFit w directory := by
  obtain ⟨dir,raw,room,team,teams,width,_⟩ := h
  simp only [Arena.bitFrame,Arena.frame] at room ⊢
  unfold Frame.addressesFit
  dsimp only
  omega

theorem Arena.Fits.bitFit {a : Arena} {w directory : ℕ} (h : a.Fits w directory) :
    (a.bitFrame w).fits w := by
  obtain ⟨_,_,room,_,_,_,hw⟩ := h
  simp [Arena.bitFrame,DiagonalTallyUnpack.Frame.fits,Nat.mul_div_cancel _ hw,hw] at room ⊢
  omega

variable {w : ℕ}

/-- Source memory following record generation and explicit zero initialization. -/
def Arena.initialized (a : Arena) (m : Memory w) (os : List Operand) : Memory w :=
  cleared (storeAll m a.fresh os) a.frame.localBase a.dim

theorem Arena.initialized_before (a : Arena) (m : Memory w) (os : List Operand)
    (p : ℕ) (hp : p<a.fresh) : a.initialized m os p=m p := by
  have h : p<a.frame.localBase := by change p<a.fresh+2*a.count; omega
  simp [Arena.initialized,cleared,Nat.not_le_of_lt h,storeAll_before m a.fresh p os hp]

private theorem increment_outside (base dim p : ℕ) (rs : List (ℕ × ℕ)) (hc : ∀ r∈rs,r.1<dim)
    (hp : p<base ∨ base+dim≤p) : incrementAt base p rs=0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hd := hc r List.mem_cons_self
    have he : base+r.1≠p := by omega
    simp [incrementAt,he,ih (fun x hx => hc x (.tail _ hx))]

/-- Derive all native-input conditions from the source memory, raw fields, and ordinary
word bounds. Local counters may contain arbitrary values on entry. -/
theorem Arena.input (a : Arena) (pub : Arg → Word w) (m : Memory w) (os : List Operand)
    (xs : List (List Bool)) (p : ℕ) (hfit : a.Fits w (pub 0).val) (hr : a.frame.resident pub m)
    (hops : DiagonalTallyMaterialize.supplied m a.fresh p os)
    (hcount : os.length=a.count) (coords : ∀ o∈os,o.pair.1<a.dim)
    (sums : ∀ j<a.dim,incrementAt a.frame.localBase (a.frame.localBase+j) (os.map Operand.pair)<2^w)
    (bits : DiagonalTallyBits.WordsAt m a.raw xs) (num : xs.length=a.teams*a.dim)
    (lengths : ∀ x∈xs,x.length=a.width) :
    Input a.frame pub (a.initialized m os) (os.map Operand.pair) xs := by
  let f := a.frame
  let m' := a.initialized m os
  have hdr := hfit.dir
  have hraw := hfit.raw
  have hc (r : ℕ × ℕ) (hr : r ∈ os.map Operand.pair) : r.1 < a.dim := by
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hr
    exact coords o ho
  have resident := resident_congr f pub m m' hr (fun j _ hj => a.initialized_before m os j (by omega))
  have generated := DiagonalTallyMaterialize.storeAll_recordsAt m a.fresh os (supplied_fits m _ p os hops)
  have recAt := recordsAt_congr _ m' _ _ generated (by
    intro j _ hj
    simp only [List.length_map,hcount] at hj
    have ht : j<f.localBase := hj
    simp [m',Arena.initialized,cleared,show ¬a.frame.localBase≤j from Nat.not_le_of_lt ht])
  refine Input.of_disjoint f pub m' _ xs hfit.frameFit resident recAt
    (by simpa only [f,Arena.frame,List.length_map] using hcount) hc ?_ ?_ num lengths ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro q
    by_cases hq : f.localBase≤q ∧ q<f.localBase+a.dim
    · change a.frame.localBase≤q ∧ q<a.frame.localBase+a.dim at hq
      have zeroWord : m' q=0 := by simp [m',Arena.initialized,cleared,hq.1,hq.2]
      rw [zeroWord,Fin.val_zero,zero_add]
      have he := sums (q-a.frame.localBase) (by omega)
      change incrementAt a.frame.localBase q (os.map Operand.pair) < 2^w
      simpa only [Nat.add_sub_of_le hq.1] using he
    · have hz := increment_outside f.localBase a.dim q _ hc (by omega)
      rw [hz,Nat.add_zero]; exact (m' q).isLt
  · apply DiagonalTallyBits.words_congr m m' a.raw a.width xs bits lengths
    intro j _ hj
    rw [num] at hj
    exact a.initialized_before m os j (by omega)
  all_goals dsimp only [f,Arena.frame,separated]; first | omega | rw [Nat.mul_comm a.dim a.teams]; omega

/-- The output-bit frame is readable after the generated counters and decoded broadcast
have been written. -/
theorem Arena.finalFrame (a : Arena) (pub : Arg → Word w) (m : Memory w) (os : List Operand)
    (xs : List (List Bool)) (hfit : a.Fits w (pub 0).val)
    (hframe : serializeFrame pub m (a.bitFrame w) a.dim)
    (hi : Input a.frame pub (a.initialized m os) (os.map Operand.pair) xs) :
    serializeFrame pub (resultBank a.frame (os.map Operand.pair) xs (a.initialized m os)) (a.bitFrame w) a.dim := by
  have hdr := hfit.dir
  apply resultBank_serializeFrame a.frame (a.bitFrame w) pub _ _ xs hi
  · dsimp only [serializeFrame] at hframe ⊢
    repeat' rw [a.initialized_before m os _ (by omega)]
    exact hframe
  all_goals dsimp only [Arena.frame,separated]; omega

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI

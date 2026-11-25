import OAI.Computability.BorderVNP.TeamTapeInputRouteBank

/-! # Physical preparation of each virtual sorting site's public data

The site index is a tagged fixed-width binary word in the saved literal. Its actual bit
length supplies the address-width tally. The original public word and bucket supply the
other tallies. The real block copies the closed record array; the virtual padding block
uses the same number of zero bits. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute

open VPVNP BurstRAM RAMTape

/-- The public metadata remainder saved by the input parser. -/
abbrev metadata : Port := .entry (.inl (.peek .input))
/-- Original public capacity in unary, retained through all record emissions. -/
abbrev bucket : Port := .entry (.inr .bucket)
/-- The sorted input is formed only after all initialization and instruction records have
been appended and the buffer closed. -/
abbrev closedBlock : Port := .entry (.inr (.emit (.buffer .output)))

private abbrev tmp := Port.work .tmp

private def taggedPorts (lane : Bool) : Option Unit → Port
  | none => metadata
  | some _ => .post lane SitePost.addressPort

private theorem tagged_inj (lane : Bool) : Function.Injective (taggedPorts lane) := by
  rintro (_ | ⟨⟩) (_ | ⟨⟩) h <;> simp_all [taggedPorts]

private def readId (lane : Bool) : FiniteRoutine Port :=
  (FiniteRoutine.ofRoutine (Evaluator.InputBank.readField ())).onPorts (taggedPorts lane)

private theorem readId_runs (lane : Bool) (s : Stacks Port) (bs rest : List Bool)
    (hi : s metadata = Evaluator.InputBank.fieldBits bs ++ rest)
    (hz : s (.post lane SitePost.addressPort) = []) :
    (readId lane).Runs (3*bs.length+1) s
      (Function.update (Function.update s metadata rest) (.post lane SitePost.addressPort) bs) := by
  apply (FiniteRoutine.ofRoutine (Evaluator.InputBank.readField ())).runs_onPorts_framed (tagged_inj lane)
    (Evaluator.InputBank.readField_runs () bs rest (fun _ => []))
  · rintro (_ | ⟨⟩) <;> assumption
  · rintro (_ | ⟨⟩) <;> simp [taggedPorts, Evaluator.InputBank.frame]
  · intro p hp
    have h₁ : p ≠ metadata := fun e => hp none e.symm
    have h₂ : p ≠ .post lane SitePost.addressPort := fun e => hp (some ()) e.symm
    simp [h₁,h₂]

private def marks (src dst : Port) : ℕ → FiniteRoutine Port
  | 0 => .ret
  | k+1 => (WordCopy.mapWord tmp dst (fun _ => true) src).followedBy (marks src dst k)

private theorem marks_run (src dst : Port) (k : ℕ) (s : Stacks Port) (hne : src ≠ dst)
    (h₁ : src ≠ tmp) (h₂ : tmp ≠ dst) (ht : s tmp = []) :
    (marks src dst k).Runs (k*(5*(s src).length+2)+1) s
      (Function.update s dst (List.replicate (k*(s src).length) true ++ s dst)) := by
  induction k generalizing s with
  | zero =>
    simp only [Nat.zero_mul,Nat.zero_add,List.replicate_zero,List.nil_append,Function.update_eq_self]
    exact Routine.runs_ret s
  | succ k ih =>
    let L := (s src).length
    let mid := Function.update s dst (List.replicate L true ++ s dst)
    have run := WordCopy.mapWord_run tmp dst (fun _ => true) h₁ hne h₂ s ht
    simp only [List.map_const',List.reverse_replicate] at run
    have rest := ih mid (by simpa [mid,Function.update_of_ne h₂] using ht)
    have hsrc : mid src = s src := Function.update_of_ne hne ..
    rw [hsrc] at rest
    change (marks src dst (k+1)).Runs ((k+1)*(5*L+2)+1) s
      (Function.update s dst (List.replicate ((k+1)*L) true ++ s dst))
    rw [show (k+1)*(5*L+2)+1 = (5*L+2)+(k*(5*L+2)+1) by ring,Nat.succ_mul k L,List.replicate_add]
    simpa only [marks,mid,Function.update_self,Function.update_idem,List.append_assoc] using run.followedBy rest

private def block (lane : Bool) : FiniteRoutine Port :=
  if lane then WordCopy.mapWord tmp (.post lane SitePost.blockPort) (fun _ => false) closedBlock
  else SuccessorFields.prependCopy closedBlock (.post lane SitePost.blockPort) tmp

/-- Canonical bytes of the real or padded virtual array. -/
def blockContents (lane : Bool) (real : List Bool) : List Bool :=
  if lane then List.replicate real.length false else real

private theorem block_run (lane : Bool) (s : Stacks Port) (ht : s tmp = [])
    (hb : s (.post lane SitePost.blockPort) = []) :
    (block lane).Runs (5*(s closedBlock).length+2) s
      (Function.update s (.post lane SitePost.blockPort) (blockContents lane (s closedBlock))) := by
  cases lane
  · simpa only [block,blockContents,Bool.false_eq_true,ite_false,hb,List.append_nil] using
      SuccessorFields.prependCopy_runs closedBlock (.post false SitePost.blockPort) tmp
        (by decide) (by decide) (by decide) s ht
  · exact WordCopy.zero_template tmp (.post true SitePost.blockPort) (by decide : closedBlock ≠ tmp)
      (by decide) (by decide) s ht hb

/-- A fixed virtual-site setup, starting at the tagged index. All sizes are read from
actual stack lengths rather than embedded in the finite control. -/
def geometry (lane : Bool) : FiniteRoutine Port :=
  ((((readId lane).followedBy (marks widthSource (.post lane SitePost.widthPort) 1)).followedBy
    (marks (.post lane SitePost.addressPort) (.post lane SitePost.addressWidthPort) 1)).followedBy
      (marks bucket (.post lane SitePost.slotsPort) 4)).followedBy (block lane)

/-- Exact time of the public setup and record-block staging. -/
def geometryTime (d w H bytes : ℕ) := 8*d + 5*w + 20*H + 5*bytes + 18

/-- Bank after staging the index, geometry tallies and real or empty physical record block. -/
def installed {d : ℕ} (lane : Bool) (w H : ℕ) (v : Word d) (rest : List Bool) (s : Stacks Port) :
    Stacks Port :=
  let a := Function.update (Function.update s metadata rest) (.post lane SitePost.addressPort) (wordBits v)
  let b := Function.update a (.post lane SitePost.widthPort) (List.replicate w true)
  let c := Function.update b (.post lane SitePost.addressWidthPort) (List.replicate d true)
  let f := Function.update c (.post lane SitePost.slotsPort) (List.replicate (4*H) true)
  Function.update f (.post lane SitePost.blockPort) (blockContents lane (s closedBlock))

/-- All of the sorter's initially vacant stacks are actually prepared from the parsed
public fields and the emitted physical block. -/
theorem geometry_runs {d : ℕ} (lane : Bool) (w H : ℕ) (v : Word d) (s : Stacks Port)
    (rest : List Bool) (hi : s metadata = Evaluator.InputBank.fieldBits (wordBits v) ++ rest)
    (hw : (s widthSource).length = w) (hH : (s bucket).length = H) (ht : s tmp = [])
    (hz : ∀ p, s (.post lane p) = []) :
    (geometry lane).Runs (geometryTime d w H (s closedBlock).length) s (installed lane w H v rest s) := by
  let addr := Port.post lane SitePost.addressPort
  let wid := Port.post lane SitePost.widthPort
  let dw := Port.post lane SitePost.addressWidthPort
  let slots := Port.post lane SitePost.slotsPort
  let x := Function.update (Function.update s metadata rest) addr (wordBits v)
  let y := Function.update x wid (List.replicate w true)
  let z := Function.update y dw (List.replicate d true)
  let u := Function.update z slots (List.replicate (4*H) true)
  have idRun := readId_runs lane s (wordBits v) rest hi (hz _)
  rw [length_wordBits] at idRun
  have widthRun := marks_run widthSource wid 1 x (by simp [wid]) (by decide) (by simp [wid]) (by simpa [x,addr] using ht)
  have adrRun := marks_run addr dw 1 y (by simp [addr,dw,SitePost.addressPort,SitePost.addressWidthPort])
    (by simp [addr]) (by simp [dw]) (by simpa [y,x,wid,addr] using ht)
  have slotRun := marks_run bucket slots 4 z (by simp [slots]) (by decide) (by simp [slots])
    (by simpa [z,y,x,wid,dw,addr] using ht)
  have blockRun := block_run lane u (by simpa [u,z,y,x,slots,dw,wid,addr] using ht)
    (by cases lane <;> exact hz _)
  have wx : x widthSource = s widthSource := rfl
  have wy : x wid = [] := by cases lane <;> exact hz _
  have ay : y addr = wordBits v := by cases lane <;> rfl
  have dy : y dw = [] := by cases lane <;> exact hz _
  have bz : z bucket = s bucket := rfl
  have sz : z slots = [] := by cases lane <;> exact hz _
  have bu : u closedBlock = s closedBlock := rfl
  rw [wx,hw,wy,one_mul,List.append_nil,one_mul] at widthRun
  rw [ay,length_wordBits,dy,one_mul,List.append_nil,one_mul] at adrRun
  rw [bz,hH,sz,List.append_nil] at slotRun
  rw [bu] at blockRun
  have total := (((idRun.followedBy widthRun).followedBy adrRun).followedBy slotRun).followedBy blockRun
  convert total using 1 <;> first | rfl | (unfold geometryTime; omega)

end TeamTapeInputRoute

end BorderVNP
end Computability
end OAI

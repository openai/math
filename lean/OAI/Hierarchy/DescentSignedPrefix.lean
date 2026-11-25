import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! Append-only original RAM scans and literal pages for an ordinary signed date. -/
namespace Hierarchy.DescentDatedAddressBook.SignedPrefix
open DescentSixParty.Chronology Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
inductive Job
  | words (n:ℕ) (value:ℕ→ℕ)
  | columns (count rows pitch:ℕ) (value:ℕ→Expr)
def Job.width:Job→ℕ
  | .words n _=>n
  | .columns n _ pitch _=>n*pitch

def Job.atBase (base w:ℕ):Job→NativePhase w
  | .words n v=>⟨DescentStaticWordColumn.program w base v n,4+10*n,fun m=>DescentStaticWordColumn.image base v m n,
      DescentStaticWordColumn.cheap w base v n⟩
  | .columns n r p e=>
    let ps:=DescentPackedFlowBatch.passes base r p e 0 n
    ⟨program w ps,clock ps,result ps,program_cheap w ps⟩

def Job.Fits (base w:ℕ):Job→Prop
  | .words _ _=>True
  | .columns n r p e=>r≤p ∧ ∀i<n,(e i).Fits w base

theorem Job.any {w:ℕ} (j:Job) (base:ℕ) (m:Memory w) (fit:j.Fits base w) (room:base+j.width<2^w):
    (j.atBase base w).Runs m ∧ ∀a,a<base ∨ base+j.width≤a→(j.atBase base w).image m a=m a:=by
  cases j with
  | words n v=>
    exact ⟨DescentStaticWordColumn.mount base n v m room,DescentStaticWordColumn.frame base n v m⟩
  | columns n r p e=>
    obtain ⟨ran,_,low⟩:=DescentPackedFlowBatch.execute base r p n e m fit.2 room fit.1
    exact ⟨ran,fun a h=>h.elim (low a) (fun f=>DescentPackedFlowBatch.above base r p e m 0 n a fit.1 (by simpa only [Job.width,Nat.zero_add] using f))⟩

/-- The generated instruction list is nonempty. The terminal raster is the
last phase, and no extra literal or scan is charged for an empty suffix. -/
def build (w:ℕ) (tail:ℕ→NativePhase w) : List Job→ℕ→NativePhase w
  | [],base=>tail base
  | j::js,base=>(j.atBase base w).seq (build w tail js (base+j.width))
def finish : List Job→ℕ→ℕ
  | [],base=>base
  | j::js,base=>finish js (base+j.width)
def Fits (w:ℕ):List Job→ℕ→Prop
  | [],_=>True
  | j::js,base=>j.Fits base w ∧ Fits w js (base+j.width)

theorem lower (js:List Job) (base:ℕ):base≤finish js base:=by
  induction js generalizing base with
  | nil=>exact le_rfl
  | cons j js ih=>exact (Nat.le_add_right ..).trans (ih _)

theorem run {w:ℕ} (tail:ℕ→NativePhase w) (js:List Job) (base roof:ℕ) (m:Memory w)
    (fits:Fits w js base) (space:roof<2^w) (atEnd:finish js base≤roof)
    (last:∀m', (tail (finish js base)).Runs m' ∧ ∀a,a<finish js base ∨ roof≤a→(tail (finish js base)).image m' a=m' a):
    (build w tail js base).Runs m ∧ ∀a,a<base ∨ roof≤a→(build w tail js base).image m a=m a:=by
  induction js generalizing base m with
  | nil=>exact last m
  | cons j js ih=>
    let first:=j.atBase base w
    have sep:base+j.width≤roof:=(lower js (base+j.width)).trans atEnd
    obtain ⟨run,frame⟩:=j.any base m fits.1 (sep.trans_lt space)
    obtain ⟨later,kept⟩:=ih (base+j.width) (first.image m) fits.2 atEnd last
    refine ⟨NativePhase.seq_runs _ _ _ run later,?_⟩
    intro a outside
    exact (kept a (outside.imp (fun h=>h.trans_le (Nat.le_add_right ..)) id)).trans
      (frame a (outside.imp id (sep.trans ·)))

def earlier {w:ℕ} : List Job→ℕ→Memory w→Memory w
  | [],_,m=>m
  | j::js,base,m=>earlier js (base+j.width) ((j.atBase base w).image m)
theorem output {w:ℕ} (tail:ℕ→NativePhase w) (js:List Job) (base:ℕ) (m:Memory w):
    (build w tail js base).image m=(tail (finish js base)).image (earlier js base m):=by
  induction js generalizing base m with
  | nil=>rfl
  | cons j js ih=>exact ih _ _

end
end Hierarchy.DescentDatedAddressBook.SignedPrefix

end OAI

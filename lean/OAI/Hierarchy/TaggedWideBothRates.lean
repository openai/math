import OAI.Hierarchy.TaggedWideInstalledRates
import OAI.Hierarchy.TaggedWideInstalledWindowText
import OAI.Hierarchy.TaggedWideInstalledCheap
import OAI.Hierarchy.TaggedWidePaidDated
import OAI.Hierarchy.TaggedWideWindowVolume

namespace OAI
/-! # Fixed native text and linear native time for both actual paid parent programs -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles Tagged
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A s : ℝ} (m ell short : ℕ) {u : ℝ→ℝ} (hu : TaggedWidthProfile.Admissible s u) (δ ξ : ℝ) (unitCost : ℕ)
local notation "T" => (events v.mesh).length

include hu in
/-- Both controllers read the same finite header. This bill counts every dated scatter,
each actual shorter format bank, and both original-tag inversion prefixes. -/
theorem cofinal_both_program_rates :
    ∃K : ℕ,∀ᶠ x : WideParent κ A in WideParent.large κ A,
      let g:=v.wideDated x.h x.w ell unitCost
      let l:=v.wideInstalledLayout x m ell short u δ ξ unitCost g
      let progs:=v.widePrograms x.h x.w v.maxBits l
      let times:=v.wideProgramTicks x.h x.w v.maxBits l
      times.1+times.2≤K*2^x.h ∧
      Native.text progs.1+Native.text progs.2≤K ∧ CheapCode progs.1 ∧ CheapCode progs.2 := by
  obtain ⟨j,paid⟩:=v.cofinal_installed_native_rates (κ:=κ) (A:=A)
  obtain ⟨a,dates⟩:=v.wide_dated_resources ell
  obtain ⟨c,windows⟩:=v.wide_format_runtime (κ:=κ) (A:=A) m ell short hu δ ξ (v.wideInstalledCap unitCost)
  let b:=BoughtSockets.Public.maxMetric v.radius
  let pruneText:=87+4*(47+20*b+9*b*(b+1))
  refine ⟨j+a+c+(m+1)*5450+pruneText,?_⟩
  filter_upwards [paid] with x native
  intro g l progs times
  let n:=2^x.h
  let W:=Native.wordBits x.h (2^v.W) Native.copies
  let root:=v.wideInstalledRoot x
  let S:=v.wideInstalledSize x m ell unitCost g
  let last:=(v.wideWidthLayout x.h x.w (v.widePaidSlices x.h x.w v.maxBits)).bank T
  let pfx:=v.wideCountedPrefix x.h x.w v.maxBits
  let tick:=v.wideCountedTime x.h x.w v.maxBits
  obtain ⟨pt,pc,_⟩:=native m ell short unitCost u δ ξ g
  have pt' : times.1+TagInverse.ticks x.h+tick+l.terminal.ticks last≤j*n:=pt
  have pc' : Native.text progs.1+93+Native.text pfx+Native.text (l.terminal.code W last)≤j:=pc
  obtain ⟨dt,dc,_⟩:=dates x.h x.w unitCost root S W
  have dt' : (∑i,(l.scatter i).ticks)≤a*n:=dt
  have dc' : (∑i,Native.text ((l.scatter i).code W))≤a := by
    rw [←WideCPU.bank_text]
    exact dc
  have wc' : (∑i,l.windowTicks i)+(4+(l.pruneRows+1)*(42+2*l.prune.work))≤c*n:=
    windows x g v.maxBits root
  have second : Native.text progs.2=
      93+(((Native.text pfx+((∑i,Native.text ((l.scatter i).code W))+Native.text (l.terminal.code W last)))+
      (m+1)*5450)+pruneText):=v.wide_installed_second_text x m ell short u δ ξ unitCost g
  have clock : times.2=TagInverse.ticks x.h+((tick+((∑i,(l.scatter i).ticks)+l.terminal.ticks last))+
      ∑i,l.windowTicks i)+(4+(l.pruneRows+1)*(42+2*l.prune.work)) := by
    change TagInverse.ticks x.h+l.ticks tick last=_
    rw [WideCPU.Layout.finish_time]
    omega
  have small:=v.wide_installed_cheap x m ell short u δ ξ unitCost g
  refine ⟨?_,by omega,small⟩
  change times.1+times.2≤(j+a+c+(m+1)*5450+pruneText)*n
  simp only [Nat.add_mul]
  omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

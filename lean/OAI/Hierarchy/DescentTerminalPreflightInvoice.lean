import OAI.Hierarchy.DescentTerminalPreflightTariff

namespace OAI
/-! # Complete native terminal preprocessing invoice through the last header scatter -/
namespace Hierarchy.DescentTerminalPreflightInvoice
open DescentSIMDLookup DescentTerminalRowArena DescentStaticWordColumn DescentColonies.SplitRAM
open DescentTerminalPreflightTariff DescentTerminalGeometryTariff DescentTerminalHeaderDraft DescentDyadicSpan
open DescentTerminalLocalPortBook DescentTerminalGrainProfiles DescentTerminalCombinedRole DescentTerminalPointerDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {B aa:ℕ} (w H G M a b c lo M' next:ℕ) (old:Fin B→Bank) (external:Bank)
    (pick:Fin B→Cell aa→Cell 1) (source:Fin B→Bank)
    (X:DescentTerminalPublicWidthTape.Shape) (q p:ℕ) (A:Arena) (L:DescentTerminalHeaderSockets.Layout) (rom:ℕ)
local notation "prior1" => DescentTerminalPopulation.RAM.issue H G M a b c lo old external w
local notation "prior2" => DescentTerminalActorRepack.program pick H G M' next source w
local notation "paidROM" => DescentTerminalPopulation.RAM.lease H G M a c lo
local notation "actorROM" => DescentTerminalActorRepack.count H G M' aa B next
local notation "publicROM" => (DescentTerminalPublicCountRAM.lut X.base X.maxCohorts).size+X.widthLayout.entries
local notation "lanes" => chunks G M+chunks G M'
local notation "bits_" => X.program w q p
local notation "clocks₁" => DescentTerminalPopulation.RAM.ticks H G M a c lo old external
local notation "clocks₂" => DescentTerminalActorRepack.ticks (a:=aa) H G M' next source
local notation "core" => ((((prior1).seq prior2).seq bits_).seq (litProc w rom A.rows)).seq (machine A L 3 w)


variable {Q D R₀ U₀ U₇ J d0 cap groups pitch:ℕ}
    (first second:Shelf) (roleOut origin dc cc cw hidden nodes args:ℕ)
    (chart:Fin Q→Fin B→Gather.Address) (f0:(Fin Q→Cell d0)→Cell U₀) (f7:(Fin Q→Cell d0)→Cell U₇)
    (counts:Fin 3→Bank) (C:Print.Layout J) (V arg base:ℕ)
    (decode:(Fin J→Cell C.bits)→Directory 4 V arg) (T:Counter.Rack B cap groups pitch)
    (ctl:DescentTerminalControlProgram.Plan) (values:ℕ→ℕ) (parts:Book.Parts)
local notation "prim" => DescentTerminalPrimitiveNames.program w first second roleOut origin H chart f0 f7 counts dc cc cw q hidden nodes args groups p
local notation "primTime" => DescentTerminalPrimitiveNames.clocks d0 dc origin H chart
local notation "buy" => Book.WeightShelf.program V arg base w
local notation "weigh" => (4+10*Book.WeightShelf.words V arg)
local notation "bk" => C.prefix decode (V*arg) w 6 le_rfl
local notation "bkTime" => C.time 6 le_rfl
local notation "ctrl" => ctl.program w values (Book.expression parts)
local notation "ctrlTime" => ctl.time (Book.expression parts)
local notation "racks" => T.program w q p
local notation "rcTime" => T.time q p
local notation "done" => machine A L 3 w
local notation "literals" => litProc w rom A.rows
local notation "preflights" => ((((((((((prior1).seq prior2).seq prim).seq buy).seq bk).seq ctrl).seq racks).seq bits_).seq literals).seq done)
local notation "steps" => clocks₁+clocks₂+primTime+weigh+bkTime+ctrlTime+rcTime+X.clocks q p+(4+40*DescentTerminalHeaderDraft.span A.rows)+clocks A L 3

theorem total (h bw scale paid:ℕ)
    (menus:paidROM+actorROM+publicROM≤12*(2^(h/2)+H*scale))
    (packing:B*(1+lanes)≤ scale) (sites:A.sites≤H) (publicH:X.H≤H)
    (publicRows:X.rows+A.rows≤paid) (positive:0<H) (rate:0<scale)
    (fetch:∀j,(C.source j).work≤64)
    (bookTable:DescentTerminalPointerFrame.size J C.bits≤2^(h/2))
    (cableTable:T.fee≤2^(h/2)) (widths:T.printer.entries≤4*2^(h/2))
    (bookCells:(C.homes+1)*(J+1)≤H*scale) (cableCells:(T.tickets+1)*(T.cols+1)≤H*scale)
    (cableRows:T.maxRows≤paid) (weights:Book.WeightShelf.words V arg≤6*2^(h/2))
    (pointerTable:DescentTerminalPointerFrame.size Q d0≤2^(h/2))
    (countTable:DescentTerminalPointerFrame.size 3 dc≤2^(h/2))
    (scalarCells:(H+1)*(Q+1)*(B+1)≤H*scale)
    (controlTable:ctl.codeWords≤2^(h/2)) (controlROM:ctl.shape.limit≤2^(h/2)) (controlRows:ctl.sites≤H*scale) :
    (names preflights+steps)*(bw+1)≤6050000*((2^(h/2)+H*scale)*(bw+1)+paid*(bw+1)) := by
  apply assembled
  · unfold cost
    simpa only [Nat.add_assoc,budget] using calibrated_price w H G M a b c lo M' next old external pick source X q p A L rom
      h bw scale paid menus packing sites publicH publicRows positive rate
  · exact primitive w first second roleOut origin H chart f0 f7 counts dc cc cw q hidden nodes args groups p h scale paid bw
      pointerTable countTable scalarCells
  · exact DescentTerminalPreflightTariff.weights V arg base h H scale paid bw w weights
  · exact DescentTerminalGeometryTariff.paid C decode (V*arg) w T q p h bw H scale paid fetch bookTable cableTable widths bookCells cableCells cableRows
  · exact controls ctl w h H scale paid bw values parts controlTable controlROM controlRows

end
end Hierarchy.DescentTerminalPreflightInvoice

end OAI

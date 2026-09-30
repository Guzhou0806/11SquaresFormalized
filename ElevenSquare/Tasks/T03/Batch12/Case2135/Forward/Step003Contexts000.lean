import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step003State
import ElevenSquare.Tasks.T03.PhysicalRowInput
import ElevenSquare.Tasks.T03.Batch12.Case2135.Node000.Step003GeometryPart000

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row000
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell01Row000).withInterval 0 (1/8)
noncomputable def band : AngleBand := ⟨0,(1/8),1,2⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row000Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row000Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row000Geometry.domain,[⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[4]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step003State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row000Geometry.geometry Step003State.refined.rows (by change (0:ℚ) ≤ 0 ∧ (1/8) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step003State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row000

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row001
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell01Row001).withInterval (1/8) (1/4)
noncomputable def band : AngleBand := ⟨(1/8),(1/4),79,130⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row001Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row001Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row001Geometry.domain,[⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[4]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step003State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row001Geometry.geometry Step003State.refined.rows (by change (0:ℚ) ≤ (1/8) ∧ (1/4) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step003State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row001

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row002
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell01Row002).withInterval (1/4) (3/8)
noncomputable def band : AngleBand := ⟨(1/4),(3/8),23,34⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row002Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row002Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row002Geometry.domain,[⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[4]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step003State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row002Geometry.geometry Step003State.refined.rows (by change (0:ℚ) ≤ (1/4) ∧ (3/8) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step003State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row002

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row003
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell01Row003).withInterval (3/8) (1/2)
noncomputable def band : AngleBand := ⟨(3/8),(1/2),7,10⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row003Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row003Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row003Geometry.domain,[⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[4]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step003State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row003Geometry.geometry Step003State.refined.rows (by change (0:ℚ) ≤ (3/8) ∧ (1/2) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step003State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row003

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row004
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell01Row004).withInterval (1/2) (5/8)
noncomputable def band : AngleBand := ⟨(1/2),(5/8),119,178⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row004Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row004Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row004Geometry.domain,[⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[4]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step003State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row004Geometry.geometry Step003State.refined.rows (by change (0:ℚ) ≤ (1/2) ∧ (5/8) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step003State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row004

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row005
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell01Row005).withInterval (5/8) (3/4)
noncomputable def band : AngleBand := ⟨(5/8),(3/4),31,50⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row005Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row005Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row005Geometry.domain,[⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[4]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step003State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row005Geometry.geometry Step003State.refined.rows (by change (0:ℚ) ≤ (5/8) ∧ (3/4) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step003State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row005

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row006
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell01Row006).withInterval (3/4) (7/8)
noncomputable def band : AngleBand := ⟨(3/4),(7/8),127,226⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row006Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row006Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row006Geometry.domain,[⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[4]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step003State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row006Geometry.geometry Step003State.refined.rows (by change (0:ℚ) ≤ (3/4) ∧ (7/8) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step003State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row006

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row007
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell01Row007).withInterval (7/8) 1
noncomputable def band : AngleBand := ⟨(7/8),1,1,2⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row007Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row007Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row007Geometry.domain,[⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[4]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step003State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Row007Geometry.geometry Step003State.refined.rows (by change (0:ℚ) ≤ (7/8) ∧ 1 ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step003State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Row007

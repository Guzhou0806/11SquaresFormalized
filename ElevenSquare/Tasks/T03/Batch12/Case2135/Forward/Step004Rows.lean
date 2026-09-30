import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step004Contexts000

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step004Rows
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step004Data
noncomputable def block000_001 : ForwardRows prior Step004State.refined.rows owner chosen := Step004Row000.certificate
noncomputable def block001_002 : ForwardRows prior Step004State.refined.rows owner chosen := Step004Row001.certificate
noncomputable def block000_002 : ForwardRows prior Step004State.refined.rows owner chosen := block000_001.append block001_002
noncomputable def block002_003 : ForwardRows prior Step004State.refined.rows owner chosen := Step004Row002.certificate
noncomputable def block003_004 : ForwardRows prior Step004State.refined.rows owner chosen := Step004Row003.certificate
noncomputable def block002_004 : ForwardRows prior Step004State.refined.rows owner chosen := block002_003.append block003_004
noncomputable def block000_004 : ForwardRows prior Step004State.refined.rows owner chosen := block000_002.append block002_004
noncomputable def block004_005 : ForwardRows prior Step004State.refined.rows owner chosen := Step004Row004.certificate
noncomputable def block005_006 : ForwardRows prior Step004State.refined.rows owner chosen := Step004Row005.certificate
noncomputable def block004_006 : ForwardRows prior Step004State.refined.rows owner chosen := block004_005.append block005_006
noncomputable def block006_007 : ForwardRows prior Step004State.refined.rows owner chosen := Step004Row006.certificate
noncomputable def block007_008 : ForwardRows prior Step004State.refined.rows owner chosen := Step004Row007.certificate
noncomputable def block006_008 : ForwardRows prior Step004State.refined.rows owner chosen := block006_007.append block007_008
noncomputable def block004_008 : ForwardRows prior Step004State.refined.rows owner chosen := block004_006.append block006_008
noncomputable def block000_008 : ForwardRows prior Step004State.refined.rows owner chosen := block000_004.append block004_008
noncomputable def certificate : ForwardRows prior Step004State.refined.rows owner chosen := block000_008

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step004Rows

import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime002.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FeatureData
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianTargetCertificate

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def medCert00 : MedianFacetCertificate := {
  direction := .uPos
  facetIndex := 0
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site07}
  signU := 1
  signV := 1
}

def medCert01 : MedianFacetCertificate := {
  direction := .uNeg
  facetIndex := 1
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := 1
  signV := 1
}

def medCert02 : MedianFacetCertificate := {
  direction := .vPos
  facetIndex := 2
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := 1
  signV := 1
}

def medCert03 : MedianFacetCertificate := {
  direction := .vNeg
  facetIndex := 3
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := 1
  signV := 1
}

def medCert04 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site06 false
  facetIndex := 4
  medianSite := G005.site02
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site07}
  signU := 1
  signV := 1
}

def medCert05 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site06 true
  facetIndex := 5
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := -1
  signV := -1
}

def medCert06 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site07 false
  facetIndex := 6
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := 1
  signV := 1
}

def medCert07 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site07 true
  facetIndex := 7
  medianSite := G005.site02
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := -1
  signV := -1
}

def medCert08 : MedianFacetCertificate := {
  direction := .pair G005.site06 G005.site07 false
  facetIndex := 8
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := -1
  signV := 1
}

def medCert09 : MedianFacetCertificate := {
  direction := .pair G005.site06 G005.site07 true
  facetIndex := 9
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := 1
  signV := -1
}

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime002

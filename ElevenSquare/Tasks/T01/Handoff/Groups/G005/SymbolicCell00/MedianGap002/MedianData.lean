import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Cover
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianMixedCertificate

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def medCertL00 : MedianFacetCertificate := {
  direction := .uPos
  facetIndex := 0
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site07}
  signU := 1
  signV := 1
}

def guardedL00 : GuardedMedianFacetCertificate := {
  base := medCertL00
  orderSigns := [.factor ⟨1, 0, 0⟩, .plain, .plain]
}

def medCertL01 : MedianFacetCertificate := {
  direction := .uNeg
  facetIndex := 1
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := 1
  signV := 1
}

def medCertL02 : MedianFacetCertificate := {
  direction := .vPos
  facetIndex := 2
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := 1
  signV := 1
}

def medCertL03 : MedianFacetCertificate := {
  direction := .vNeg
  facetIndex := 3
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := 1
  signV := 1
}

def medCertL04 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site06 false
  facetIndex := 4
  medianSite := G005.site02
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site07}
  signU := 1
  signV := 1
}

def medCertL05 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site06 true
  facetIndex := 5
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := -1
  signV := -1
}

def medCertL06 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site07 false
  facetIndex := 6
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := 1
  signV := 1
}

def medCertL07 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site07 true
  facetIndex := 7
  medianSite := G005.site02
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := -1
  signV := -1
}

def medCertL08 : MedianFacetCertificate := {
  direction := .pair G005.site06 G005.site07 false
  facetIndex := 8
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := -1
  signV := 1
}

def medCertL09 : MedianFacetCertificate := {
  direction := .pair G005.site06 G005.site07 true
  facetIndex := 9
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := 1
  signV := -1
}

def medCertR00 : MedianFacetCertificate := {
  direction := .uPos
  facetIndex := 10
  medianSite := G005.site02
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site07}
  signU := 1
  signV := 1
}

def guardedR00 : GuardedMedianFacetCertificate := {
  base := medCertR00
  orderSigns := [.plain, .factor ⟨1, 0, 0⟩, .plain]
}

def medCertR01 : MedianFacetCertificate := {
  direction := .uNeg
  facetIndex := 11
  medianSite := G005.site02
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := 1
  signV := 1
}

def medCertR02 : MedianFacetCertificate := {
  direction := .vPos
  facetIndex := 2
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := 1
  signV := 1
}

def medCertR03 : MedianFacetCertificate := {
  direction := .vNeg
  facetIndex := 3
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := 1
  signV := 1
}

def medCertR04 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site06 false
  facetIndex := 12
  medianSite := G005.site02
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site07}
  signU := 1
  signV := -1
}

def medCertR05 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site06 true
  facetIndex := 13
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := -1
  signV := 1
}

def medCertR06 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site07 false
  facetIndex := 6
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := 1
  signV := 1
}

def medCertR07 : MedianFacetCertificate := {
  direction := .pair G005.site02 G005.site07 true
  facetIndex := 7
  medianSite := G005.site02
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := -1
  signV := -1
}

def medCertR08 : MedianFacetCertificate := {
  direction := .pair G005.site06 G005.site07 false
  facetIndex := 8
  medianSite := G005.site06
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site02}
  signU := -1
  signV := 1
}

def medCertR09 : MedianFacetCertificate := {
  direction := .pair G005.site06 G005.site07 true
  facetIndex := 9
  medianSite := G005.site07
  sitesList := [G005.site02, G005.site06, G005.site07]
  exceptions := {G005.site06}
  signU := 1
  signV := -1
}

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002

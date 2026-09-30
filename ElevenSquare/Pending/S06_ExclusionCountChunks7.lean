import ElevenSquare.Pending.S06_Data
import ElevenSquare.Pending.OrderedData
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem returned_block2 : Block id returnedArrayChunk2.toList 45 1889 2135 := by
  change Block id [
  1889,
  1891,
  1950,
  1955,
  2047,
  2048,
  2049,
  2050,
  2051,
  2052,
  2053,
  2055,
  2056,
  2057,
  2068,
  2069,
  2070,
  2071,
  2072,
  2073,
  2074,
  2075,
  2076,
  2077,
  2078,
  2084,
  2088,
  2091,
  2094,
  2097,
  2098,
  2102,
  2103,
  2111,
  2112,
  2114,
  2116,
  2119,
  2122,
  2125,
  2129,
  2130,
  2132,
  2133,
  2135] 45 1889 2135
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms returned_block2
end ElevenSquare.Pending.ExclusionCounts

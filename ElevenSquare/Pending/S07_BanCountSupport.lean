import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.OrderedData
namespace ElevenSquare.Pending
-- Strictly increasing keys imply distinct pairs; injectivity of the key is unnecessary.
def banKey (p : ℕ × ℕ) : ℕ := 220*p.2+p.1
end ElevenSquare.Pending

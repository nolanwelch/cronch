/// The corpus's receipts, rendered as one hex string.
///
/// Exists so that a genuinely fresh operating-system process can compute the
/// same thing and the two can be compared byte for byte. A second BEAM has its
/// own scheduler, heap, module table and process identifiers, so anything that
/// leaked a timestamp, a PID, a hash seed or a map iteration order into a
/// receipt shows up here as a mismatch.
import cronch/receipt
import gleam/bit_array
import gleam/list
import gleam/string
import support/corpus

/// The kernel identity every receipt in this fixture is issued under.
pub const kernel_id: String = "cronch-kernel/0.1.0"

pub const budget: Int = 100_000

/// Every corpus receipt's bytes, concatenated in corpus order and hex-encoded.
pub fn receipts_hex() -> String {
  corpus.cases()
  |> list.map(fn(c) {
    receipt.issue(kernel_id, c.environment, c.provenance, budget, c.term, c.typ)
    |> receipt.encode
    |> bit_array.base16_encode
    |> string.lowercase
  })
  |> string.join("")
}

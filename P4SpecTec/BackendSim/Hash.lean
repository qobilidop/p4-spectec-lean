import P4SpecTec.BackendSim.SpecImpl.Unpack

/-!
Port of `p4spec/lib/backend-sim/hash.ml`: the checksum and hash algorithms of the v1model
target (CRC-16, CRC-32, the ones'-complement checksums and identity), with the packing of
a tuple of P4 numbers into one bit string. Upstream computes over `Bigint`; the values are
non-negative after two's-complement normalization, so the port computes over `Nat`, and
every upstream exception (an unknown algorithm, a negative slice bound, a modulus by a
non-positive range) is `none`.
-/

namespace P4SpecTec.BackendSim.Hash

open P4SpecTec.Lang.Il P4SpecTec.BackendSim.SpecImpl

/-- The CRC16-ARC table. -/
def crc16_table : Array Nat := #[
  0x0000, 0xC0C1, 0xC181, 0x0140, 0xC301, 0x03C0, 0x0280, 0xC241,
  0xC601, 0x06C0, 0x0780, 0xC741, 0x0500, 0xC5C1, 0xC481, 0x0440,
  0xCC01, 0x0CC0, 0x0D80, 0xCD41, 0x0F00, 0xCFC1, 0xCE81, 0x0E40,
  0x0A00, 0xCAC1, 0xCB81, 0x0B40, 0xC901, 0x09C0, 0x0880, 0xC841,
  0xD801, 0x18C0, 0x1980, 0xD941, 0x1B00, 0xDBC1, 0xDA81, 0x1A40,
  0x1E00, 0xDEC1, 0xDF81, 0x1F40, 0xDD01, 0x1DC0, 0x1C80, 0xDC41,
  0x1400, 0xD4C1, 0xD581, 0x1540, 0xD701, 0x17C0, 0x1680, 0xD641,
  0xD201, 0x12C0, 0x1380, 0xD341, 0x1100, 0xD1C1, 0xD081, 0x1040,
  0xF001, 0x30C0, 0x3180, 0xF141, 0x3300, 0xF3C1, 0xF281, 0x3240,
  0x3600, 0xF6C1, 0xF781, 0x3740, 0xF501, 0x35C0, 0x3480, 0xF441,
  0x3C00, 0xFCC1, 0xFD81, 0x3D40, 0xFF01, 0x3FC0, 0x3E80, 0xFE41,
  0xFA01, 0x3AC0, 0x3B80, 0xFB41, 0x3900, 0xF9C1, 0xF881, 0x3840,
  0x2800, 0xE8C1, 0xE981, 0x2940, 0xEB01, 0x2BC0, 0x2A80, 0xEA41,
  0xEE01, 0x2EC0, 0x2F80, 0xEF41, 0x2D00, 0xEDC1, 0xEC81, 0x2C40,
  0xE401, 0x24C0, 0x2580, 0xE541, 0x2700, 0xE7C1, 0xE681, 0x2640,
  0x2200, 0xE2C1, 0xE381, 0x2340, 0xE101, 0x21C0, 0x2080, 0xE041,
  0xA001, 0x60C0, 0x6180, 0xA141, 0x6300, 0xA3C1, 0xA281, 0x6240,
  0x6600, 0xA6C1, 0xA781, 0x6740, 0xA501, 0x65C0, 0x6480, 0xA441,
  0x6C00, 0xACC1, 0xAD81, 0x6D40, 0xAF01, 0x6FC0, 0x6E80, 0xAE41,
  0xAA01, 0x6AC0, 0x6B80, 0xAB41, 0x6900, 0xA9C1, 0xA881, 0x6840,
  0x7800, 0xB8C1, 0xB981, 0x7940, 0xBB01, 0x7BC0, 0x7A80, 0xBA41,
  0xBE01, 0x7EC0, 0x7F80, 0xBF41, 0x7D00, 0xBDC1, 0xBC81, 0x7C40,
  0xB401, 0x74C0, 0x7580, 0xB541, 0x7700, 0xB7C1, 0xB681, 0x7640,
  0x7200, 0xB2C1, 0xB381, 0x7340, 0xB101, 0x71C0, 0x7080, 0xB041,
  0x5000, 0x90C1, 0x9181, 0x5140, 0x9301, 0x53C0, 0x5280, 0x9241,
  0x9601, 0x56C0, 0x5780, 0x9741, 0x5500, 0x95C1, 0x9481, 0x5440,
  0x9C01, 0x5CC0, 0x5D80, 0x9D41, 0x5F00, 0x9FC1, 0x9E81, 0x5E40,
  0x5A00, 0x9AC1, 0x9B81, 0x5B40, 0x9901, 0x59C0, 0x5880, 0x9841,
  0x8801, 0x48C0, 0x4980, 0x8941, 0x4B00, 0x8BC1, 0x8A81, 0x4A40,
  0x4E00, 0x8EC1, 0x8F81, 0x4F40, 0x8D01, 0x4DC0, 0x4C80, 0x8C41,
  0x4400, 0x84C1, 0x8581, 0x4540, 0x8701, 0x47C0, 0x4680, 0x8641,
  0x8201, 0x42C0, 0x4380, 0x8341, 0x4100, 0x81C1, 0x8081, 0x4040]

/-- The CRC32 table. -/
def crc32_table : Array Nat := #[
  0x00000000, 0x77073096, 0xEE0E612C, 0x990951BA, 0x076DC419, 0x706AF48F, 0xE963A535, 0x9E6495A3,
  0x0EDB8832, 0x79DCB8A4, 0xE0D5E91E, 0x97D2D988, 0x09B64C2B, 0x7EB17CBD, 0xE7B82D07, 0x90BF1D91,
  0x1DB71064, 0x6AB020F2, 0xF3B97148, 0x84BE41DE, 0x1ADAD47D, 0x6DDDE4EB, 0xF4D4B551, 0x83D385C7,
  0x136C9856, 0x646BA8C0, 0xFD62F97A, 0x8A65C9EC, 0x14015C4F, 0x63066CD9, 0xFA0F3D63, 0x8D080DF5,
  0x3B6E20C8, 0x4C69105E, 0xD56041E4, 0xA2677172, 0x3C03E4D1, 0x4B04D447, 0xD20D85FD, 0xA50AB56B,
  0x35B5A8FA, 0x42B2986C, 0xDBBBC9D6, 0xACBCF940, 0x32D86CE3, 0x45DF5C75, 0xDCD60DCF, 0xABD13D59,
  0x26D930AC, 0x51DE003A, 0xC8D75180, 0xBFD06116, 0x21B4F4B5, 0x56B3C423, 0xCFBA9599, 0xB8BDA50F,
  0x2802B89E, 0x5F058808, 0xC60CD9B2, 0xB10BE924, 0x2F6F7C87, 0x58684C11, 0xC1611DAB, 0xB6662D3D,
  0x76DC4190, 0x01DB7106, 0x98D220BC, 0xEFD5102A, 0x71B18589, 0x06B6B51F, 0x9FBFE4A5, 0xE8B8D433,
  0x7807C9A2, 0x0F00F934, 0x9609A88E, 0xE10E9818, 0x7F6A0DBB, 0x086D3D2D, 0x91646C97, 0xE6635C01,
  0x6B6B51F4, 0x1C6C6162, 0x856530D8, 0xF262004E, 0x6C0695ED, 0x1B01A57B, 0x8208F4C1, 0xF50FC457,
  0x65B0D9C6, 0x12B7E950, 0x8BBEB8EA, 0xFCB9887C, 0x62DD1DDF, 0x15DA2D49, 0x8CD37CF3, 0xFBD44C65,
  0x4DB26158, 0x3AB551CE, 0xA3BC0074, 0xD4BB30E2, 0x4ADFA541, 0x3DD895D7, 0xA4D1C46D, 0xD3D6F4FB,
  0x4369E96A, 0x346ED9FC, 0xAD678846, 0xDA60B8D0, 0x44042D73, 0x33031DE5, 0xAA0A4C5F, 0xDD0D7CC9,
  0x5005713C, 0x270241AA, 0xBE0B1010, 0xC90C2086, 0x5768B525, 0x206F85B3, 0xB966D409, 0xCE61E49F,
  0x5EDEF90E, 0x29D9C998, 0xB0D09822, 0xC7D7A8B4, 0x59B33D17, 0x2EB40D81, 0xB7BD5C3B, 0xC0BA6CAD,
  0xEDB88320, 0x9ABFB3B6, 0x03B6E20C, 0x74B1D29A, 0xEAD54739, 0x9DD277AF, 0x04DB2615, 0x73DC1683,
  0xE3630B12, 0x94643B84, 0x0D6D6A3E, 0x7A6A5AA8, 0xE40ECF0B, 0x9309FF9D, 0x0A00AE27, 0x7D079EB1,
  0xF00F9344, 0x8708A3D2, 0x1E01F268, 0x6906C2FE, 0xF762575D, 0x806567CB, 0x196C3671, 0x6E6B06E7,
  0xFED41B76, 0x89D32BE0, 0x10DA7A5A, 0x67DD4ACC, 0xF9B9DF6F, 0x8EBEEFF9, 0x17B7BE43, 0x60B08ED5,
  0xD6D6A3E8, 0xA1D1937E, 0x38D8C2C4, 0x4FDFF252, 0xD1BB67F1, 0xA6BC5767, 0x3FB506DD, 0x48B2364B,
  0xD80D2BDA, 0xAF0A1B4C, 0x36034AF6, 0x41047A60, 0xDF60EFC3, 0xA867DF55, 0x316E8EEF, 0x4669BE79,
  0xCB61B38C, 0xBC66831A, 0x256FD2A0, 0x5268E236, 0xCC0C7795, 0xBB0B4703, 0x220216B9, 0x5505262F,
  0xC5BA3BBE, 0xB2BD0B28, 0x2BB45A92, 0x5CB36A04, 0xC2D7FFA7, 0xB5D0CF31, 0x2CD99E8B, 0x5BDEAE1D,
  0x9B64C2B0, 0xEC63F226, 0x756AA39C, 0x026D930A, 0x9C0906A9, 0xEB0E363F, 0x72076785, 0x05005713,
  0x95BF4A82, 0xE2B87A14, 0x7BB12BAE, 0x0CB61B38, 0x92D28E9B, 0xE5D5BE0D, 0x7CDCEFB7, 0x0BDBDF21,
  0x86D3D2D4, 0xF1D4E242, 0x68DDB3F8, 0x1FDA836E, 0x81BE16CD, 0xF6B9265B, 0x6FB077E1, 0x18B74777,
  0x88085AE6, 0xFF0F6A70, 0x66063BCA, 0x11010B5C, 0x8F659EFF, 0xF862AE69, 0x616BFFD3, 0x166CCF45,
  0xA00AE278, 0xD70DD2EE, 0x4E048354, 0x3903B3C2, 0xA7672661, 0xD06016F7, 0x4969474D, 0x3E6E77DB,
  0xAED16A4A, 0xD9D65ADC, 0x40DF0B66, 0x37D83BF0, 0xA9BCAE53, 0xDEBB9EC5, 0x47B2CF7F, 0x30B5FFE9,
  0xBDBDF21C, 0xCABAC28A, 0x53B39330, 0x24B4A3A6, 0xBAD03605, 0xCDD70693, 0x54DE5729, 0x23D967BF,
  0xB3667A2E, 0xC4614AB8, 0x5D681B02, 0x2A6F2B94, 0xB40BBE37, 0xC30C8EA1, 0x5A05DF1B, 0x2D02EF8D]

/-- Mirrors `power_of_two`. -/
def power_of_two (w : Nat) : Nat := 2 ^ w

/-- Mirrors `of_two_complement`: the value modulo `2 ^ w`, with a negative value brought
into range by repeated addition. -/
def of_two_complement (n : Int) (w : Nat) : Nat := (n % (power_of_two w : Int)).toNat

/-- Mirrors `slice_bitstring n m l`: the bits `m` down to `l` of `n`; a negative lower
bound raises upstream. -/
def slice_bitstring (n : Nat) (m l : Int) : Option Nat := do
  if l < 0 then none
  let slice_width := (m + 1 - l).toNat
  pure ((n >>> l.toNat) &&& (power_of_two slice_width - 1))

/-- Mirrors `bitwise_neg n w`: complement the low `w` bits. -/
def bitwise_neg (n : Nat) : Nat → Option Nat
  | 0 => pure n
  | w + 1 => do
    let w' := power_of_two w
    let g ← slice_bitstring n w w
    bitwise_neg (if g == 0 then n + w' else n - w') w

/-- Mirrors `partition_bytes`: the bytes of a value of the given width, most significant
first; the width counts down in steps of eight. -/
partial def partition_bytes (width : Int) (value : Nat) : Option (List Nat) :=
  if width == 0 then pure []
  else do
    let hi := width - 1
    let lo := width - 8
    let byte_value ← slice_bitstring value hi lo
    let bytes_rest ← slice_bitstring value (lo - 1) 0
    pure (byte_value :: (← partition_bytes lo bytes_rest))

/-- Mirrors `pad_right_to_16`. -/
def pad_right_to_16 (p : Nat × Nat) : Nat × Nat :=
  let remainder := p.1 % 16
  if remainder == 0 then p else (p.1 + (16 - remainder), p.2)

/-- Mirrors `compute_hash_crc16`. -/
def compute_hash_crc16 (width : Nat) (value : Nat) : Option Nat := do
  let bytes ← partition_bytes width value
  pure (bytes.foldl (fun hash byte =>
    (hash >>> 8) ^^^ crc16_table[(hash ^^^ byte) &&& 255]!) 0)

/-- Mirrors `compute_hash_crc32`. -/
def compute_hash_crc32 (width : Nat) (value : Nat) : Option Nat := do
  let mask32 := 0xFFFFFFFF
  let bytes ← partition_bytes width value
  pure ((bytes.foldl (fun hash byte =>
    (hash >>> 8) ^^^ crc32_table[(hash ^^^ byte) &&& 255]!) mask32) ^^^ mask32)

/-- Mirrors `add_one_complement`: sixteen-bit ones'-complement addition. -/
def add_one_complement (v w : Nat) : Nat :=
  let tmp := v + w
  let thres := power_of_two 16
  if tmp ≥ thres then tmp % thres + 1 else tmp % thres

/-- The sixteen-bit words of a value, most significant first, folded into a checksum; the
word is complemented first when `sub` is set. -/
partial def csum16_words (sub : Bool) (value_hash : Nat) (width : Int) (value : Nat) :
    Option Nat :=
  if width == 0 then pure value_hash
  else do
    let msb := width - 1
    let lsb := width - 16
    let word ← slice_bitstring value msb lsb
    let word ← if sub then bitwise_neg word 16 else pure word
    let value_hash := add_one_complement value_hash word
    let value ← slice_bitstring value (msb - 1) 0
    csum16_words sub value_hash lsb value

/-- Mirrors `compute_hash_csum16`. -/
def compute_hash_csum16 (value_init : Nat) (width : Nat) (value : Nat) : Option Nat := do
  bitwise_neg (← csum16_words false value_init width value) 16

/-- Mirrors `compute_hash_csum16_sub`. -/
def compute_hash_csum16_sub (value_init : Nat) (width : Nat) (value : Nat) : Option Nat := do
  bitwise_neg (← csum16_words true value_init width value) 16

/-- Mirrors `adjust`: into `[base, base + max - 1]`; a non-positive range raises upstream's
`Bigint` modulus. -/
def adjust (base rmax : Int) (value : Nat) : Option Int :=
  if rmax == 0 then pure base
  else if rmax - base ≤ 0 then none
  else pure ((value : Int) % (rmax - base) + base)

/-- Mirrors `compute_hash` on a packed width and value. -/
def compute_hash (algo : ByteText) (value_init : Nat := 0) (p : Nat × Nat) : Option Nat :=
  let (width, value) := p
  if algo == ByteText.ofString "csum16" then compute_hash_csum16 value_init width value
  else if algo == ByteText.ofString "csum16_sub" then compute_hash_csum16_sub value_init width value
  else if algo == ByteText.ofString "crc16" then compute_hash_crc16 width value
  else if algo == ByteText.ofString "crc32" then compute_hash_crc32 width value
  else if algo == ByteText.ofString "identity" then pure value
  else none

/-- Mirrors `package`: concatenate the P4 numbers' two's-complement bit strings, then pad
to a multiple of sixteen bits. -/
def package (values : List value) : Option (Nat × Nat) := do
  let numbers ← values.mapM Unpack.unpack_p4_precision_numberValue
  let packed := numbers.foldl (fun (width_pack, value_pack) (width, value) =>
    let width := width.toNat
    (width_pack + width, (value_pack <<< width) + of_two_complement value width)) (0, 0)
  pure (pad_right_to_16 packed)

/-- Mirrors `compute_checksum`. -/
def compute_checksum (algo : ByteText) (values : List value) (value_init : Nat := 0) :
    Option Nat := do
  compute_hash algo value_init (← package values)

end P4SpecTec.BackendSim.Hash
